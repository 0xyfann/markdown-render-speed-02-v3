// parse.js — an original Markdown parser.
//
// parse(markdown) renders the same HTML as marked 18.1.3 with its default
// options (gfm: true, breaks: false, pedantic: false, async: false).
//
// The implementation follows the CommonMark 0.31.2 block/inline model with
// the GFM extensions marked enables (tables, task list items, strikethrough,
// extended autolinks), and marked's own HTML conventions where they differ
// from the spec's reference renderer. It is dependency-free, deterministic,
// and keeps no state between calls: every call re-parses from scratch.
//
// Layout:
//   1. small text helpers (escaping, entities, URL tidying)
//   2. block structure parser (container stack over lines)
//   3. inline parser (scanner + delimiter stack)
//   4. HTML rendering of the block tree
//   5. the exported parse()

'use strict';

// ---------------------------------------------------------------------------
// 1. Text helpers
// ---------------------------------------------------------------------------

const ESCAPES = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

// Escape text the way marked escapes running text: `<`, `>`, `"` and `'`
// always become entities; `&` becomes `&amp;` unless it already introduces
// something that looks like a named character reference (`&copy;`), which
// marked leaves untouched.
function escapeText(s) {
  if (!/[&<>"']/.test(s)) return s;
  return s.replace(/&(?![A-Za-z][A-Za-z0-9]*;)|[<>"']/g, (c) => ESCAPES[c]);
}

// Escape a value placed inside a double-quoted attribute. Same rule as
// escapeText: marked preserves entity-looking ampersands in attributes too.
function escapeAttr(s) {
  if (!/[&<>"']/.test(s)) return s;
  return s.replace(/&(?![A-Za-z][A-Za-z0-9]*;)|[<>"']/g, (c) => ESCAPES[c]);
}

// Escape code block / code span content: here every `&` is escaped, because
// code is literal text and no entity recognition happens inside it.
function escapeCode(s) {
  if (!/[&<>"']/.test(s)) return s;
  return s.replace(/[&<>"']/g, (c) => ESCAPES[c]);
}

const PUNCT_ASCII = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~";
function isPunct(ch) {
  return ch !== undefined && PUNCT_ASCII.indexOf(ch) !== -1;
}
const PUNCT_U_RE = /^[\p{P}\p{S}]$/u;
const ALNUM_U_RE = /^[\p{L}\p{N}]$/u;
function isPunctU(ch) {
  return ch !== undefined && (PUNCT_ASCII.indexOf(ch) !== -1 || (ch.length === 1 && PUNCT_U_RE.test(ch)));
}
function isAlnumU(ch) {
  return ch !== undefined && ch.length === 1 && ALNUM_U_RE.test(ch);
}

function isSpace(ch) {
  return ch !== undefined && /\s/.test(ch);
}

// Decode a numeric character reference body (the part between &# and ;).
// Returns the decoded string, or null when marked would leave the reference
// as literal text: the value must fit in the Unicode range; zero and
// surrogates follow the usual replacement rules.
function decodeNumericRef(body) {
  let cp;
  if (body.charCodeAt(0) === 120 || body.charCodeAt(0) === 88) { // x or X
    cp = parseInt(body.slice(1), 16);
  } else {
    cp = parseInt(body, 10);
  }
  if (!Number.isFinite(cp) || cp > 0x10ffff) return null;
  if (cp === 0 || (cp >= 0xd800 && cp <= 0xdfff)) return '�';
  return String.fromCodePoint(cp);
}

// Percent-encode a link destination the way marked does before putting it in
// an href/src attribute: run encodeURI, but leave existing %XX escapes alone
// (encodeURI would double-encode the % of an escape that is already there
// only when it is not a valid escape introducer in its table — marked's
// behaviour is encodeURI with %25 restored when it came from an original %).
const HREF_SAFE = new Set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789;/?:@&=+$,-_.!~*'()#%");
function encodeHref(href) {
  let out = '';
  for (const ch of href) {
    if (HREF_SAFE.has(ch)) { out += ch; continue; }
    let cp = ch.codePointAt(0);
    if (cp >= 0xd800 && cp <= 0xdfff) cp = 0xfffd;
    if (cp < 0x80) {
      out += '%' + cp.toString(16).toUpperCase().padStart(2, '0');
    } else {
      for (const byte of new TextEncoder().encode(String.fromCodePoint(cp))) {
        out += '%' + byte.toString(16).toUpperCase().padStart(2, '0');
      }
    }
  }
  return out;
}

// Normalise a reference label for lookup: collapse internal whitespace runs
// to single spaces, trim, and fold case (Unicode-aware, like the spec).
function normaliseLabel(s) {
  return s.replace(/\s+/g, ' ').trim().toLowerCase().replace(/ß/g, 'ss');
}

// ---------------------------------------------------------------------------
// 2. Block structure
// ---------------------------------------------------------------------------
//
// Blocks are plain objects: { t, children, ... } with t one of:
//   doc, quote, list, item, para, heading, code, html, hr, table
// Paragraph and heading nodes keep their raw inline source in `text` until
// rendering; code keeps literal text in `text`; html keeps raw lines.

function makeBlock(t) {
  return { t, children: [], lastLineBlank: false, open: true };
}

// Advance past up to `n` columns of indentation starting at state.pos in
// `line`, expanding tabs partially when a tab straddles the boundary.
// state: { pos, col, partial } — partial is the number of columns of the tab
// at line[pos] already consumed (0 when line[pos] is not a tab).
function advanceIndent(line, st, n) {
  let remaining = n;
  while (remaining > 0 && st.pos < line.length) {
    const ch = line[st.pos];
    if (ch === ' ') {
      st.pos++; st.col++; remaining--;
    } else if (ch === '\t') {
      const tabWidth = 4 - (st.col % 4);
      const avail = tabWidth - st.partial;
      if (avail > remaining) {
        st.partial += remaining;
        st.col += remaining;
        remaining = 0;
      } else {
        st.pos++; st.col += avail; st.partial = 0;
        remaining -= avail;
      }
    } else {
      break;
    }
  }
}

// Count columns of a whitespace-only remainder etc. Helpers on raw strings:

// Does `line` from position `pos` contain only spaces/tabs?
function isBlankFrom(line, pos) {
  for (let i = pos; i < line.length; i++) {
    const c = line[i];
    if (c !== ' ' && c !== '\t') return false;
  }
  return true;
}

// Match up to three leading spaces (the block-start allowance). Returns the
// position after them, or -1 when the line is indented by 4+ columns (an
// indented code context) — computed with tab awareness from column `col0`.
function skipUpTo3(line, pos, col) {
  let p = pos, c = col, partial = 0;
  let spaces = 0;
  while (p < line.length) {
    const ch = line[p];
    if (ch === ' ') { p++; c++; spaces++; if (spaces === 4) return -1; }
    else if (ch === '\t') {
      const w = 4 - (c % 4);
      if (spaces + w >= 4) return -1;
      spaces += w; c += w; p++;
    } else break;
  }
  return p;
}

// A fence opening: ``` or ~~~ (3+), up to 3 spaces indent. Returns
// { ch, len, info, end } or null. For backtick fences the info string may
// not contain backticks.
function matchFence(line, pos) {
  const ch = line[pos];
  if (ch !== '`' && ch !== '~') return null;
  let p = pos;
  while (p < line.length && line[p] === ch) p++;
  const len = p - pos;
  if (len < 3) return null;
  const info = line.slice(p);
  if (ch === '`' && info.indexOf('`') !== -1) return null;
  return { ch, len, info: info.trim() };
}

// An ATX heading: 1-6 # followed by space/tab or end of line.
function matchAtx(line, pos) {
  let p = pos;
  while (p < line.length && line[p] === '#') p++;
  const level = p - pos;
  if (level === 0 || level > 6) return null;
  if (p < line.length && line[p] !== ' ' && line[p] !== '\t') return null;
  let text = line.slice(p).replace(/[ \t]+$/, '');
  // Optional closing sequence of #s, preceded by whitespace (the whitespace
  // that separates it from the opening sequence counts when it is all that
  // precedes it).
  const close = /[ \t](#+)$/.exec(text);
  if (close) text = text.slice(0, close.index);
  text = text.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  return { level, text };
}

// A thematic break: 3+ of -, _ or * (same char), spaces/tabs interspersed.
function matchHr(line, pos) {
  let p = pos;
  const ch = line[p];
  if (ch !== '-' && ch !== '_' && ch !== '*') return null;
  let count = 0;
  while (p < line.length) {
    const c = line[p];
    if (c === ch) count++;
    else if (c !== ' ' && c !== '\t') return null;
    p++;
  }
  return count >= 3;
}

// A setext underline: === or --- runs with optional trailing spaces.
function matchSetext(line, pos) {
  const ch = line[pos];
  if (ch !== '=' && ch !== '-') return null;
  let p = pos;
  while (p < line.length && line[p] === ch) p++;
  if (!isBlankFrom(line, p)) return null;
  return ch === '=' ? 1 : 2;
}

// Take the part of `line` that starts at column `target`, where columns are
// counted from the line's start with tabs jumping to multiples of 4. Marker
// characters in the consumed region count one column each. A tab cut by the
// boundary contributes its remaining columns as spaces, and the rest of the
// leading whitespace run is expanded to spaces too, so the result keeps the
// original column layout for its first content character.
function sliceAtColumn(line, target) {
  let col = 0, pos = 0;
  while (pos < line.length && col < target) {
    const c = line[pos];
    const w = c === '\t' ? 4 - (col % 4) : 1;
    if (col + w > target) {
      let out = ' '.repeat(col + w - target);
      pos++;
      col += w;
      while (pos < line.length && (line[pos] === ' ' || line[pos] === '\t')) {
        const w2 = line[pos] === '\t' ? 4 - (col % 4) : 1;
        out += ' '.repeat(w2);
        col += w2;
        pos++;
      }
      return out + line.slice(pos);
    }
    col += w;
    pos++;
  }
  return line.slice(pos);
}

// A list marker at pos: bullet (-, +, *) or ordered (1-9 digits then . or )).
// Returns { bullet, ch, num, digits, delim, contentStart, markerEnd } where
// contentStart is the column the item's content begins at, or null.
function matchListMarker(line, pos, col) {
  const ch = line[pos];
  let bullet = false, num = 0, digits = 0, delim = '';
  let p = pos;
  if (ch === '-' || ch === '+' || ch === '*') {
    bullet = true; delim = ch; p++;
  } else if (ch >= '0' && ch <= '9') {
    while (p < line.length && line[p] >= '0' && line[p] <= '9' && digits < 10) { p++; digits++; }
    if (digits === 0 || digits > 9) return null;
    if (line[p] !== '.' && line[p] !== ')') return null;
    num = parseInt(line.slice(pos, p), 10);
    delim = line[p]; p++;
  } else {
    return null;
  }
  // After the marker: 1-4 spaces/tabs, or end of line (empty item).
  let spaces = 0, q = p, c = col + (p - pos);
  let partialTab = 0;
  while (q < line.length) {
    const cc = line[q];
    if (cc === ' ') { spaces++; q++; c++; }
    else if (cc === '\t') {
      const w = 4 - (c % 4);
      spaces += w; c += w; q++;
      if (spaces > 4) { partialTab = w - (spaces - 4); }
    } else break;
    if (spaces > 4) break;
  }
  const blankRest = q >= line.length;
  let contentSpaces;
  if (blankRest) contentSpaces = 1;
  else if (spaces >= 1 && spaces <= 4) contentSpaces = spaces;
  else contentSpaces = 1; // 0 or 5+: content starts one column after marker
  const markerWidth = (p - pos);
  return {
    bullet, ch: bullet ? ch : '', num, digits, delim,
    markerEndPos: blankRest ? q : (contentSpaces === spaces ? q : p),
    contentIndent: markerWidth + contentSpaces,
    empty: blankRest,
    afterPos: p,
    spacesAfter: spaces,
    qPos: q,
  };
}

// HTML block start conditions (CommonMark's seven types). Returns the type
// number 1-7 or 0. `pos` is at the first non-space character (<=3 indent).
const HTML_BLOCK_TAGS_6 = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param section source summary table tbody td tfoot th thead title tr track ul').split(' '));

function matchHtmlBlockStart(line, pos, inParagraph) {
  if (line[pos] !== '<') return 0;
  const rest = line.slice(pos);
  // type 1: script, pre, style, textarea
  if (/^<(script|pre|style|textarea)(?=[\s>]|$)/i.test(rest)) return 1;
  if (rest.startsWith('<!--')) return 2;
  if (rest.startsWith('<?')) return 3;
  if (/^<![A-Z]/.test(rest)) return 4;
  if (rest.startsWith('<![CDATA[')) return 5;
  const m = /^<\/?([A-Za-z][A-Za-z0-9-]*)(?=[\s/>]|$)/.exec(rest);
  if (m && HTML_BLOCK_TAGS_6.has(m[1].toLowerCase())) return 6;
  if (!inParagraph) {
    // type 7: a complete open or closing tag, alone on its line
    const t = matchTagAt(rest, 0, true);
    if (t > 0 && rest.slice(t).trim() === '') return 7;
  }
  return 0;
}

// How an HTML block of the given type ends, tested against a line: types 1-5
// end when the line contains the closing marker (block includes that line);
// types 6-7 end at a blank line (block excludes it).
function htmlBlockEndOnLine(type, line) {
  switch (type) {
    case 1: return /<\/(script|pre|style|textarea)>/i.test(line);
    case 2: return line.includes('-->');
    case 3: return line.includes('?>');
    case 4: return line.includes('>');
    case 5: return line.includes(']]>');
    default: return false;
  }
}

// Scan a CommonMark tag starting at s[i] === '<'. Returns the index just
// past the closing '>', or -1 when the text at i is not a tag. When
// `complete` is set the tag must be a full open or close tag (HTML block
// type 7); attributes follow the spec grammar.
function matchTagAt(s, i, complete) {
  let p = i + 1;
  if (s[p] === '/') p++;
  if (p >= s.length || !/[A-Za-z]/.test(s[p])) return -1;
  p++;
  while (p < s.length && /[A-Za-z0-9-]/.test(s[p])) p++;
  if (s[i + 1] === '/') {
    // closing tag: optional whitespace then '>'
    while (p < s.length && (s[p] === ' ' || s[p] === '\t' || s[p] === '\n')) p++;
    return s[p] === '>' ? p + 1 : -1;
  }
  // open tag: attributes
  for (;;) {
    let ws = 0;
    while (p < s.length && (s[p] === ' ' || s[p] === '\t' || s[p] === '\n' || s[p] === '\r')) { p++; ws++; }
    if (p >= s.length) return -1;
    if (s[p] === '>') return p + 1;
    if (s[p] === '/' && s[p + 1] === '>') return p + 2;
    if (ws === 0) return -1;
    // attribute name
    if (!/[A-Za-z_:]/.test(s[p])) return -1;
    p++;
    while (p < s.length && /[A-Za-z0-9_.:-]/.test(s[p])) p++;
    // optional value
    let q = p;
    while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q++;
    if (s[q] === '=') {
      q++;
      while (q < s.length && (s[q] === ' ' || s[q] === '\t' || s[q] === '\n')) q++;
      const v = s[q];
      if (v === '"' || v === "'") {
        const end = s.indexOf(v, q + 1);
        if (end === -1) return -1;
        p = end + 1;
      } else {
        if (q >= s.length || /[\s"'=<>`]/.test(v)) return -1;
        while (q < s.length && !/[\s"'=<>`]/.test(s[q])) q++;
        p = q;
      }
    }
  }
}

// --- link reference definitions -------------------------------------------

// Try to parse a link reference definition starting at text[pos] (which is
// at a '['). On success returns { label, href, title, end } with end just
// past the definition's final newline (or at end of text); else null.
// Backslash escapes in destination and title are resolved; entity-looking
// text is left as written (marked does not decode entities here).
function parseLinkDef(text, pos, links) {
  let p = pos;
  if (text[p] !== '[') return null;
  // label: up to the matching unescaped ']'
  let q = p + 1, labelEnd = -1;
  while (q < text.length && q - p <= 1000) {
    const c = text[q];
    if (c === '\\') { q += 2; continue; }
    if (c === '[') return null;
    if (c === ']') { labelEnd = q; break; }
    q++;
  }
  if (labelEnd === -1) return null;
  const label = text.slice(p + 1, labelEnd);
  if (label.trim() === '') return null;
  q = labelEnd + 1;
  if (text[q] !== ':') return null;
  q++;
  // optional whitespace, including at most one line ending
  q = skipDefWs(text, q);
  const dest = parseDestAt(text, q);
  if (!dest) return null;
  q = dest.end;
  let title = null;
  // optional title, possibly on the next line; it must be separated from
  // the destination by whitespace and followed by the end of the line
  const saveQ = q;
  let r = q;
  while (r < text.length && (text[r] === ' ' || text[r] === '\t')) r++;
  if (text[r] === '\n') { r++; while (r < text.length && (text[r] === ' ' || text[r] === '\t')) r++; }
  const t = r > saveQ ? parseTitleAt(text, r) : null;
  if (t) {
    let e = t.end;
    while (e < text.length && (text[e] === ' ' || text[e] === '\t')) e++;
    if (e >= text.length || text[e] === '\n') {
      title = t.title;
      q = e;
    }
  }
  if (title === null) {
    // no title: the destination must end the line
    let e = saveQ;
    while (e < text.length && (text[e] === ' ' || text[e] === '\t')) e++;
    if (e < text.length && text[e] !== '\n') return null;
    q = e;
  }
  if (text[q] === '\n') q++;
  const key = normaliseLabel(label);
  if (key && !links.has(key)) {
    links.set(key, { href: unescapeStr(dest.href), title: title === null ? null : unescapeStr(title) });
  }
  return { end: q };
}

function skipDefWs(text, q) {
  let nl = 0;
  while (q < text.length) {
    const c = text[q];
    if (c === ' ' || c === '\t') q++;
    else if (c === '\n' && nl === 0) { nl++; q++; }
    else break;
  }
  return q;
}

// A link destination at text[q]: <...> or a bare run with balanced parens.
// Returns { href, end } (href still backslash-escaped) or null.
function parseDestAt(text, q) {
  if (text[q] === '<') {
    let p = q + 1;
    while (p < text.length) {
      const c = text[p];
      if (c === '\\') { p += 2; continue; }
      if (c === '>') return { href: text.slice(q + 1, p), end: p + 1 };
      if (c === '<' || c === '\n') return null;
      p++;
    }
    return null;
  }
  let p = q, depth = 0;
  while (p < text.length) {
    const c = text[p];
    if (c === '\\') { p += 2; continue; }
    if (c === '(') { depth++; if (depth > 32) return null; }
    else if (c === ')') { if (depth === 0) break; depth--; }
    else if (c === ' ' || c === '\t' || c === '\n' || c < ' ') break;
    p++;
  }
  if (p === q || depth !== 0) return null;
  return { href: text.slice(q, p), end: p };
}

// A link title at text[q]: "..." or '...' or (...). Returns { title, end }.
function parseTitleAt(text, q) {
  const open = text[q];
  const close = open === '"' ? '"' : open === "'" ? "'" : open === '(' ? ')' : null;
  if (close === null) return null;
  let p = q + 1;
  while (p < text.length) {
    const c = text[p];
    if (c === '\\') { p += 2; continue; }
    if (c === close) return { title: text.slice(q + 1, p), end: p + 1 };
    if (open === '(' && c === '(') return null;
    if (c === '\n') {
      let j = p + 1;
      while (text[j] === ' ' || text[j] === '\t') j++;
      if (text[j] === '\n') return null; // blank line inside a title
    }
    p++;
  }
  return null;
}

// Resolve backslash escapes of ASCII punctuation.
function unescapeStr(s) {
  if (s.indexOf('\\') === -1) return s;
  return s.replace(/\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/g, '$1');
}

// --- GFM table helpers ------------------------------------------------------

// Split a table row into cell strings. `\|` is an escaped pipe (kept for the
// inline pass as `\|`? no: it becomes a literal | in the cell text), pipes
// inside code spans do not split. Leading/trailing pipes are optional.
function splitTableRow(line) {
  const s = line.trim();
  const cells = [];
  let cur = '', i = 0;
  if (s.startsWith('|')) i = 1;
  let endedWithPipe = false;
  for (; i < s.length; i++) {
    const c = s[i];
    if (c === '\\' && s[i + 1] === '|') { cur += '|'; i++; endedWithPipe = false; continue; }
    if (c === '\\' && i + 1 < s.length) { cur += c + s[i + 1]; i++; endedWithPipe = false; continue; }
    if (c === '|') { cells.push(cur); cur = ''; endedWithPipe = true; continue; }
    cur += c; endedWithPipe = false;
  }
  cells.push(cur);
  if (endedWithPipe) cells.pop();
  return cells.map((c) => c.trim());
}

// Is this line a table delimiter row? Returns the alignments array
// ('left' | 'right' | 'center' | null per column) or null.
function matchTableDelim(line) {
  const s = line.trim();
  if (s.indexOf('-') === -1) return null;
  const cells = splitTableRow(line);
  if (cells.length === 0) return null;
  const aligns = [];
  for (const cell of cells) {
    if (!/^:?-+:?$/.test(cell)) return null;
    const left = cell.startsWith(':'), right = cell.endsWith(':');
    aligns.push(left && right ? 'center' : left ? 'left' : right ? 'right' : null);
  }
  return aligns;
}

// --- line utilities ---------------------------------------------------------

// Leading whitespace of a line, in columns (tabs jump to the next multiple
// of 4) and the index of the first non-whitespace character.
function leadingWs(line) {
  let cols = 0, pos = 0;
  while (pos < line.length) {
    const c = line[pos];
    if (c === ' ') { cols++; pos++; }
    else if (c === '\t') { cols += 4 - (cols % 4); pos++; }
    else break;
  }
  return { cols, pos };
}

function isBlankLine(line) {
  return leadingWs(line).pos === line.length;
}

// Remove n columns of leading whitespace. When a tab straddles the cut, the
// unconsumed part of the tab comes back as spaces.
function removeCols(line, n) {
  let cols = 0, pos = 0;
  while (pos < line.length && cols < n) {
    const c = line[pos];
    if (c === ' ') { cols++; pos++; }
    else if (c === '\t') {
      const w = 4 - (cols % 4);
      if (cols + w <= n) { cols += w; pos++; }
      else return ' '.repeat(cols + w - n) + line.slice(pos + 1);
    } else break;
  }
  return line.slice(pos);
}

// A usable list marker at the position given by leadingWs, or null. A marker
// must be followed by whitespace or by the end of the line.
function listMarkerAt(line) {
  const { cols, pos } = leadingWs(line);
  if (cols > 3 || pos >= line.length) return null;
  const m = matchListMarker(line, pos, cols);
  if (!m) return null;
  if (!m.empty && m.spacesAfter === 0) return null;
  m.startCol = cols;
  m.contentCol = cols + m.contentIndent;
  return m;
}

function sameListType(a, b) {
  if (a.bullet !== b.bullet) return false;
  return a.bullet ? a.ch === b.ch : a.delim === b.delim;
}

// Does this line start a block that interrupts a paragraph? Used for lazy
// continuation lines in quotes and list items.
function startsInterruptingBlock(line, state, allowQuote) {
  const { cols, pos } = leadingWs(line);
  if (cols > 3 || pos >= line.length) return false;
  const c = line[pos];
  if (c === '#') return matchAtx(line, pos) !== null;
  if (c === '`' || c === '~') return matchFence(line, pos) !== null;
  if (c === '-' || c === '_' || c === '*') {
    if (matchHr(line, pos)) return true;
  }
  if (c === '>') return allowQuote;
  if (c === '<') return matchHtmlBlockStart(line, pos, true) !== 0;
  const m = listMarkerAt(line);
  if (m) {
    if (m.empty) return false;
    // an ordered list interrupts a paragraph only when it starts at 1 —
    // except inside list items, where marked allows any start number
    if (!m.bullet && m.num !== 1 && !state.inItem) return false;
    return true;
  }
  return false;
}

// A lazy setext underline (one gathered without its container's marker) is
// paragraph text, never a heading. Lines gathered lazily that look like
// setext underlines are prefixed with this sentinel so the inner block pass
// keeps them as text; it is stripped again there.
const LAZY_SETEXT = '\u0001';

// Could a lazy line continue the block quote content gathered so far? Only
// when its last line is paragraph-like: not blank, not indented code, and
// not a leaf block start of its own.
function fenceStillOpen(lines) {
  let open = null;
  for (const l of lines) {
    const lw = leadingWs(l);
    if (lw.cols > 3) continue;
    const ch = l[lw.pos];
    if (ch !== '`' && ch !== '~') continue;
    const f = matchFence(l, lw.pos);
    if (!f) continue;
    if (open && f.ch === open.ch && f.len >= open.len && isBlankFrom(l, lw.pos + f.len)) open = null;
    else if (!open) open = f;
  }
  return open !== null;
}

function quoteParaOpen(inner) {
  if (fenceStillOpen(inner)) return false;
  const last = inner[inner.length - 1];
  if (last === undefined || isBlankLine(last)) return false;
  if (last.charCodeAt(0) === 1) return true;
  const { cols, pos } = leadingWs(last);
  if (cols >= 4) return false;
  const c = last[pos];
  if (c === '#') return matchAtx(last, pos) === null;
  if (c === '`' || c === '~') return matchFence(last, pos) === null;
  if ((c === '-' || c === '_' || c === '*') && matchHr(last, pos)) return false;
  return true;
}

// --- the block parser -------------------------------------------------------
//
// lexBlocks turns an array of lines (container prefixes already stripped by
// the caller) into block nodes. Link reference definitions found anywhere
// are registered into state.links and produce no node.

function lexBlocks(lines, state, topLevel) {
  const blocks = [];
  let blankBetween = false;
  let lastEnd = -1; // line index just past the last emitted block
  let i = 0;
  const n = lines.length;
  while (i < n) {
    let line = lines[i];
    if (isBlankLine(line)) { i++; continue; }
    const startLine = i;
    // a blank line after an emitted block, with any further content after
    // it (a block or a link definition), separates two elements
    if (blocks.length && lastEnd !== -1 && !blankBetween) {
      for (let q = lastEnd; q < startLine; q++) {
        if (isBlankLine(lines[q])) { blankBetween = true; break; }
      }
    }
    const pushBlock = (b) => {
      blocks.push(b);
      lastEnd = i;
    };
    if (line.charCodeAt(0) === 1) line = line.slice(1);
    const { cols, pos } = leadingWs(line);
    const c = line[pos];

    // fenced code
    if (cols <= 3 && (c === '`' || c === '~')) {
      const f = matchFence(line, pos);
      if (f) {
        const body = [];
        i++;
        while (i < n) {
          const l = lines[i];
          const lw = leadingWs(l);
          if (lw.cols <= 3 && l[lw.pos] === f.ch) {
            // closing fence: same char, at least as long, nothing after
            let p = lw.pos, cnt = 0;
            while (l[p] === f.ch) { p++; cnt++; }
            if (cnt >= f.len && isBlankFrom(l, p)) { i++; break; }
          }
          body.push(removeCols(l, Math.min(cols, lw.cols)));
          i++;
        }
        if (body.length && body[body.length - 1] === '') body.pop();
        pushBlock({ t: 'code', text: body.length ? body.join('\n') + '\n' : '', info: unescapeStr(f.info), fenced: true });
        continue;
      }
    }

    // ATX heading
    if (cols <= 3 && c === '#') {
      const h = matchAtx(line, pos);
      if (h) {
        pushBlock({ t: 'heading', level: h.level, text: h.text });
        i++;
        continue;
      }
    }

    // thematic break
    if (cols <= 3 && (c === '-' || c === '_' || c === '*') && matchHr(line, pos)) {
      pushBlock({ t: 'hr' });
      i++;
      continue;
    }

    // block quote
    if (cols <= 3 && c === '>') {
      const inner = [];
      let lazyStreak = 0;
      // Marked's quote capture treats a run of indented (>= 4 cols) lazy
      // lines specially: they are dedented by four columns, and the next
      // non-indented line (lazy or marked) is separated from them by a
      // blank line inside the paragraph text. Once a non-indented lazy
      // line has been taken, later indented lines stay verbatim.
      let lazyAllIndented = true;
      let phantom = false;
      while (i < n) {
        const l = lines[i];
        const lw = leadingWs(l);
        if (lw.cols <= 3 && l[lw.pos] === '>') {
          const stripped = stripQuoteMarker(l, lw);
          if (phantom && !isBlankLine(stripped) && inner.length) {
            inner[inner.length - 1] += '\n';
          }
          phantom = false;
          inner.push(stripped);
          lazyStreak = 0;
          lazyAllIndented = true;
          i++;
          continue;
        }
        // lazy continuation: a paragraph line without the marker. A bare
        // bullet marker is not lazy (it starts a list outside the quote),
        // and neither is any other list marker, whatever its number.
        const trimmed = l.trim();
        const bareBullet = trimmed === '-' || trimmed === '+' || trimmed === '*';
        const lm = lw.cols <= 3 ? listMarkerAt(l) : null;
        let lazyLine;
        if (lw.cols >= 4 && lazyAllIndented) {
          lazyLine = sliceAtColumn(l, 4);
        } else {
          lazyLine = l;
        }
        if (inner.length && !isBlankLine(l) && !isBlankLine(inner[inner.length - 1])
            && quoteParaOpen(inner) && !bareBullet && !(lm && !lm.empty)
            && !startsInterruptingBlock(l, state, false)) {
          if (lw.cols >= 4 && lazyAllIndented) {
            phantom = true;
          } else if (lw.cols < 4) {
            if (phantom && inner.length) inner[inner.length - 1] += '\n';
            phantom = false;
            lazyAllIndented = false;
          }
          const lwl = leadingWs(lazyLine);
          if (lwl.cols <= 3 && (matchSetext(lazyLine, lwl.pos)
              || startsInterruptingBlock(lazyLine, state, true)
              || lazyLine[lwl.pos] === '>')) {
            // a lazy setext underline stays paragraph text: after another
            // lazy line marked indents it by four columns; as the first
            // lazy line it is flagged so the inner pass keeps it as text
            inner.push(lazyStreak >= 1 && matchSetext(lazyLine, lwl.pos)
              ? '    ' + lazyLine : LAZY_SETEXT + lazyLine);
          } else {
            inner.push(lazyLine);
          }
          lazyStreak++;
          i++;
          continue;
        }
        break;
      }
      const savedInItem = state.inItem;
      state.inItem = false;
      const quoteChildren = lexBlocks(inner, state, false).blocks;
      state.inItem = savedInItem;
      pushBlock({ t: 'quote', children: quoteChildren });
      continue;
    }

    // list
    if (cols <= 3 && listMarkerAt(line)) {
      const res = lexList(lines, i, state);
      i = res.next;
      pushBlock(res.block);
      continue;
    }

    // HTML block
    if (cols <= 3 && c === '<') {
      const type = matchHtmlBlockStart(line, pos, false);
      if (type !== 0) {
        const body = [line];
        i++;
        if (type >= 6) {
          while (i < n && !isBlankLine(lines[i])) { body.push(lines[i]); i++; }
        } else {
          while (i < n && !htmlBlockEndOnLine(type, body[body.length - 1])) {
            body.push(lines[i]); i++;
          }
        }
        // The block's last line keeps its newline unless a blank line
        // follows the block (or the source ends without one).
        let text = body.join('\n');
        const followedByBlank = i < n && (type >= 6 ? isBlankLine(lines[i]) : lines[i] === '');
        if (!followedByBlank && (i < n || (topLevel && state.endsWithNl))) text += '\n';
        pushBlock({ t: 'html', text });
        continue;
      }
    }

    // indented code
    if (cols >= 4) {
      const body = [];
      const blanks = [];
      while (i < n) {
        const l = lines[i];
        if (isBlankLine(l)) { blanks.push(sliceAtColumn(l, Math.min(4, leadingWs(l).cols))); i++; continue; }
        if (leadingWs(l).cols >= 4) {
          while (blanks.length) body.push(blanks.shift());
          body.push(removeCols(l, 4));
          i++;
          continue;
        }
        break;
      }
      pushBlock({ t: 'code', text: body.length ? body.join('\n') + '\n' : '', info: '', fenced: false });
      continue;
    }

    // link reference definition(s) at a block start
    if (c === '[') {
      const joined = lines.slice(i, Math.min(n, i + 8)).join('\n');
      const def = parseLinkDef(joined, pos, state.links);
      if (def) {
        const consumed = joined.slice(0, def.end);
        const usedLines = consumed.split('\n').length - (consumed.endsWith('\n') ? 1 : 0);
        i += Math.max(1, usedLines);
        continue;
      }
    }

    // table starting on this line
    if (i + 1 < n && line.indexOf('|') !== -1) {
      const aligns = matchTableDelim(lines[i + 1]);
      if (aligns) {
        const header = splitTableRow(line);
        if (header.length === aligns.length) {
          const tbl = { t: 'table', header, aligns, rows: [] };
          i += 2;
          while (i < n && !/^ *$/.test(lines[i]) && !startsInterruptingBlock(lines[i], state, true)) {
            tbl.rows.push(splitTableRow(lines[i]));
            i++;
          }
          pushBlock(tbl);
          continue;
        }
      }
    }

    // paragraph (with setext / table conversion and interruption rules)
    const paraLines = [];
    let heading = 0;
    let tableConv = null;
    while (i < n) {
      const l = lines[i];
      if (isBlankLine(l)) {
        // A whitespace-only final line (with no newline after it in the
        // source) belongs to the paragraph in marked's capture.
        if (l.length > 0 && i === n - 1 && paraLines.length > 0
            && !(topLevel && state.endsWithNl)) {
          paraLines.push({ raw: l, text: l });
          i++;
        }
        break;
      }
      if (l.charCodeAt(0) === 1) {
        paraLines.push({ raw: l, text: l.slice(1) });
        i++;
        continue;
      }
      const lw = leadingWs(l);
      if (paraLines.length > 0 && lw.cols <= 3) {
        const cc = l[lw.pos];
        // setext underline?
        if (cc === '=' || cc === '-') {
          const lvl = matchSetext(l, lw.pos);
          if (lvl) { heading = lvl; i++; break; }
        }
        // table delimiter under a one-line paragraph?
        if (paraLines.length === 1 && l.indexOf('-') !== -1) {
          const aligns = matchTableDelim(l);
          if (aligns) {
            const header = splitTableRow(paraLines[0].raw);
            if (header.length === aligns.length) {
              tableConv = { header, aligns };
              i++;
              break;
            }
          }
        }
        if (startsInterruptingBlock(l, state, true)) break;
      }
      paraLines.push({ raw: l, text: paraRawLine(l) });
      i++;
    }
    if (tableConv) {
      const tbl = { t: 'table', header: tableConv.header, aligns: tableConv.aligns, rows: [] };
      while (i < n && !/^ *$/.test(lines[i]) && !startsInterruptingBlock(lines[i], state, true)) {
        tbl.rows.push(splitTableRow(lines[i]));
        i++;
      }
      pushBlock(tbl);
      continue;
    }
    const joinedText = paraLines.map((p) => p.text).join('\n');
    const text = heading ? joinedText.split('\n').map((l) => l.trim()).join('\n') : joinedText;
    if (heading) {
      pushBlock({ t: 'heading', level: heading, text });
      continue;
    }
    // a paragraph may still begin with link definitions that the block-start
    // check could not see (e.g. after a lazy continuation joined it)
    pushBlock({ t: 'para', text });
  }
  return { blocks, blankBetween };
}

// Remove a block quote marker (and at most one column of whitespace after
// it) from a line, keeping the column layout of what follows: whitespace
// after the marker is expanded to the same number of spaces it occupied.
function stripQuoteMarker(l, lw) {
  let pos = lw.pos + 1; // just past '>'
  let col = lw.cols + 1;
  let prefix = '';
  if (l[pos] === ' ') { pos++; col++; }
  else if (l[pos] === '\t') {
    const w = 4 - (col % 4);
    prefix = ' '.repeat(w - 1);
    pos++; col += w;
  }
  let extra = 0;
  while (pos < l.length && (l[pos] === ' ' || l[pos] === '\t')) {
    const w = l[pos] === '\t' ? 4 - (col % 4) : 1;
    extra += w;
    col += w;
    pos++;
  }
  return prefix + ' '.repeat(extra) + l.slice(pos);
}

// One paragraph source line. Marked keeps a paragraph's lines exactly as
// written (leading whitespace included); trailing whitespace is dealt with
// when the lines are joined (see lexBlocks): only lines followed by another
// line collapse it into a break marker.
function paraRawLine(line) {
  return line;
}

// Dedent one list-item content line by `cols` columns. Marked expands
// tabs in the line's leading whitespace to tab stops before removing the
// item indent, so a tab that starts before the indent boundary leaves
// spaces behind rather than surviving as a tab.
function dedentItemLine(line, cols) {
  let p = 0, col = 0, prefix = '';
  while (p < line.length && (line[p] === ' ' || line[p] === '\t')) {
    if (line[p] === '\t') {
      const w = 4 - (col % 4);
      prefix += ' '.repeat(w);
      col += w;
    } else {
      prefix += ' ';
      col++;
    }
    p++;
  }
  if (p === 0 || !prefix.includes(' ')) return sliceAtColumn(line, cols);
  return sliceAtColumn(prefix + line.slice(p), cols);
}

// Parse a whole list starting at lines[start] (which listMarkerAt accepts).
// Returns { block, next }: the list node and the first unconsumed line.
function lexList(lines, start, state) {
  const first = listMarkerAt(lines[start]);
  const list = {
    t: 'list',
    bullet: first.bullet,
    start: first.bullet ? 1 : first.num,
    items: [],
    tight: true,
  };
  let loose = false;
  let i = start;
  while (i < lines.length) {
    const lw0 = leadingWs(lines[i]);
    if (lw0.cols <= 3 && matchHr(lines[i], lw0.pos)) break;
    const m = listMarkerAt(lines[i]);
    if (!m || !sameListType(m, first)) break;
    const contentCol = m.contentCol;
    const itemLines = [dedentItemLine(lines[i], contentCol)];
    i++;
    let innerBlank = false;
    // deepest nested item content column (in this item's own coordinates)
    // among the content lines gathered so far; blanks followed by lines
    // that belong to such a nested item do not loosen this list
    let deepestNested = -1;
    let fenceOpen = null;
    const noteNested = (itemSpaceLine) => {
      const mm = listMarkerAt(itemSpaceLine);
      if (mm && mm.contentCol > deepestNested) deepestNested = mm.contentCol;
      const lw = leadingWs(itemSpaceLine);
      if (lw.cols <= 3 && (itemSpaceLine[lw.pos] === '`' || itemSpaceLine[lw.pos] === '~')) {
        const f = matchFence(itemSpaceLine, lw.pos);
        if (f) {
          if (fenceOpen && f.ch === fenceOpen.ch && f.len >= fenceOpen.len) fenceOpen = null;
          else if (!fenceOpen) fenceOpen = f;
        }
      }
    };
    noteNested(itemLines[0]);
    let endBlank = false;
    let stop = 'eof';
    while (i < lines.length) {
      const l = lines[i];
      if (isBlankLine(l)) {
        // Look past the blank run to decide who owns it.
        let k = i;
        while (k < lines.length && isBlankLine(lines[k])) k++;
        if (k >= lines.length) { stop = 'eof'; i = k; break; }
        const nl = lines[k];
        // An item with no content yet ends at the blank line, unless the
        // next thing is another item of the list.
        if (itemLines.length === 1 && itemLines[0] === '') {
          const nm = listMarkerAt(nl);
          if (nm && sameListType(nm, first)) { endBlank = true; stop = 'nextItem'; i = k; }
          else stop = 'endOfList';
          break;
        }
        if (leadingWs(nl).cols >= contentCol) {
          for (let b = i; b < k; b++) itemLines.push('');
          const nextIndItemSpace = leadingWs(nl).cols - contentCol;
          if (!fenceOpen && (nextIndItemSpace === 0 || deepestNested === -1
              || nextIndItemSpace < deepestNested)) innerBlank = true;
          i = k;
          continue;
        }
        if (listMarkerAt(nl)) {
          endBlank = true;
          stop = 'nextItem';
          i = k;
          break;
        }
        stop = 'endOfList';
        break;
      }
      const ind = leadingWs(l).cols;
      if (ind >= contentCol) {
        const sliced = dedentItemLine(l, contentCol);
        itemLines.push(sliced);
        noteNested(sliced);
        i++;
        continue;
      }
      if (listMarkerAt(l)) { stop = 'nextItem'; break; }
      if (ind <= 3 && matchHr(l, leadingWs(l).pos)) { stop = 'endOfList'; break; }
      // Lazy paragraph continuation inside the item.
      const lastContent = itemLines[itemLines.length - 1];
      const lazyLine = ind >= 4 ? sliceAtColumn(l, 4) : l;
      if (lastContent !== '' && !startsInterruptingBlock(l, state, true)) {
        const lw2 = leadingWs(lazyLine);
        if (lw2.cols <= 3 && (matchSetext(lazyLine, lw2.pos)
            || startsInterruptingBlock(lazyLine, state, true)
            || lazyLine[lw2.pos] === '>')) {
          itemLines.push(LAZY_SETEXT + lazyLine);
        } else itemLines.push(lazyLine);
        i++;
        continue;
      }
      stop = 'endOfList';
      break;
    }
    while (itemLines.length && itemLines[itemLines.length - 1] === '') itemLines.pop();
    const savedInItem2 = state.inItem;
    state.inItem = true;
    const sub = lexBlocks(itemLines, state, false);
    state.inItem = savedInItem2;
    list.items.push(sub.blocks);
    if (sub.blankBetween) loose = true;
    if (endBlank && stop === 'nextItem') {
      // blanks between this item and the next loosen the list; remember by
      // peeking: only counts when another item really follows
      const nm = i < lines.length ? listMarkerAt(lines[i]) : null;
      if (nm && sameListType(nm, first)) loose = true;
    }
    if (stop === 'endOfList' || stop === 'eof') break;
  }
  list.tight = !loose;
  return { block: list, next: i };
}

// --- inline parsing ---------------------------------------------------------
//
// Inline content becomes a small tree of nodes:
//   text  { s }                 literal characters (escapes already resolved)
//   code  { s }                 code span content
//   html  { s }                 raw inline HTML
//   soft / hard                 line breaks
//   em / strong / del           { children }
//   link  { href, title, children }
//   image { href, title, children }
// Container nodes keep children in a doubly linked list (first/last).

function inode(k, s) {
  return { k, s: s || '', href: null, title: null, first: null, last: null, next: null, prev: null, delimRun: false };
}

function appendNode(parent, node) {
  node.prev = parent.last;
  if (parent.last) parent.last.next = node;
  if (!parent.first) parent.first = node;
  parent.last = node;
}

function detach(node, parent) {
  if (node.prev) node.prev.next = node.next;
  if (node.next) node.next.prev = node.prev;
  if (parent.first === node) parent.first = node.next;
  if (parent.last === node) parent.last = node.prev;
  node.next = null; node.prev = null;
}

// Move all siblings after `after` (up to the end of parent's list) into
// `container` as its children.
function wrapSiblings(parent, after, container) {
  let cur = after.next;
  const moved = [];
  while (cur) { const nx = cur.next; moved.push(cur); cur = nx; }
  for (const m of moved) detach(m, parent);
  for (const m of moved) appendNode(container, m);
  after.next = container;
  container.prev = after;
  container.next = null;
  parent.last = container;
}

const EMAIL_RE = /^[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9_-]*[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9_-]*[A-Za-z0-9])?)+/;

// Follow rule for a matched email: when the next character is - or _ the
// address may not end there, so drop the last domain label (the result
// must keep a dot in the domain). A following _ needs no drop when the
// run of underscores closes an emphasis span opened before the address.
function finishEmail(text, s, end, delims) {
  let t = text, e = end;
  for (;;) {
    const nx = s[e];
    if (nx !== '-' && nx !== '_') return t;
    if (nx === '_') {
      let runEnd = e;
      while (s[runEnd] === '_') runEnd++;
      const after = runEnd < s.length ? s[runEnd] : '';
      const closesSpan = delims !== null
        && !/[\p{L}\p{N}]/u.test(after)
        && delims.some(d => d.ch === '_' && d.canOpen && d.len > 0);
      if (closesSpan) return t;
    }
    const at = t.indexOf('@');
    const dot = t.lastIndexOf('.');
    if (dot <= at) return null;
    const nt = t.slice(0, dot);
    if (!nt.slice(at + 1).includes('.')) return null;
    e -= t.length - nt.length;
    t = nt;
  }
}
const SCHEME_AUTOLINK_RE = /^<([A-Za-z][A-Za-z0-9+.-]{1,31}:[^<>\s]*)>/;
const EMAIL_AUTOLINK_RE = /^<([A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)+)>/;

// Try an extended (GFM) autolink at s[i]: http(s)://, ftp://, www., or an
// email address. Returns { text, href, end } or null.
function matchExtendedAutolink(s, i, inBrackets, delims) {
  if (IN_LINK) return null;
  // word boundary: the previous character must not be part of an address
  const prev = i > 0 ? s[i - 1] : '';
  if (/[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~@-]/.test(prev)) return null;
  const head = s.slice(i, i + 8).toLowerCase();
  let prefix = null, hrefPrefix = '';
  if (head.startsWith('https://')) prefix = s.slice(i, i + 8);
  else if (head.startsWith('http://')) prefix = s.slice(i, i + 7);
  else if (head.startsWith('ftp://')) prefix = s.slice(i, i + 6);
  else if (s.startsWith('www.', i)) { prefix = 'www.'; hrefPrefix = 'http://'; }
  if (prefix) {
    let j = i + prefix.length;
    while (j < s.length && !isSpace(s[j]) && s[j] !== '<'
        && !(inBrackets && s[j] === ']')) j++;
    let text = s.slice(i, j);
    text = trimAutolinkEnd(text, 0, s, i);
    if (text.length <= prefix.length) return null;
    return { text, href: hrefPrefix + text, end: i + text.length };
  }
  if (head.startsWith('mailto:')) {
    const m = EMAIL_RE.exec(s.slice(i + 7, i + 7 + 320));
    if (m) {
      const em = finishEmail(m[0], s, i + 7 + m[0].length, delims);
      if (em) {
        const text = s.slice(i, i + 7) + em;
        return { text, href: text, end: i + text.length };
      }
    }
    return null;
  }
  if (head.startsWith('xmpp:')) {
    const m = EMAIL_RE.exec(s.slice(i + 5, i + 5 + 320));
    if (m) {
      const em = finishEmail(m[0], s, i + 5 + m[0].length, delims);
      if (em) {
        let end = i + 5 + em.length;
        if (s[end] === '/') {
          let j = end + 1;
          while (j < s.length && !isSpace(s[j]) && s[j] !== '<' && s[j] !== '/') j++;
          if (j > end + 1) end = j;
        }
        const text = s.slice(i, end);
        return { text, href: text, end };
      }
    }
    return null;
  }
  const m = EMAIL_RE.exec(s.slice(i, i + 320));
  if (!m) return null;
  const em = finishEmail(m[0], s, i + m[0].length, delims);
  if (!em) return null;
  return { text: em, href: 'mailto:' + em, end: i + em.length };
}

// GFM trailing-punctuation rules for extended autolinks.
function trimAutolinkEnd(text, minLen, whole, start) {
  let t = text;
  for (;;) {
    if (t.length === 0) return t;
    const last = t[t.length - 1];
    if ('?!.,:*_~'.indexOf(last) !== -1) { t = t.slice(0, -1); continue; }
    if (last === ')') {
      let open = 0, closed = 0;
      for (const ch of t) { if (ch === '(') open++; else if (ch === ')') closed++; }
      if (closed > open) { t = t.slice(0, -1); continue; }
    }
    if (last === ';') {
      const m = /&[A-Za-z][A-Za-z0-9]*;$/.exec(t);
      if (m) { t = t.slice(0, t.length - m[0].length); continue; }
      t = t.slice(0, -1);
      continue;
    }
    if (last === '<') { t = t.slice(0, -1); continue; }
    break;
  }
  return t;
}

function parseInline(text, links) {
  const root = inode('root');
  const delims = [];   // { node, ch, len, canOpen, canClose, pos, origLen }
  const matchedClosers = []; // { ch, pos, end } closer runs that have matched
  const allRuns = []; // every delimiter entry, for the rule above
  const brackets = []; // { node, image, delimLen, inactive }
  const s = text;
  const n = s.length;
  let i = 0;

  function addText(str) {
    if (!str) return;
    const last = root.last;
    if (last && last.k === 'text' && !last.delimRun && !last.brk) { last.s += str; return; }
    appendNode(root, inode('text', str));
  }
  function addNode(node) { appendNode(root, node); }

  function processEmphasis(bottom) {
    let closerPos = -1;
    for (let j = bottom; j < delims.length; j++) {
      if (delims[j].canClose) { closerPos = j; break; }
    }
    while (closerPos !== -1) {
      const closer = delims[closerPos];
      let openerPos = -1;
      for (let j = closerPos - 1; j >= bottom; j--) {
        const o = delims[j];
        if (o.ch !== closer.ch || !o.canOpen) continue;
        if (o.canClose || closer.canOpen) {
          const sum = o.len + closer.len;
          if (sum % 3 === 0 && !(o.len % 3 === 0 && closer.len % 3 === 0)) continue;
        }
        // Marked rejects a match whose span contains a mixed-weight
        // emphasis (em inside strong or strong inside em) that was closed
        // by a run immediately followed by an alphanumeric, when this
        // closer also directly follows an alphanumeric — unless the inner
        // opener is itself intraword, or a delimiter run that never
        // matched sits between that inner closer and this one.
        const use = o.len >= 2 && closer.len >= 2 ? 2 : 1;
        const candWeight = o.origLen >= 2 ? 2 : 1;
        if (closer.pos > 0 && /[\p{L}\p{N}]/u.test(s[closer.pos - 1])) {
          let blocked = false;
          for (const mc of matchedClosers) {
            if (mc.ch !== closer.ch || mc.pos <= o.pos || mc.pos >= closer.pos) continue;
            if (mc.use === candWeight) continue; // same weight nests freely
            if (!(mc.end < s.length && /[\p{L}\p{N}]/u.test(s[mc.end]))) continue;
            if (mc.openerPos > 0 && /[\p{L}\p{N}]/u.test(s[mc.openerPos - 1])) continue;
            let cancelled = false;
            for (const r of allRuns) {
              if (r.ch === closer.ch && !r.used && r.pos > mc.pos && r.pos < closer.pos) {
                cancelled = true;
                break;
              }
            }
            if (!cancelled) { blocked = true; break; }
          }
          if (blocked) continue;
        }
        openerPos = j;
        break;
      }
      if (openerPos === -1) {
        if (!closer.canOpen) {
          delims.splice(closerPos, 1);
        } else {
          closerPos++;
        }
      } else {
        const opener = delims[openerPos];
        const use = opener.len >= 2 && closer.len >= 2 ? 2 : 1;
        const kind = closer.ch === '~' ? 'del' : use === 2 ? 'strong' : 'em';
        const wrap = inode(kind);
        // move nodes between opener.node and closer.node into wrap
        let cur = opener.node.next;
        const between = [];
        while (cur && cur !== closer.node) { const nx = cur.next; between.push(cur); cur = nx; }
        for (const b of between) detach(b, root);
        for (const b of between) appendNode(wrap, b);
        // insert wrap right after opener.node
        wrap.prev = opener.node;
        wrap.next = closer.node;
        opener.node.next = wrap;
        closer.node.prev = wrap;
        if (root.last === closer.node) root.last = closer.node; // unchanged
        matchedClosers.push({ ch: closer.ch, pos: closer.pos, end: closer.pos + closer.origLen, use, openerPos: opener.pos });
        opener.used = true;
        closer.used = true;
        opener.len -= use;
        closer.len -= use;
        opener.node.s = opener.node.s.slice(0, opener.len);
        closer.node.s = closer.node.s.slice(closer.node.s.length - closer.len);
        // drop delimiters that were between the pair
        delims.splice(openerPos + 1, closerPos - openerPos - 1);
        closerPos = openerPos + 1;
        if (opener.len === 0) {
          detach(opener.node, root);
          delims.splice(openerPos, 1);
          closerPos--;
        }
        if (closer.len === 0) {
          detach(closer.node, root);
          delims.splice(closerPos, 1);
        }
      }
      // advance to next closer
      let next = -1;
      for (let j = Math.max(closerPos, bottom); j < delims.length; j++) {
        if (delims[j].canClose) { next = j; break; }
      }
      closerPos = next;
    }
  }

  while (i < n) {
    const c = s[i];

    if (c === '\\') {
      const next = s[i + 1];
      if (next === '\n') {
        addNode(inode('hard'));
        i += 2;
        while (s[i] === ' ' || s[i] === '\t') i++;
        continue;
      }
      if (next !== undefined && isPunct(next)) { addNode(inode('esc', next)); i += 2; continue; }
      addText('\\');
      i++;
      continue;
    }

    if (c === '\n') {
      const last = root.last;
      let hard = false;
      if (last && last.k === 'text' && !last.delimRun && / {2}$/.test(last.s)) {
        hard = true;
        last.s = last.s.replace(/[ \t]+$/, '');
        if (last.s === '') detach(last, root);
      }
      addNode(inode(hard ? 'hard' : 'soft'));
      i++;
      if (hard) while (s[i] === ' ' || s[i] === '\t') i++;
      continue;
    }

    if (c === '`') {
      let runLen = 0;
      while (s[i + runLen] === '`') runLen++;
      // find a matching run
      let j = i + runLen, found = -1;
      while (j < n) {
        if (s[j] === '`') {
          let l = 0;
          while (s[j + l] === '`') l++;
          if (l === runLen) { found = j; break; }
          j += l;
        } else j++;
      }
      if (found === -1) {
        addText(s.slice(i, i + runLen));
        i += runLen;
        continue;
      }
      let content = s.slice(i + runLen, found).replace(/\n/g, ' ');
      if (content.length >= 2 && content.startsWith(' ') && content.endsWith(' ')
          && /[^ ]/.test(content)) {
        content = content.slice(1, -1);
      }
      addNode(inode('code', content));
      i = found + runLen;
      continue;
    }

    if (c === '<') {
      const rest = s.slice(i);
      let m = SCHEME_AUTOLINK_RE.exec(rest);
      if (m) {
        const link = inode('link');
        link.href = m[1];
        link.auto = true;
        appendNode(link, inode('text', m[1]));
        addNode(link);
        i += m[0].length;
        continue;
      }
      m = EMAIL_AUTOLINK_RE.exec(rest);
      if (m) {
        const link = inode('link');
        link.href = 'mailto:' + m[1];
        link.auto = true;
        appendNode(link, inode('text', m[1]));
        addNode(link);
        i += m[0].length;
        continue;
      }
      // raw HTML forms
      let htmlEnd = -1, isHtml = false;
      if (rest.startsWith('<!--')) {
        const end = rest.indexOf('-->', 2);
        if (end !== -1) { htmlEnd = end + 3; isHtml = true; }
      } else if (rest.startsWith('<?')) {
        const end = rest.indexOf('?>', 2);
        if (end !== -1) { htmlEnd = end + 2; isHtml = true; }
      } else if (rest.startsWith('<![CDATA[')) {
        const end = rest.indexOf(']]>', 9);
        if (end !== -1) { htmlEnd = end + 3; isHtml = true; }
      } else if (/^<![A-Za-z]/.test(rest)) {
        const end = rest.indexOf('>', 2);
        if (end !== -1) { htmlEnd = end + 1; isHtml = true; }
      } else {
        const t = matchTagAt(s, i, false);
        if (t > 0) { htmlEnd = t - i; isHtml = true; }
      }
      if (isHtml) {
        const raw = s.slice(i, i + htmlEnd);
        if (/^<a /i.test(raw)) IN_LINK = true;
        else if (/^<\/a>$/i.test(raw)) IN_LINK = false;
        addNode(inode('html', raw));
        i += htmlEnd;
        continue;
      }
      addText('<');
      i++;
      continue;
    }

    if (c === '&') {
      const m = /^&#(?:[0-9]+|[xX][0-9A-Fa-f]+);/.exec(s.slice(i, i + 12));
      if (m) {
        const decoded = decodeNumericRef(m[0].slice(2, -1));
        if (decoded !== null) { addNode(inode('esc', decoded)); i += m[0].length; continue; }
      }
      addText('&');
      i++;
      continue;
    }

    if (c === '!' && s[i + 1] === '[') {
      const node = inode('text', '![');
      node.brk = true;
      addNode(node);
      brackets.push({ node, image: true, delimLen: delims.length, inactive: false, srcPos: i + 1 });
      i += 2;
      continue;
    }

    if (c === '[') {
      const node = inode('text', '[');
      node.brk = true;
      addNode(node);
      brackets.push({ node, image: false, delimLen: delims.length, inactive: false, srcPos: i });
      i++;
      continue;
    }

    if (c === ']') {
      const br = brackets[brackets.length - 1];
      if (!br || br.inactive) {
        if (br) brackets.pop();
        addText(']');
        i++;
        continue;
      }
      // Try to form a link or image.
      let href = null, title = null, endPos = -1, isRef = false;
      let p = i + 1;
      if (s[p] === '(') {
        // inline link
        let q = p + 1;
        while (q < n && isSpace(s[q])) q++;
        let dest = null;
        if (s[q] === ')') { dest = { href: '', end: q }; }
        else dest = parseDestAt(s, q);
        if (dest) {
          let r = dest.end;
          while (r < n && isSpace(s[r])) r++;
          let t = null;
          if (s[r] !== ')' && r > dest.end) {
            t = parseTitleAt(s, r);
            if (t) {
              let e = t.end;
              while (e < n && isSpace(s[e])) e++;
              r = e;
            }
          }
          if (s[r] === ')') {
            href = unescapeStr(dest.href);
            title = t ? unescapeStr(t.title) : null;
            endPos = r + 1;
          }
        }
      }
      let refFailed = false;
      if (endPos === -1 && s[p] === '[') {
        // full or collapsed reference
        let q = p + 1, labelEnd = -1;
        while (q < n) {
          if (s[q] === '\\') { q += 2; continue; }
          if (s[q] === ']') { labelEnd = q; break; }
          if (s[q] === '[') break;
          q++;
        }
        if (labelEnd !== -1) {
          let label = s.slice(p + 1, labelEnd);
          if (label === '') label = s.slice(br.srcPos + 1, i);
          const found = links.get(normaliseLabel(label));
          if (found) {
            href = found.href; title = found.title;
            endPos = labelEnd + 1; isRef = true;
          } else {
            refFailed = true; // a [label] was present but matched nothing:
            // the shortcut form is not tried after this
          }
        }
      }
      if (endPos === -1 && !refFailed) {
        // shortcut reference: the bracket's own source text is the label
        const label = s.slice(br.srcPos + 1, i);
        const found = label ? links.get(normaliseLabel(label)) : undefined;
        if (found) {
          href = found.href; title = found.title;
          endPos = i + 1; isRef = true;
        }
      }
      if (endPos === -1) {
        brackets.pop();
        addText(']');
        i++;
        continue;
      }
      // success: resolve emphasis inside the bracket first, then drop any
      // delimiters that were left inside (emphasis does not span a link)
      processEmphasis(br.delimLen);
      delims.length = br.delimLen;
      const link = inode(br.image ? 'image' : 'link');
      link.href = br.image ? href : href;
      link.title = title;
      // move siblings after br.node into the link
      let cur = br.node.next;
      const between = [];
      while (cur) { const nx = cur.next; between.push(cur); cur = nx; }
      for (const b of between) detach(b, root);
      for (const b of between) appendNode(link, b);
      detach(br.node, root);
      addNode(link);
      brackets.pop();
      if (!br.image) {
        // a link cannot contain another link: deactivate earlier link
        // brackets (image brackets stay live), and unwrap autolinks
        // captured inside this one
        for (const b of brackets) if (!b.image) b.inactive = true;
        unwrapAutolinks(link);
      }
      i = endPos;
      continue;
    }

    if (c === '*' || c === '_' || c === '~') {
      let runLen = 0;
      while (s[i + runLen] === c) runLen++;
      const before = i > 0 ? s[i - 1] : undefined;
      const after = i + runLen < n ? s[i + runLen] : undefined;
      const beforeWs = before === undefined || isSpace(before);
      const afterWs = after === undefined || isSpace(after);
      const beforeP = isPunctU(before), afterP = isPunctU(after);
      const leftFlank = !afterWs && (!afterP || beforeWs || beforeP);
      const rightFlank = !beforeWs && (!beforeP || afterWs || afterP);
      let canOpen, canClose;
      if (c === '_') {
        canOpen = leftFlank && (!rightFlank || beforeP);
        canClose = rightFlank && (!leftFlank || afterP);
      } else {
        canOpen = leftFlank;
        canClose = rightFlank;
      }
      if (c === '~' && runLen > 2) {
        addText(s.slice(i, i + runLen));
        i += runLen;
        continue;
      }
      const node = inode('text', s.slice(i, i + runLen));
      node.delimRun = true;
      addNode(node);
      const entry = { node, ch: c, len: runLen, canOpen, canClose, pos: i, origLen: runLen, used: false };
      delims.push(entry);
      allRuns.push(entry);
      i += runLen;
      continue;
    }

    // extended autolinks at word starts
    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) {
      const auto = matchExtendedAutolink(s, i, brackets.length > 0, delims);
      if (auto) {
        const link = inode('link');
        link.href = auto.href;
        link.auto = 2;
        appendNode(link, inode('text', auto.text));
        addNode(link);
        i = auto.end;
        continue;
      }
    }

    // plain text run: consume until the next special character or a spot
    // where an extended autolink could begin (a word character right after
    // a character that cannot be part of an address)
    let j = i + 1;
    while (j < n) {
      const cc = s[j];
      if (cc === '\\' || cc === '`' || cc === '<' || cc === '&' || cc === '[' || cc === ']'
          || cc === '*' || cc === '_' || cc === '~' || cc === '\n') break;
      if (cc === '!' && s[j + 1] === '[') break;
      if (/[A-Za-z0-9]/.test(cc)
          && !/[A-Za-z0-9.!#$%&'*+\/=?^_`{|}~@-]/.test(s[j - 1])) break;
      j++;
    }
    addText(s.slice(i, j));
    i = j;
  }

  processEmphasis(0);
  return root;

  // The plain text of everything appended after `node` (used for reference
  // labels and image alt text).
  function plainTextBetween(node) {
    let out = '';
    let cur = node.next;
    while (cur) { out += plainTextOf(cur); cur = cur.next; }
    return out;
  }
}

function plainTextOf(node) {
  switch (node.k) {
    case 'text': return node.s;
    case 'esc': return node.s;
    case 'code': return node.s;
    case 'html': return '';
    case 'soft': case 'hard': return '\n';
    default: {
      let out = '';
      let cur = node.first;
      while (cur) { out += plainTextOf(cur); cur = cur.next; }
      return out;
    }
  }
}

// Replace any autolink nodes inside a freshly formed link with their text
// (links cannot nest, and GFM does not autolink inside link text).
function unwrapAutolinks(container) {
  let cur = container.first;
  while (cur) {
    const nx = cur.next;
    if (cur.k === 'link' && cur.auto === 2) {
      const textNode = inode('text', plainTextOf(cur));
      textNode.prev = cur.prev; textNode.next = cur.next;
      if (cur.prev) cur.prev.next = textNode;
      if (cur.next) cur.next.prev = textNode;
      if (container.first === cur) container.first = textNode;
      if (container.last === cur) container.last = textNode;
    } else if (cur.first) {
      unwrapAutolinks(cur);
    }
    cur = nx;
  }
}

// --- rendering --------------------------------------------------------------

function renderInlineNodes(node) {
  let out = '';
  let cur = node.first;
  while (cur) { out += renderInlineNode(cur); cur = cur.next; }
  return out;
}

function renderInlineNode(node) {
  switch (node.k) {
    case 'text': return escapeText(node.s);
    case 'esc': return node.s.length === 1 && ESCAPES[node.s] ? ESCAPES[node.s] : escapeText(node.s);
    case 'code': return '<code>' + escapeCode(node.s) + '</code>';
    case 'html': return node.s;
    case 'soft': return '\n';
    case 'hard': return '<br>';
    case 'em': return '<em>' + renderInlineNodes(node) + '</em>';
    case 'strong': return '<strong>' + renderInlineNodes(node) + '</strong>';
    case 'del': return '<del>' + renderInlineNodes(node) + '</del>';
    case 'link': {
      let out = '<a href="' + escapeAttr(encodeHref(node.href)) + '"';
      if (node.title !== null) out += ' title="' + escapeAttr(node.title) + '"';
      return out + '>' + renderInlineNodes(node) + '</a>';
    }
    case 'image': {
      let out = '<img src="' + escapeAttr(encodeHref(node.href)) + '" alt="'
        + escapeAttr(plainTextOfChildren(node)) + '"';
      if (node.title !== null) out += ' title="' + escapeAttr(node.title) + '"';
      return out + '>';
    }
    default: return renderInlineNodes(node);
  }
}

function plainTextOfChildren(node) {
  let out = '';
  let cur = node.first;
  while (cur) { out += plainTextOf(cur); cur = cur.next; }
  return out;
}

function renderBlocks(blocks, links, tight) {
  let out = '';
  for (const b of blocks) out += renderBlock(b, links, tight);
  return out;
}

function renderBlock(b, links, tight) {
  switch (b.t) {
    case 'para': {
      const html = renderInlineNodes(parseInline(b.text, links));
      return tight ? html : '<p>' + html + '</p>\n';
    }
    case 'heading':
      return '<h' + b.level + '>' + renderInlineNodes(parseInline(b.text, links)) + '</h' + b.level + '>\n';
    case 'code': {
      let cls = '';
      if (b.info) {
        const lang = b.info.split(/\s+/, 1)[0];
        if (lang) cls = ' class="language-' + escapeAttr(lang) + '"';
      }
      return '<pre><code' + cls + '>' + escapeCode(b.text) + '</code></pre>\n';
    }
    case 'hr': return '<hr>\n';
    case 'html': return b.text;
    case 'quote':
      return '<blockquote>\n' + renderBlocks(b.children, links, false) + '</blockquote>\n';
    case 'list': return renderList(b, links);
    case 'table': return renderTable(b, links);
    default: return '';
  }
}

function renderList(list, links) {
  const tag = list.bullet ? 'ul' : 'ol';
  let out = '<' + tag + (!list.bullet && list.start !== 1 ? ' start="' + list.start + '"' : '') + '>\n';
  for (const item of list.items) {
    out += '<li>' + renderItem(item, list.tight, links) + '</li>\n';
  }
  return out + '</' + tag + '>\n';
}

function renderItem(blocks, tight, links) {
  let prefix = '';
  let bs = blocks;
  if (bs.length && bs[0].t === 'para') {
    const txt = bs[0].text;
    const task = /^\[( |x|X)\]( )/.exec(txt) || /^\[( |x|X)\]$/.exec(txt);
    if (task) {
      const checked = task[1] !== ' ';
      prefix = checked
        ? '<input checked="" disabled="" type="checkbox">'
        : '<input disabled="" type="checkbox">';
      const rest = txt.slice(3);
      bs = [{ t: 'para', text: rest }].concat(bs.slice(1));
      let out = prefix;
      if (tight) {
        out += renderInlineNodes(parseInline(bs[0].text, links));
        for (let k = 1; k < bs.length; k++) {
          const b = bs[k];
          out += b.t === 'para'
            ? renderInlineNodes(parseInline(b.text, links))
            : renderBlock(b, links, true);
        }
      } else {
        out = '<p>' + prefix + renderInlineNodes(parseInline(bs[0].text, links)) + '</p>\n';
        for (let k = 1; k < bs.length; k++) out += renderBlock(bs[k], links, false);
      }
      return out;
    }
  }
  if (tight) {
    let out = '';
    for (const b of bs) {
      out += b.t === 'para'
        ? renderInlineNodes(parseInline(b.text, links))
        : renderBlock(b, links, tight);
    }
    return out;
  }
  let out = '';
  for (const b of bs) out += renderBlock(b, links, false);
  return out;
}

function renderTable(tbl, links) {
  let out = '<table>\n<thead>\n<tr>\n';
  for (let c = 0; c < tbl.header.length; c++) {
    const align = tbl.aligns[c];
    out += '<th' + (align ? ' align="' + align + '"' : '') + '>'
      + renderInlineNodes(parseInline(tbl.header[c], links)) + '</th>\n';
  }
  out += '</tr>\n</thead>\n';
  if (tbl.rows.length === 0) return out + '</table>\n';
  out += '<tbody>';
  for (const row of tbl.rows) {
    out += '<tr>\n';
    for (let c = 0; c < tbl.header.length; c++) {
      const align = tbl.aligns[c];
      const cell = c < row.length ? row[c] : '';
      out += '<td' + (align ? ' align="' + align + '"' : '') + '>'
        + renderInlineNodes(parseInline(cell, links)) + '</td>\n';
    }
    out += '</tr>\n';
  }
  return out + '</tbody></table>\n';
}

// --- entry point --------------------------------------------------------------

/**
 * Render a Markdown string to HTML with the same output as marked 18.1.3
 * under its default options. Stateless: nothing is kept between calls.
 */
// Marked leaks its "inside a link" inline state across blocks: an
// unclosed <a ...> tag (with a space after the tag name) anywhere in
// inline content disables extended autolinks from that point on, until
// an inline </a> appears. This flag models that, per parse() call.
let IN_LINK = false;

export function parse(markdown) {
  let src = typeof markdown === 'string' ? markdown : String(markdown);
  if (src.indexOf('\r') !== -1) src = src.replace(/\r\n|\r/g, '\n');
  if (src.indexOf('\0') !== -1) src = src.replace(/\0/g, '�');
  IN_LINK = false;
  const state = { links: new Map(), endsWithNl: src.endsWith('\n') };
  const lines = src.split('\n');
  if (state.endsWithNl) lines.pop();
  const blocks = lexBlocks(lines, state, true).blocks;
  return renderBlocks(blocks, state.links, false);
}
