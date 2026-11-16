// Driver for the markdown-render-speed-02 entry.
//
// The harness runs this file as `node /bot/main.ts`. It loads the case list
// from the input directory, renders every case independently through the
// parser in parse.js, and writes the resulting HTML strings, in order, as a
// JSON array to the output directory. The MAKEFUN_INPUT_DIR and
// MAKEFUN_OUTPUT_DIR environment variables override the two locations so the
// same driver can be exercised outside the grading container.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

type Case = { id: string; markdown: string };

const inputDir = process.env.MAKEFUN_INPUT_DIR || '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';

const raw = readFileSync(join(inputDir, 'cases.json'), 'utf8');
const cases = JSON.parse(raw) as Case[];

const rendered = new Array<string>(cases.length);
for (let i = 0; i < cases.length; i++) {
  rendered[i] = parse(cases[i].markdown);
}

writeFileSync(join(outputDir, 'html.json'), JSON.stringify(rendered));
