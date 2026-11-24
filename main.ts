// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// Sections 1 to 4 (command line, output and exit codes, safe paths, format detection),
// 9 (JSON edits) and 10 (order and atomicity) follow the kit starter; sections 5
// (matching lines at three tiers), 6 (unified diffs), 7 (SEARCH/REPLACE blocks) and
// 8 (V4A patches) are implemented here.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this
// file hands over to runner.ts (the last lines below): keep that hand-over and runner.ts
// as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---- file lines (SPEC.md section 3) ----

interface FileState {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.final ? st.br : '');
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

// ---- matching lines (SPEC.md section 5) ----

function norm(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** Positions where O occurs in lines at the tier; occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  const no = o.map((l) => norm(l, tier));
  outer: for (let i = 0; i + o.length <= lines.length; i++) {
    for (let j = 0; j < o.length; j++) {
      if (norm(lines[i + j]!, tier) !== no[j]) continue outer;
    }
    out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2) at which O occurs at least once, with its positions. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; pos: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const pos = occurrences(lines, o, t);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** Like findTier, but only occurrences at or after `from`; an end-of-file occurrence
 *  is one that ends at the file's last line. */
function findTierFrom(
  lines: string[],
  o: string[],
  from: number,
  strict: boolean,
  eof: boolean,
): { tier: number; pos: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const pos: number[] = [];
    for (const p of occurrences(lines, o, t)) {
      if (p < from) continue;
      if (eof && p + o.length !== lines.length) continue;
      pos.push(p);
    }
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** The first line at or after `from` equal to the anchor, at the first tier where
 *  one is; -1 when there is none. */
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    for (let i = from; i < lines.length; i++) {
      if (norm(lines[i]!, t) === norm(anchor, t)) return i;
    }
  }
  return -1;
}

/** One line of N: `oIndex` is the index into O of the corresponding context line,
 *  or -1 for a line that is new. */
interface NItem {
  text: string;
  oIndex: number;
}

/** Render N at the match position: context lines are the file's own matched lines;
 *  at tier 2 every other line is re-indented from O's first line to the file's. */
function renderN(fileLines: string[], at: number, o: string[], n: NItem[], tier: number): string[] {
  const F = leadingWs(fileLines[at] ?? '');
  const P = o.length > 0 ? leadingWs(o[0]!) : '';
  return n.map((item) => {
    if (item.oIndex >= 0) return fileLines[at + item.oIndex]!;
    if (tier === 2) {
      const t = item.text;
      if (t !== '' && t.trim() !== '' && t.startsWith(P)) return F + t.slice(P.length);
      return t;
    }
    return item.text;
  });
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

interface Edit {
  apply: (tree: Tree) => void;
  /** Move pairs this edit performs, [old path, new path]. */
  moves: Array<[string, string]>;
}

const noMoves: Array<[string, string]> = [];

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return {
      moves: noMoves,
      apply: (tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, text);
      },
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return {
      moves: noMoves,
      apply: (tree) => {
        const before = exists(tree);
        const nl = before.indexOf('\n');
        const crlf = nl > 0 && before[nl - 1] === '\r';
        const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
        const t = lf(before);
        const old = lf(oldStr);
        let count = 0;
        for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
        if (count === 0) throw new Fail('no-match', p);
        if (count > 1) throw new Fail('ambiguous', p);
        const at = t.indexOf(old);
        const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
        tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
      },
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return {
      moves: noMoves,
      apply: (tree) => {
        const before = exists(tree);
        const st = splitFile(before);
        if (line < 0 || line > st.lines.length) throw new Fail('no-match', p);
        st.lines.splice(line, 0, ...add);
        tree.now.set(p, joinFile(st));
      },
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- unified diffs (SPEC.md section 6) ----

interface UBody {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
}

interface UHunk {
  /** Old-file line number (1-based) from the header. */
  a: number;
  body: UBody[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noEol: boolean;
}

interface USection {
  oldPath: string;
  newPath: string;
  isCreate: boolean;
  isDelete: boolean;
  hunks: UHunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

/** The path of a `--- ` or `+++ ` header line. */
function headerPath(l: string): string {
  let t = l.slice(4);
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t.startsWith('a/')) t = t.slice(2);
  else if (t.startsWith('b/')) t = t.slice(2);
  return t;
}

/** Parse a section's header (lines before its first hunk); fills in the paths and
 *  the creation/deletion flags. Returns the index of the first hunk header, the
 *  next section start, or the end of the patch. */
function parseUHeader(lines: string[], i: number, sec: USection): number {
  const n = lines.length;
  let oldFromPair: string | null = null;
  let newFromPair: string | null = null;
  let renameFrom: string | null = null;
  let renameTo: string | null = null;
  let hasNewFile = false;
  let hasDeletedFile = false;
  while (i < n) {
    const l = lines[i]!;
    if (l.startsWith('@@')) break;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ')) {
      if ((lines[i + 1] ?? '').startsWith('+++ ')) {
        if (oldFromPair === null) {
          oldFromPair = headerPath(l);
          newFromPair = headerPath(lines[i + 1]!);
        }
        i += 2;
        continue;
      }
      throw new Exit2(`error: parse ${i + 2}`);
    }
    if (l.startsWith('rename from ')) {
      if (renameFrom === null) renameFrom = l.slice('rename from '.length).trim();
      i++;
      continue;
    }
    if (l.startsWith('rename to ')) {
      if (renameTo === null) renameTo = l.slice('rename to '.length).trim();
      i++;
      continue;
    }
    if (l.startsWith('new file mode')) {
      hasNewFile = true;
      i++;
      continue;
    }
    if (l.startsWith('deleted file mode')) {
      hasDeletedFile = true;
      i++;
      continue;
    }
    i++;
  }
  if (oldFromPair !== null) {
    sec.oldPath = oldFromPair;
    sec.newPath = newFromPair!;
  } else if (renameFrom !== null) {
    sec.oldPath = renameFrom;
    // A lone `rename from` names only the old path; the new path stays the
    // one from the `diff --git` line.
    if (renameTo !== null) sec.newPath = renameTo;
  }
  if (sec.oldPath === '/dev/null' || hasNewFile) sec.isCreate = true;
  else if (sec.newPath === '/dev/null' || hasDeletedFile) sec.isDelete = true;
  return i;
}

/** Parse a section's hunks. Returns the index of the next section start or the
 *  end of the patch. */
function parseUHunks(lines: string[], i: number, sec: USection): number {
  const n = lines.length;
  while (i < n) {
    const l = lines[i]!;
    if (l.startsWith('@@')) {
      const m = HUNK_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(m[1]!, 10);
      i++;
      const body: UBody[] = [];
      while (i < n) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          if (bl === '') body.push({ kind: 'ctx', text: '' });
          else if (bl.startsWith(' ')) body.push({ kind: 'ctx', text: bl.slice(1) });
          else if (bl.startsWith('-')) body.push({ kind: 'old', text: bl.slice(1) });
          else if (bl.startsWith('+')) body.push({ kind: 'new', text: bl.slice(1) });
          else body.push({ kind: 'bs', text: bl.slice(1) });
          i++;
        } else break;
      }
      while (body.length > 0) {
        const b = body[body.length - 1]!;
        if (b.kind === 'ctx' && b.text === '') body.pop();
        else break;
      }
      let noEol = false;
      for (let k = 0; k < body.length; k++) {
        if (body[k]!.kind === 'ctx' || body[k]!.kind === 'new') noEol = body[k + 1]?.kind === 'bs';
      }
      sec.hunks.push({ a, body, noEol });
    } else if (l.startsWith('diff --git ')) {
      break;
    } else if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      break;
    } else {
      i++;
    }
  }
  return i;
}

function parseUnified(lines: string[]): USection[] {
  const sections: USection[] = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = DIFF_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const sec: USection = { oldPath: m[1]!, newPath: m[2]!, isCreate: false, isDelete: false, hunks: [] };
      i++;
      i = parseUHeader(lines, i, sec);
      i = parseUHunks(lines, i, sec);
      sections.push(sec);
    } else if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const sec: USection = { oldPath: '', newPath: '', isCreate: false, isDelete: false, hunks: [] };
      i = parseUHeader(lines, i, sec);
      i = parseUHunks(lines, i, sec);
      sections.push(sec);
    } else if (l.startsWith('@@')) {
      throw new Exit2(`error: parse ${i + 1}`);
    } else {
      i++;
    }
  }
  return sections;
}

/** A hunk's O lines and N lines (with context links). */
function hunkON(h: UHunk): { o: string[]; n: NItem[] } {
  const o: string[] = [];
  const n: NItem[] = [];
  for (const b of h.body) {
    if (b.kind === 'bs') continue;
    if (b.kind === 'ctx') {
      n.push({ text: b.text, oIndex: o.length });
      o.push(b.text);
    } else if (b.kind === 'old') {
      o.push(b.text);
    } else {
      n.push({ text: b.text, oIndex: -1 });
    }
  }
  return { o, n };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseUnified(lines);
  return sections.map((sec) => {
    const isMove = !sec.isCreate && !sec.isDelete && sec.oldPath !== sec.newPath;
    const moves: Array<[string, string]> = isMove ? [[sec.oldPath, sec.newPath]] : noMoves;
    return {
      moves,
      apply: (tree) => {
        if (sec.isCreate) {
          if (!safe(sec.newPath)) throw new Fail('unsafe', sec.newPath);
          if (tree.get(sec.newPath) !== null) throw new Fail('exists', sec.newPath);
          const plus: string[] = [];
          let noEol = false;
          for (const h of sec.hunks) {
            for (let k = 0; k < h.body.length; k++) {
              if (h.body[k]!.kind === 'new') {
                plus.push(h.body[k]!.text);
                noEol = h.body[k + 1]?.kind === 'bs';
              }
            }
          }
          tree.now.set(sec.newPath, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
          return;
        }
        if (sec.isDelete) {
          if (!safe(sec.oldPath)) throw new Fail('unsafe', sec.oldPath);
          if (tree.get(sec.oldPath) === null) throw new Fail('missing', sec.oldPath);
          tree.now.set(sec.oldPath, null);
          return;
        }
        if (!safe(sec.oldPath)) throw new Fail('unsafe', sec.oldPath);
        if (isMove && !safe(sec.newPath)) throw new Fail('unsafe', sec.newPath);
        const cur = tree.get(sec.oldPath);
        if (cur === null) throw new Fail('missing', sec.oldPath);
        if (isMove && tree.get(sec.newPath) !== null) throw new Fail('exists', sec.newPath);
        const st = splitFile(cur);
        let d = 0;
        for (const hunk of sec.hunks) {
          const { o, n } = hunkON(hunk);
          if (o.length === 0) {
            const oldLen = st.lines.length;
            const idx = Math.min(hunk.a + d, oldLen);
            st.lines.splice(idx, 0, ...n.map((x) => x.text));
            if (idx === oldLen) st.final = !hunk.noEol;
            d += n.length;
          } else {
            const found = findTier(st.lines, o, strict);
            if (!found) throw new Fail('no-match', sec.oldPath);
            const target = hunk.a - 1 + d;
            let best = found.pos[0]!;
            for (const p of found.pos) {
              if (Math.abs(p - target) < Math.abs(best - target)) best = p;
            }
            const atEnd = best + o.length === st.lines.length;
            const rendered = renderN(st.lines, best, o, n, found.tier);
            st.lines.splice(best, o.length, ...rendered);
            if (atEnd) st.final = !hunk.noEol;
            d += n.length - o.length;
          }
        }
        const out = joinFile(st);
        if (isMove) {
          tree.now.set(sec.oldPath, null);
          tree.now.set(sec.newPath, out);
        } else {
          tree.now.set(sec.oldPath, out);
        }
      },
    };
  });
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ----

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = 0;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    let s = -1;
    for (let j = i; j < n; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let path: string | null = null;
    for (let j = s - 1; j >= prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '') continue;
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = s + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    const oldLines = lines.slice(s + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push({
      moves: noMoves,
      apply: (tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (oldLines.length === 0) {
          if (tree.get(p) !== null) throw new Fail('exists', p);
          tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
          return;
        }
        const cur = tree.get(p);
        if (cur === null) throw new Fail('missing', p);
        const st = splitFile(cur);
        const found = findTier(st.lines, oldLines, strict);
        if (!found) throw new Fail('no-match', p);
        if (found.pos.length > 1) throw new Fail('ambiguous', p);
        const at = found.pos[0]!;
        const rendered = renderN(
          st.lines,
          at,
          oldLines,
          newLines.map((t) => ({ text: t, oIndex: -1 })),
          found.tier,
        );
        st.lines.splice(at, oldLines.length, ...rendered);
        tree.now.set(p, joinFile(st));
      },
    });
    prevPath = p;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

// ---- V4A patches (SPEC.md section 8) ----

interface VBody {
  kind: 'ctx' | 'old' | 'new';
  text: string;
}

interface VChunk {
  /** The anchor text, or null when the chunk has none. */
  anchor: string | null;
  body: VBody[];
  /** Ended by a `*** End of File` line: the match must end at the file's last line. */
  eof: boolean;
}

function isV4ASectionStart(l: string): boolean {
  return l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:');
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    if (l.startsWith('*** Add File:')) {
      const path = l.slice('*** Add File:'.length).trim();
      i++;
      const secStart = i;
      const secLines: string[] = [];
      while (i < last) {
        const m = lines[i]!;
        if (isV4ASectionStart(m) || m.trim() === '*** End Patch') break;
        secLines.push(m);
        i++;
      }
      while (secLines.length > 0 && blank(secLines[secLines.length - 1]!)) secLines.pop();
      const fileLines: string[] = [];
      for (let k = 0; k < secLines.length; k++) {
        const sl = secLines[k]!;
        if (sl.startsWith('+')) fileLines.push(sl.slice(1));
        else if (sl === '') fileLines.push('');
        else throw new Exit2(`error: parse ${secStart + k + 1}`);
      }
      edits.push({
        moves: noMoves,
        apply: (tree) => {
          if (!safe(path)) throw new Fail('unsafe', path);
          if (tree.get(path) !== null) throw new Fail('exists', path);
          tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
        },
      });
    } else if (l.startsWith('*** Delete File:')) {
      const path = l.slice('*** Delete File:'.length).trim();
      i++;
      while (i < last) {
        const m = lines[i]!;
        if (isV4ASectionStart(m) || m.trim() === '*** End Patch') break;
        if (blank(m)) {
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      edits.push({
        moves: noMoves,
        apply: (tree) => {
          if (!safe(path)) throw new Fail('unsafe', path);
          if (tree.get(path) === null) throw new Fail('missing', path);
          tree.now.set(path, null);
        },
      });
    } else if (l.startsWith('*** Update File:')) {
      const path = l.slice('*** Update File:'.length).trim();
      const updateLineNo = i + 1;
      i++;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to:')) {
        moveTo = lines[i]!.slice('*** Move to:'.length).trim();
        i++;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      let afterEof = false;
      while (i < last) {
        const m = lines[i]!;
        if (isV4ASectionStart(m) || m.trim() === '*** End Patch') break;
        if (m.startsWith('@@')) {
          const anchorText = m.slice(2).trim();
          cur = { anchor: anchorText === '' ? null : anchorText, body: [], eof: false };
          chunks.push(cur);
          afterEof = false;
          i++;
          continue;
        }
        if (m.trim() === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
          cur.eof = true;
          cur = null;
          afterEof = true;
          i++;
          continue;
        }
        // A blank line after a chunk ended is at the end of the section (or
        // between chunks): it is not part of the section, so it is ignored.
        if (cur === null && afterEof && blank(m)) {
          i++;
          continue;
        }
        if (m.startsWith(' ') || m.startsWith('-') || m.startsWith('+') || m === '') {
          if (cur === null) {
            if (chunks.length === 0 && !afterEof) {
              cur = { anchor: null, body: [], eof: false };
              chunks.push(cur);
            } else {
              throw new Exit2(`error: parse ${i + 1}`);
            }
          }
          if (m === '') cur.body.push({ kind: 'ctx', text: '' });
          else if (m.startsWith(' ')) cur.body.push({ kind: 'ctx', text: m.slice(1) });
          else if (m.startsWith('-')) cur.body.push({ kind: 'old', text: m.slice(1) });
          else cur.body.push({ kind: 'new', text: m.slice(1) });
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      if (chunks.length > 0) {
        const lc = chunks[chunks.length - 1]!;
        while (lc.body.length > 0) {
          const b = lc.body[lc.body.length - 1]!;
          if (b.kind === 'ctx' && b.text.trim() === '') lc.body.pop();
          else break;
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLineNo}`);
      const moves: Array<[string, string]> = moveTo !== null ? [[path, moveTo]] : noMoves;
      const mt = moveTo;
      edits.push({
        moves,
        apply: (tree) => {
          if (!safe(path)) throw new Fail('unsafe', path);
          if (mt !== null && !safe(mt)) throw new Fail('unsafe', mt);
          const cur = tree.get(path);
          if (cur === null) throw new Fail('missing', path);
          if (mt !== null && tree.get(mt) !== null) throw new Fail('exists', mt);
          const st = splitFile(cur);
          let cursor = 0;
          for (const chunk of chunks) {
            if (chunk.anchor !== null) {
              const a = findAnchor(st.lines, chunk.anchor, cursor, strict);
              if (a < 0) throw new Fail('no-match', path);
              cursor = a + 1;
            }
            const o: string[] = [];
            const n: NItem[] = [];
            for (const b of chunk.body) {
              if (b.kind === 'ctx') {
                n.push({ text: b.text, oIndex: o.length });
                o.push(b.text);
              } else if (b.kind === 'old') {
                o.push(b.text);
              } else {
                n.push({ text: b.text, oIndex: -1 });
              }
            }
            if (o.length === 0) {
              const idx = chunk.eof ? st.lines.length : cursor;
              st.lines.splice(idx, 0, ...n.map((x) => x.text));
              cursor = idx + n.length;
            } else {
              const found = findTierFrom(st.lines, o, cursor, strict, chunk.eof);
              if (!found) throw new Fail('no-match', path);
              const at = found.pos[0]!;
              const rendered = renderN(st.lines, at, o, n, found.tier);
              st.lines.splice(at, o.length, ...rendered);
              cursor = at + rendered.length;
            }
          }
          const out = joinFile(st);
          if (mt !== null) {
            tree.now.set(path, null);
            tree.now.set(mt, out);
          } else {
            tree.now.set(path, out);
          }
        },
      });
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
  }
  return edits;
}

// ---- driver (SPEC.md sections 1, 2, 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit.apply(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: { key: string; line: string }[] = [];
  const movedOld = new Set<string>();
  const movedNew = new Set<string>();
  for (const edit of edits) {
    for (const [oldP, newP] of edit.moves) {
      if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
        rows.push({ key: newP, line: `R ${oldP} -> ${newP}` });
        movedOld.add(oldP);
        movedNew.add(newP);
      }
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (!movedOld.has(p) && !movedNew.has(p)) {
      rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
    }
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = rows.map((r) => r.line);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
