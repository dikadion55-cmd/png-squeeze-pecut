// png-squeeze-01 V1: lossless PNG re-encoder.
// Self-contained (Node built-ins only). Decodes each input screenshot to RGBA,
// picks the smallest lossless form (palette / grey / RGB / RGBA, with tRNS keys),
// chooses per-row PNG filters (fixed, min-sum, fewest-pairs, brute-force deflate),
// and writes the winner with zlib level 9. Deterministic: fixed work per input,
// no clock, no randomness, no environment reads for variation.
import { deflateSync, inflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------------------------------------------------------------- CRC32
const CRC_TABLE: Uint32Array = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(buf: Uint8Array): number {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function chunk(type: string, data: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + data.length);
  const dv = new DataView(out.buffer);
  dv.setUint32(0, data.length);
  out[4] = type.charCodeAt(0);
  out[5] = type.charCodeAt(1);
  out[6] = type.charCodeAt(2);
  out[7] = type.charCodeAt(3);
  out.set(data, 8);
  dv.setUint32(8 + data.length, crc32(out.subarray(4, 8 + data.length)));
  return out;
}

function pngOf(chunks: [string, Uint8Array][]): Uint8Array {
  const sig = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
  const parts: Uint8Array[] = [sig];
  let total = sig.length;
  for (const [type, data] of chunks) {
    const c = chunk(type, data);
    parts.push(c);
    total += c.length;
  }
  const out = new Uint8Array(total);
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}

function ihdrOf(width: number, height: number, colourType: number): Uint8Array {
  const b = new Uint8Array(13);
  const dv = new DataView(b.buffer);
  dv.setUint32(0, width);
  dv.setUint32(4, height);
  b[8] = 8; // bit depth
  b[9] = colourType;
  b[10] = 0; // compression
  b[11] = 0; // filter
  b[12] = 0; // interlace
  return b;
}

// ---------------------------------------------------------------- PNG decode
const BPP_OF: Record<number, number> = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

function paethPredictor(left: number, up: number, upLeft: number): number {
  const p = left + up - upLeft;
  const pa = Math.abs(p - left);
  const pb = Math.abs(p - up);
  const pc = Math.abs(p - upLeft);
  if (pa <= pb && pa <= pc) return left;
  if (pb <= pc) return up;
  return upLeft;
}

function unfilterRow(
  filter: number,
  row: Uint8Array,
  prev: Uint8Array | null,
  bpp: number,
): void {
  const n = row.length;
  if (filter === 0) return;
  if (filter === 1) {
    for (let i = bpp; i < n; i++) row[i] = (row[i] + row[i - bpp]) & 0xff;
  } else if (filter === 2) {
    if (prev) for (let i = 0; i < n; i++) row[i] = (row[i] + prev[i]) & 0xff;
  } else if (filter === 3) {
    for (let i = 0; i < n; i++) {
      const left = i >= bpp ? row[i - bpp] : 0;
      const up = prev ? prev[i] : 0;
      row[i] = (row[i] + ((left + up) >> 1)) & 0xff;
    }
  } else if (filter === 4) {
    for (let i = 0; i < n; i++) {
      const left = i >= bpp ? row[i - bpp] : 0;
      const up = prev ? prev[i] : 0;
      const upLeft = prev && i >= bpp ? prev[i - bpp] : 0;
      row[i] = (row[i] + paethPredictor(left, up, upLeft)) & 0xff;
    }
  } else {
    throw new Error(`unknown filter ${filter}`);
  }
}

interface Decoded {
  rgba: Uint8Array;
  width: number;
  height: number;
}

function decodePng(bytes: Uint8Array): Decoded {
  if (
    bytes.length < 8 ||
    bytes[0] !== 137 || bytes[1] !== 80 || bytes[2] !== 78 || bytes[3] !== 71 ||
    bytes[4] !== 13 || bytes[5] !== 10 || bytes[6] !== 26 || bytes[7] !== 10
  ) {
    throw new Error('not a PNG');
  }
  let width = 0;
  let height = 0;
  let colourType = -1;
  let bitDepth = -1;
  let interlace = -1;
  let plte: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idat: Uint8Array[] = [];
  let idatLen = 0;
  let at = 8;
  while (at + 8 <= bytes.length) {
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    const len = dv.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    if (type === 'IHDR') {
      const d = new DataView(data.buffer, data.byteOffset, data.byteLength);
      width = d.getUint32(0);
      height = d.getUint32(4);
      bitDepth = data[8];
      colourType = data[9];
      interlace = data[12];
    } else if (type === 'PLTE') {
      plte = data;
    } else if (type === 'tRNS') {
      trns = data;
    } else if (type === 'IDAT') {
      idat.push(data);
      idatLen += len;
    } else if (type === 'IEND') {
      break;
    }
    at += 12 + len;
  }
  if (bitDepth !== 8) throw new Error(`bit depth ${bitDepth}`);
  if (interlace !== 0) throw new Error('interlaced');
  const bpp = BPP_OF[colourType];
  if (bpp === undefined) throw new Error(`colour type ${colourType}`);
  const raw = new Uint8Array(idatLen);
  let off = 0;
  for (const part of idat) {
    raw.set(part, off);
    off += part.length;
  }
  const inflated = inflateSync(raw);
  const stride = width * bpp;
  const samples = new Uint8Array(width * height * bpp);
  let prev: Uint8Array | null = null;
  for (let y = 0; y < height; y++) {
    const filter = inflated[y * (stride + 1)];
    const row = inflated.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1));
    const out = samples.subarray(y * stride, (y + 1) * stride);
    out.set(row);
    unfilterRow(filter, out, prev, bpp);
    prev = out;
  }
  // Expand samples to RGBA.
  const rgba = new Uint8Array(width * height * 4);
  const n = width * height;
  if (colourType === 6) {
    rgba.set(samples);
  } else if (colourType === 2) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = 255;
    }
  } else if (colourType === 0) {
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = g;
      rgba[d + 1] = g;
      rgba[d + 2] = g;
      rgba[d + 3] = 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      const g = samples[s];
      rgba[d] = g;
      rgba[d + 1] = g;
      rgba[d + 2] = g;
      rgba[d + 3] = samples[s + 1];
    }
  } else if (colourType === 3) {
    if (plte === null) throw new Error('palette without PLTE');
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const idx = samples[i] * 3;
      rgba[d] = plte[idx];
      rgba[d + 1] = plte[idx + 1];
      rgba[d + 2] = plte[idx + 2];
      rgba[d + 3] = trns && samples[i] < trns.length ? trns[samples[i]] : 255;
    }
  }
  return { rgba, width, height };
}

// ---------------------------------------------------------------- Analyse
interface Colour {
  rgba: [number, number, number, number];
  word: number;
  count: number;
}

interface Analysis {
  opaque: boolean;
  grey: boolean;
  colours: Colour[] | null; // null when > 256 distinct colours
}

function analyse(rgba: Uint8Array): Analysis {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map<number, number>();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const r = rgba[d];
    const g = rgba[d + 1];
    const b = rgba[d + 2];
    const a = rgba[d + 3];
    if (a !== 255) opaque = false;
    if (r !== g || r !== b) grey = false;
    if (!many) {
      const w = (r | (g << 8) | (b << 16) | (a << 24)) >>> 0;
      const k = counts.get(w);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(w, 1);
      } else {
        counts.set(w, k + 1);
      }
    }
  }
  if (many) return { opaque, grey, colours: null };
  const colours: Colour[] = [];
  for (const [w, count] of counts) {
    colours.push({
      rgba: [w & 0xff, (w >>> 8) & 0xff, (w >>> 16) & 0xff, (w >>> 24) & 0xff],
      word: w,
      count,
    });
  }
  return { opaque, grey, colours };
}

/** The single fully-transparent value usable as a tRNS key, or null. */
function transparentKey(rgba: Uint8Array, grey: boolean): number | null {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

// ---------------------------------------------------------------- Forms
interface Form {
  colourType: number;
  bpp: number;
  samples: Uint8Array;
  plte: Uint8Array | null;
  trns: Uint8Array | null;
  filters: (number | 'minsum' | 'pairs' | 'brute')[];
}

function samplesOf(rgba: Uint8Array, ct: number): Uint8Array {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

function paletteOrder(colours: Colour[], order: 'count' | 'luminance'): Colour[] {
  const lum = (c: Colour): number => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

function paletteForm(
  rgba: Uint8Array,
  colours: Colour[],
  order: 'count' | 'luminance',
): { plte: Uint8Array; trns: Uint8Array | null; indices: Uint8Array } {
  const entries = paletteOrder(colours, order);
  const index = new Map<number, number>(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns =
    transparent === 0
      ? null
      : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const w = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) >>> 0;
    indices[i] = index.get(w) as number;
  }
  return { plte, trns, indices };
}

const FILTERS_CHANNEL: (number | 'minsum' | 'pairs' | 'brute')[] = [
  0, 1, 2, 4, 'minsum', 'pairs', 'brute',
];
const FILTERS_PALETTE: (number | 'minsum' | 'pairs' | 'brute')[] = [0];
const FILTERS_PALETTE_LUM: (number | 'minsum' | 'pairs' | 'brute')[] = [0, 'minsum', 'brute'];

function formsOf(rgba: Uint8Array): Form[] {
  const { opaque, grey, colours } = analyse(rgba);
  const forms: Form[] = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', FILTERS_PALETTE],
      ['luminance', FILTERS_PALETTE_LUM],
    ] as const) {
      const p = paletteForm(rgba, colours, order);
      forms.push({
        colourType: 3,
        bpp: 1,
        samples: p.indices,
        plte: p.plte,
        trns: p.trns,
        filters,
      });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct: number;
  let trns: Uint8Array | null = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) {
      trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
    }
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct] as number;
  forms.push({
    colourType: ct,
    bpp,
    samples: samplesOf(rgba, ct),
    plte: null,
    trns,
    filters: FILTERS_CHANNEL,
  });
  return forms;
}

// ---------------------------------------------------------------- Filters
function filterRow(
  type: number,
  cur: Uint8Array,
  prev: Uint8Array | null,
  bpp: number,
  out: Uint8Array,
): void {
  const n = cur.length;
  if (type === 0) {
    out.set(cur);
    return;
  }
  if (type === 1) {
    for (let i = 0; i < n; i++) {
      const left = i >= bpp ? cur[i - bpp] : 0;
      out[i] = (cur[i] - left) & 0xff;
    }
  } else if (type === 2) {
    for (let i = 0; i < n; i++) {
      const up = prev ? prev[i] : 0;
      out[i] = (cur[i] - up) & 0xff;
    }
  } else if (type === 3) {
    for (let i = 0; i < n; i++) {
      const left = i >= bpp ? cur[i - bpp] : 0;
      const up = prev ? prev[i] : 0;
      out[i] = (cur[i] - ((left + up) >> 1)) & 0xff;
    }
  } else {
    for (let i = 0; i < n; i++) {
      const left = i >= bpp ? cur[i - bpp] : 0;
      const up = prev ? prev[i] : 0;
      const upLeft = prev && i >= bpp ? prev[i - bpp] : 0;
      out[i] = (cur[i] - paethPredictor(left, up, upLeft)) & 0xff;
    }
  }
}

function signedSum(row: Uint8Array): number {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const b = row[i];
    s += b > 127 ? 256 - b : b;
  }
  return s;
}

function pairsOf(row: Uint8Array, seen: Uint32Array, stamp: number): number {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

type FilterChoice = number | 'minsum' | 'pairs' | 'brute';

function filtered(
  samples: Uint8Array,
  width: number,
  height: number,
  bpp: number,
  choice: FilterChoice,
): Uint8Array {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial: Uint8Array[] = [];
  for (let t = 0; t < 5; t++) {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    trial.push(row);
  }
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost: number;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else {
        cost = deflateSync(
          trial[t],
          before.length === 0
            ? { level: BRUTE_LEVEL, memLevel: 9 }
            : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before },
        ).length;
      }
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------------------------------------------------------------- Encode one image
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };

function chunkBytes(form: Form): number {
  return (
    (form.plte === null ? 0 : 12 + form.plte.length) +
    (form.trns === null ? 0 : 12 + form.trns.length)
  );
}

function encodeImage(rgba: Uint8Array, width: number, height: number): Uint8Array {
  let best: { form: Form; data: Uint8Array; zlib: Uint8Array; bytes: number } | null = null;
  for (const form of formsOf(rgba)) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, SCREEN);
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) {
        best = {
          form,
          data,
          zlib: new Uint8Array(zlib.buffer, zlib.byteOffset, zlib.length),
          bytes,
        };
      }
    }
  }
  if (best === null) throw new Error('no form');
  const { form, data } = best;
  // Final compression: try a small grid of level-9 settings and keep the
  // smallest stream, but never worse than the screened level-6 stream
  // (level 9 can be BIGGER than level 6 on some data). A 14-bit window
  // wins on the largest images (shorter distance codes, matches stay local).
  let zlib: Uint8Array = best.zlib;
  for (const opts of [
    { level: 9, memLevel: 9 },
    { level: 9, memLevel: 9, strategy: constants.Z_FILTERED },
    { level: 9, memLevel: 8 },
    { level: 9, memLevel: 8, strategy: constants.Z_FILTERED },
    { level: 9, memLevel: 8, windowBits: 14 },
    { level: 9, memLevel: 8, strategy: constants.Z_FILTERED, windowBits: 14 },
  ] as const) {
    const z = deflateSync(data, opts);
    if (z.length < zlib.length) {
      zlib = new Uint8Array(z.buffer, z.byteOffset, z.length);
    }
  }
  const chunks: [string, Uint8Array][] = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', zlib]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------------------------------------------------------------- Main
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), encodeImage(image.rgba, image.width, image.height));
}
