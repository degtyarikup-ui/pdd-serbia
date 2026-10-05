// Road surfaces: a few small shared detail maps and one shader patch for every
// asphalt, pavement, kerb, shoulder, ballast and crossing-deck material.
//
// Phase. Texture coordinates are baked into each surface once, right before
// it is first drawn, from its world position in the frame of the road it
// belongs to. A road frame is a rigid map from world X/Z to texture metres.
// Whenever the game rebases the world (U-turn, turn into a side road), every
// live frame is moved by the same transform, so baked surfaces keep their
// pattern and new segments of the same road continue it exactly: overlapping
// pieces (SEAM) and the patches laid over markings get identical texels.
// A road that leaves a junction at an angle that is not a multiple of 90°
// gets its own frame aligned with its axis; square paving then follows it.
//
// Colour. Maps are neutral detail: 0.5 keeps the material colour, so seasons,
// wet asphalt and the existing colour-based logic keep working unchanged.
// R = detail of horizontal faces, G = smooth large-scale variation (sampled
// at a much coarser scale to break up repetition), B = detail of vertical
// faces (kerb sections). The UI theme never reaches these materials.
(function () {
  'use strict';
  const WRAP = 44.8; // every period below divides it: frame offsets wrap here
  const KERB = 0.18; // kerb / pavement height in metres
  const ASPHALT = 0x2C2F36, SIDEWALKS = new Set([0x747970, 0x7A776F, 0xB9C0C6, 0x737870]);
  // period: metres per texture tile. macro: strength of the coarse variation.
  const KINDS = {
    asphalt: { period: 6.4, macro: 0.13, macroScale: 1 / 7, size: 256 },
    pavement: { period: 5.6, macro: 0.09, macroScale: 1 / 8, size: 256, side: 2.8, joints: true },
    gravel: { period: 3.2, macro: 0.14, macroScale: 1 / 14, size: 128, side: 3.2 },
    ballast: { period: 1.6, macro: 0.1, macroScale: 1 / 28, size: 128, side: 1.6 },
    sleeper: { period: 1.6, macro: 0, macroScale: 1 / 28, size: 64, side: 1.6 },
    deck: { local: true, panel: 1.4, macro: 0.05, macroScale: 1 / 4, w: 64, h: 256 },
    // Buildings and street furniture (pass 3): mapped in metres of the
    // object's own geometry (u, v: metres per tile along a wall and up it).
    plaster: { object: true, u: 4, v: 2.7, macro: 0.07, macroScale: 1 / 3, size: 256 },
    panel: { object: true, u: 8, v: 5.4, macro: 0.05, macroScale: 1 / 2, size: 256 },
    brick: { object: true, u: 2, v: 1.35, macro: 0.08, macroScale: 1 / 6, size: 256 },
    roofTile: { geometry: true, macro: 0.06, macroScale: 1 / 4, size: 256 },
    roofFlat: { object: true, u: 4, v: 0.5, macro: 0.04, macroScale: 1 / 3, size: 128 },
    window: { geometry: true, macro: 0, macroScale: 1, w: 128, h: 128 },
    door: { geometry: true, macro: 0, macroScale: 1, w: 64, h: 128 },
    wood: { object: true, u: 1.2, v: 1.2, macro: 0.06, macroScale: 1 / 4, size: 128 },
    metal: { object: true, u: 1.2, v: 1.2, macro: 0.04, macroScale: 1 / 4, size: 128 },
  };
  const textures = new Map();
  let renderer = null, hooks = null, dirty = true;
  let frames = new Map(), nextFrame = 1;

  // ---- Deterministic, tileable painters ----------------------------------
  function rng(seed) {
    return () => { seed = (seed + 0x6D2B79F5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  }
  // Smooth value noise that repeats exactly over `size` pixels.
  function tileNoise(size, cells, rand) {
    const g = Float32Array.from({ length: cells * cells }, rand);
    return (x, y) => {
      const fx = x / size * cells, fy = y / size * cells, x0 = Math.floor(fx), y0 = Math.floor(fy);
      const tx = fx - x0, ty = fy - y0, sx = tx * tx * (3 - 2 * tx), sy = ty * ty * (3 - 2 * ty);
      const at = (i, j) => g[(((j % cells) + cells) % cells) * cells + (((i % cells) + cells) % cells)];
      const a = at(x0, y0), b = at(x0 + 1, y0), c = at(x0, y0 + 1), d = at(x0 + 1, y0 + 1);
      return a + (b - a) * sx + (c - a) * sy + (a - b - c + d) * sx * sy;
    };
  }
  // Round speckles with wrap-around, added to a channel.
  function speckles(ch, w, h, count, rand, radius, value) {
    for (let n = 0; n < count; n++) {
      const cx = rand() * w, cy = rand() * h, r = radius[0] + rand() * (radius[1] - radius[0]);
      const v = value[0] + rand() * (value[1] - value[0]);
      for (let y = Math.floor(cy - r - 1); y <= cy + r + 1; y++) for (let x = Math.floor(cx - r - 1); x <= cx + r + 1; x++) {
        const d = Math.hypot(x + 0.5 - cx, y + 0.5 - cy), k = Math.min(1, Math.max(0, r + 0.5 - d));
        if (k <= 0) continue;
        const i = ((y + h) % h) * w + ((x + w) % w);
        ch[i] += (v - ch[i]) * k;
      }
    }
  }
  function centre(ch, mean = 0.5, lo = 0.18, hi = 0.82) {
    let s = 0; for (let i = 0; i < ch.length; i++) s += ch[i];
    const shift = mean - s / ch.length;
    for (let i = 0; i < ch.length; i++) ch[i] = Math.min(hi, Math.max(lo, ch[i] + shift));
  }
  function macroChannel(w, h, rand) {
    const a = tileNoise(w, 4, rand), b = tileNoise(w, 8, rand), out = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) out[y * w + x] = 0.5 + (a(x, y) - 0.5) * 0.75 + (b(x, y) - 0.5) * 0.35;
    return out;
  }
  const PAINT = {
    asphalt(w, h) {
      const rand = rng(11), r = new Float32Array(w * h);
      const n1 = tileNoise(w, 16, rand), n2 = tileNoise(w, 64, rand);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++)
        r[y * w + x] = 0.5 + (n1(x, y) - 0.5) * 0.05 + (n2(x, y) - 0.5) * 0.045 + (rand() - 0.5) * 0.07;
      speckles(r, w, h, 950, rand, [0.35, 1.05], [0.56, 0.66]); // light aggregate
      speckles(r, w, h, 420, rand, [0.35, 0.9], [0.36, 0.43]);  // pores
      centre(r, 0.5, 0.3, 0.72);
      return { r, g: macroChannel(w, h, rand), b: r };
    },
    pavement(w, h) {
      const rand = rng(23), r = new Float32Array(w * h), b = new Float32Array(w * h), slab = w / 4;
      const tone = Array.from({ length: 16 }, () => (rand() - 0.5) * 0.04);
      const tilt = Array.from({ length: 16 }, () => [(rand() - 0.5) * 0.016, (rand() - 0.5) * 0.016]);
      const n = tileNoise(w, 64, rand);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const i = Math.floor(y / slab) * 4 + Math.floor(x / slab), u = x % slab, v = y % slab;
        // Distance from the pixel centre to the nearest joint line.
        const d = Math.min(u + 0.5, slab - u - 0.5, v + 0.5, slab - v - 0.5);
        let val = 0.5 + tone[i] + tilt[i][0] * (u / slab - 0.5) + tilt[i][1] * (v / slab - 0.5) + (n(x, y) - 0.5) * 0.03 + (rand() - 0.5) * 0.035;
        if (d < 1.1) val = 0.4 + (rand() - 0.5) * 0.02;           // joint, about 4 cm
        else if (d < 2.1) val -= 0.035;                          // its soft edge
        else if (d < 3.2 && (u < slab / 2) === (v < slab / 2)) val += 0.015; // worn arris
        r[y * w + x] = val;
      }
      speckles(r, w, h, 160, rand, [0.4, 0.8], [0.52, 0.56]);
      centre(r, 0.5, 0.25, 0.75);
      // Kerb faces: two 1.4 m stones across u; canvas top = top of the kerb.
      const stoneTone = [(rand() - 0.5) * 0.05, (rand() - 0.5) * 0.05];
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const s = Math.floor(x / (w / 2)), u = x % (w / 2), height = 1 - y / (h - 1);
        let val = 0.53 + stoneTone[s] + (rand() - 0.5) * 0.05 + (n(x, y * 0.25) - 0.5) * 0.04;
        if (height > 0.86) val += 0.13;                       // chamfer catching the light
        else if (height > 0.8) val -= 0.04;                   // its lower edge
        if (height < 0.16) val -= 0.09 * (1 - height / 0.16); // soiled foot
        if (u < 1 || u > w / 2 - 2) val = 0.33;               // section joint
        b[y * w + x] = val;
      }
      return { r, g: macroChannel(w, h, rand), b };
    },
    gravel(w, h) {
      const rand = rng(37), r = new Float32Array(w * h), n = tileNoise(w, 16, rand);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) r[y * w + x] = 0.47 + (n(x, y) - 0.5) * 0.08 + (rand() - 0.5) * 0.08;
      speckles(r, w, h, 520, rand, [0.6, 1.7], [0.36, 0.5]);
      speckles(r, w, h, 620, rand, [0.5, 1.5], [0.55, 0.72]);
      centre(r, 0.5, 0.26, 0.76);
      return { r, g: macroChannel(w, h, rand), b: r };
    },
    ballast(w, h) {
      const rand = rng(41), r = new Float32Array(w * h).fill(0.36);
      for (let i = 0; i < r.length; i++) r[i] += (rand() - 0.5) * 0.08;
      speckles(r, w, h, 700, rand, [1.0, 2.2], [0.42, 0.6]);
      speckles(r, w, h, 500, rand, [0.7, 1.5], [0.48, 0.64]);
      speckles(r, w, h, 260, rand, [0.6, 1.2], [0.3, 0.38]);
      centre(r, 0.5, 0.28, 0.7);
      return { r, g: macroChannel(w, h, rand), b: r };
    },
    sleeper(w, h) {
      const rand = rng(53), r = new Float32Array(w * h), n = tileNoise(w, 8, rand);
      // Grain runs along the sleeper (texture V, world Z of a crossing).
      const streak = Array.from({ length: w }, () => (rand() - 0.5) * 0.08);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++)
        r[y * w + x] = 0.5 + streak[x] + (n(x * 4, y * 0.5) - 0.5) * 0.08 + (rand() - 0.5) * 0.04;
      centre(r);
      return { r, g: new Float32Array(w * h).fill(0.5), b: r };
    },
    // One 1.4 m deck panel across the road (u) by the whole deck depth (v):
    // flangeway grooves where the rails cross (±0.76 m of 3.8 m), rubber edges.
    deck(w, h) {
      const rand = rng(67), r = new Float32Array(w * h), n = tileNoise(w, 8, rand);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const v = y / (h - 1), dv = Math.min(Math.abs(v - 0.3), Math.abs(v - 0.7));
        let val = 0.52 + (n(x, y / 4) - 0.5) * 0.06 + (rand() - 0.5) * 0.06;
        if (x < 1 || x > w - 2) val = 0.32;                      // panel joints
        if (dv < 0.018) val = 0.24; else if (dv < 0.026) val = 0.4; // flangeways
        if (v < 0.02 || v > 0.98) val = 0.3;                     // rubber edge strips
        r[y * w + x] = val;
      }
      // Anchor bolts near the panel corners and mid-depth.
      for (const [x, y] of [[6, 22], [w - 7, 22], [6, h - 23], [w - 7, h - 23], [6, h / 2], [w - 7, h / 2]]) {
        const at = [x / w, y / h, 0, 0]; let k = 0;
        speckles(r, w, h, 1, () => at[k++], [1.6, 1.6], [0.33, 0.33]);
      }
      return { r, g: macroChannel(w, h, rand), b: r };
    },
  };

  // Walls carry their pattern in B (vertical faces); R repeats it for tops.
  const wall = (w, h, rand, paint) => { const b = new Float32Array(w * h); paint(b); centre(b); return { r: b, g: macroChannel(w, h, rand), b }; };
  Object.assign(PAINT, {
    plaster(w, h) {
      const rand = rng(71), n1 = tileNoise(w, 8, rand), n2 = tileNoise(w, 32, rand), n3 = tileNoise(w, 96, rand);
      const drips = Array.from({ length: 7 }, () => [rand() * w, 0.2 + rand() * 0.5, 2 + rand() * 4]);
      return wall(w, h, rand, b => {
        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
          const height = 1 - y / (h - 1); // canvas top = top of the storey
          let v = 0.5 + (n1(x, y) - 0.5) * 0.06 + (n2(x, y) - 0.5) * 0.05 + (n3(x, y) - 0.5) * 0.05 + (rand() - 0.5) * 0.04;
          for (const [dx, len, wid] of drips) { const d = Math.abs(((x - dx + w * 1.5) % w) - w / 2); if (height > 1 - len && d < wid) v -= 0.025 * (1 - d / wid) * (height - (1 - len)) / len; }
          if (height > 0.955) v -= 0.07; else if (height > 0.93) v += 0.05; // storey cornice: shadow, lit edge
          b[y * w + x] = v;
        }
      });
    },
    panel(w, h) {
      // 4 x 2 panels of 2 m x 2.7 m with sealed seams and their own tone.
      const rand = rng(83), n = tileNoise(w, 64, rand), pw = w / 4, ph = h / 2;
      const tone = Array.from({ length: 8 }, () => (rand() - 0.5) * 0.05);
      return wall(w, h, rand, b => {
        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
          const i = Math.floor(y / ph) * 4 + Math.floor(x / pw), u = x % pw, v = y % ph;
          const d = Math.min(u + 0.5, pw - u - 0.5, v + 0.5, ph - v - 0.5);
          let val = 0.51 + tone[i] + (n(x, y) - 0.5) * 0.04 + (rand() - 0.5) * 0.03;
          if (d < 1.2) val = 0.33; else if (d < 2.4) val += (u < pw / 2 || v < ph / 2) ? 0.04 : -0.04;
          b[y * w + x] = val;
        }
      });
    },
    brick(w, h) {
      // Running bond: 8 bricks of 0.25 m per 2 m, 18 courses per 1.35 m.
      const rand = rng(89), rows = 18, cols = 8, bw = w / cols, bh = h / rows;
      const tone = Array.from({ length: rows * cols }, () => (rand() - 0.5) * 0.1);
      return wall(w, h, rand, b => {
        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
          const row = Math.floor(y / bh), shift = row % 2 ? bw / 2 : 0, xx = (x + shift) % w, col = Math.floor(xx / bw);
          const u = xx - col * bw, v = y - row * bh;
          let val = 0.48 + tone[row * cols + col] + (rand() - 0.5) * 0.06;
          if (u < 1.6 || v < 1.4) val = 0.66;               // mortar joints
          else if (v > bh - 1.6) val -= 0.05;              // lower edge shadow
          b[y * w + x] = val;
        }
      });
    },
    roofTile(w, h) {
      // Rows of overlapping tiles: 8 rows, staggered 16 tiles per row.
      const rand = rng(97), rows = 8, cols = 16, tw = w / cols, th = h / rows, n = tileNoise(w, 32, rand);
      const r = new Float32Array(w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const row = Math.floor(y / th), xx = (x + (row % 2) * tw / 2) % w, col = Math.floor(xx / tw), u = xx - col * tw, v = (y - row * th) / th;
        let val = 0.5 + (((row * 31 + col * 17) % 7) - 3) * 0.012 + (n(x, y) - 0.5) * 0.05 + (rand() - 0.5) * 0.03;
        val += 0.06 * Math.sin(Math.PI * u / tw) - 0.03;   // rounded tile
        if (v < 0.16) val -= 0.14 * (1 - v / 0.16);          // shadow under the row above
        if (u < 1) val -= 0.05;
        r[y * w + x] = val;
      }
      centre(r);
      return { r, g: macroChannel(w, h, rand), b: r };
    },
    roofFlat(w, h) {
      // Bitumen membrane in 1 m strips (top), concrete coping (sides).
      const rand = rng(101), n = tileNoise(w, 16, rand), r = new Float32Array(w * h), b = new Float32Array(w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        let val = 0.5 + (n(x, y) - 0.5) * 0.05 + (rand() - 0.5) * 0.025;
        if (x % (w / 4) < 1.5) val -= 0.05;
        r[y * w + x] = val;
        b[y * w + x] = 0.52 + (rand() - 0.5) * 0.06 + (n(x * 2, y) - 0.5) * 0.04 + (y < 3 ? 0.08 : 0) - (y > h - 4 ? 0.08 : 0);
      }
      speckles(r, w, h, 60, rand, [0.4, 0.8], [0.52, 0.56]);
      centre(r); centre(b);
      return { r, g: macroChannel(w, h, rand), b };
    },
    // A whole window: light frame and sill, cross mullion, glass that is
    // darker at the bottom with a soft diagonal reflection.
    window(w, h) {
      const r = new Float32Array(w * h), f = 7;
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const top = y / (h - 1), u = x / (w - 1);
        let val = 0.36 + 0.14 * (1 - top) + (Math.abs((u * 0.7 + (1 - top)) % 1 - 0.55) < 0.06 ? 0.08 : 0);
        const frame = x < f || x >= w - f || y < f || y >= h - f - 6 || Math.abs(x - w / 2) < 3 || Math.abs(y - h * 0.38) < 3;
        if (frame) val = 0.86;
        if (y >= h - 8) val = 0.96;                          // sill
        else if (y >= h - f - 6 && y < h - 8) val = 0.7;
        if (!frame && (x < f + 3 || y < f + 3)) val -= 0.08; // reveal shadow inside the frame
        r[y * w + x] = val;
      }
      return { r, g: new Float32Array(w * h).fill(0.5), b: r };
    },
    door(w, h) {
      const r = new Float32Array(w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        let val = 0.5;
        if (x < 4 || x >= w - 4 || y < 4) val = 0.7;                       // frame
        else if (y > 12 && y < 48 && x > 12 && x < w - 12) val = 0.38;    // glazed upper panel
        else if (y > 58 && y < h - 12 && x > 12 && x < w - 12) val = 0.45; // lower panel
        if (Math.abs(x - (w - 14)) < 3 && Math.abs(y - h * 0.55) < 6) val = 0.85; // handle
        r[y * w + x] = val;
      }
      return { r, g: new Float32Array(w * h).fill(0.5), b: r };
    },
    wood(w, h) {
      const rand = rng(103), n = tileNoise(w, 8, rand), streak = Array.from({ length: w }, () => (rand() - 0.5) * 0.08);
      const b = new Float32Array(w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++)
        b[y * w + x] = 0.5 + streak[x] + (n(x * 3, y * 0.4) - 0.5) * 0.1 + (rand() - 0.5) * 0.03;
      centre(b);
      return { r: b, g: macroChannel(w, h, rand), b };
    },
    metal(w, h) {
      // Ribbed sheet: 8 ribs per 1.2 m.
      const rand = rng(107), b = new Float32Array(w * h), rib = w / 8;
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const u = (x % rib) / rib;
        b[y * w + x] = 0.5 + 0.08 * Math.cos(u * Math.PI * 2) + (rand() - 0.5) * 0.03;
      }
      centre(b);
      return { r: b, g: macroChannel(w, h, rand), b };
    },
  });

  function texture(kind) {
    if (textures.has(kind)) return textures.get(kind);
    const k = KINDS[kind], w = k.w || k.size, h = k.h || k.size;
    const { r, g, b } = PAINT[kind](w, h);
    const canvas = document.createElement('canvas'); canvas.width = w; canvas.height = h;
    const ctx = canvas.getContext('2d'), img = ctx.createImageData(w, h);
    for (let i = 0; i < w * h; i++) {
      img.data[i * 4] = Math.round(r[i] * 255); img.data[i * 4 + 1] = Math.round(g[i] * 255);
      img.data[i * 4 + 2] = Math.round(b[i] * 255); img.data[i * 4 + 3] = 255;
    }
    ctx.putImageData(img, 0, 0);
    const map = new THREE.CanvasTexture(canvas);
    map.wrapS = map.wrapT = THREE.RepeatWrapping;
    map.anisotropy = Math.min(8, renderer ? renderer.capabilities.getMaxAnisotropy() : 4);
    map.name = 'road:' + kind;
    // Shared for the whole session: disposeSegment must leave it alone.
    map.userData = { pddRoadShared: true };
    textures.set(kind, map);
    return map;
  }

  // ---- One shader for every kind -----------------------------------------
  function roadPatch(shader) {
    const k = KINDS[this.userData.pddKind] || KINDS.asphalt;
    shader.uniforms.pddMacro = { value: k.macro };
    shader.uniforms.pddMacroScale = { value: k.macroScale };
    shader.vertexShader = shader.vertexShader
      .replace('#include <uv_pars_vertex>', '#include <uv_pars_vertex>\nattribute float pddSide;\nvarying float vPddSide;')
      .replace('#include <uv_vertex>', '#include <uv_vertex>\nvPddSide = pddSide;');
    shader.fragmentShader = shader.fragmentShader
      .replace('#include <map_pars_fragment>', '#include <map_pars_fragment>\nvarying float vPddSide;\nuniform float pddMacro;\nuniform float pddMacroScale;')
      .replace('#include <map_fragment>', [
        '#ifdef USE_MAP',
        '  vec4 pddTexel = texture2D( map, vUv );',
        '  float pddSideFace = step( 0.5, vPddSide );',
        '  float pddDetail = mix( pddTexel.r, pddTexel.b, pddSideFace );',
        '  float pddLarge = mix( texture2D( map, vUv * pddMacroScale + vec2( 0.31, 0.17 ) ).g, 0.5, pddSideFace );',
        '  diffuseColor.rgb *= pddDetail * 2.0 * ( 1.0 + ( pddLarge * 2.0 - 1.0 ) * pddMacro );',
        '#endif'].join('\n'));
  }
  function decorate(material, kind) {
    if (material.userData.pddKind === kind && material.onBeforeCompile === roadPatch && material.map) return;
    material.userData.pddKind = kind;
    material.map = texture(kind);
    material.onBeforeCompile = roadPatch;
    material.needsUpdate = true;
  }

  // ---- Road frames --------------------------------------------------------
  // L = [a b; c d] · (x, z) + (e, f): world X/Z to texture metres.
  function makeFrame(a = 1, b = 0, c = 0, d = 1, e = 0, f = 0) {
    const frame = { id: nextFrame++, a, b, c, d, e, f };
    wrap(frame); frames.set(frame.id, frame);
    return frame;
  }
  function wrap(fr) { fr.e = ((fr.e % WRAP) + WRAP) % WRAP; fr.f = ((fr.f % WRAP) + WRAP) % WRAP; }
  // The frame of an object's own axes (its local X/Z are the texture axes).
  function frameOfObject(obj) {
    obj.updateWorldMatrix(true, false);
    const inv = obj.matrixWorld.clone().invert().elements;
    return makeFrame(inv[0], inv[8], inv[2], inv[10], inv[12], inv[14]);
  }
  function defaultFrame() { return frames.get(1) || (nextFrame = 1, makeFrame()); }
  function frameById(id) { return frames.get(id) || defaultFrame(); }
  // World rebase W' = T W: every frame becomes F ∘ T⁻¹.
  function rebase(matrix) {
    const t = matrix.clone().invert().elements;
    const ta = t[0], tb = t[8], tc = t[2], td = t[10], te = t[12], tf = t[14];
    frames.forEach(fr => {
      const { a, b, c, d, e, f } = fr;
      fr.a = a * ta + b * tc; fr.b = a * tb + b * td; fr.e = a * te + b * tf + e;
      fr.c = c * ta + d * tc; fr.d = c * tb + d * td; fr.f = c * te + d * tf + f;
      wrap(fr);
    });
  }
  // Mark a new road segment: its texture continues the road it was built from.
  function adopt(root, from) {
    root.userData.pddRoot = true;
    if (root.userData.pddFrameId === undefined) root.userData.pddFrameId = frameIdOf(from);
    dirty = true;
  }
  function frameIdOf(obj) {
    for (let o = obj; o; o = o.parent) if (o.userData.pddFrameId !== undefined && frames.has(o.userData.pddFrameId)) return o.userData.pddFrameId;
    return defaultFrame().id;
  }
  // A road root turned by a multiple of 90° in its frame keeps that frame
  // (square paving looks the same); any other angle gets the road's own axes.
  function resolveFrame(root, inherited) {
    let frame = frames.get(root.userData.pddFrameId) || inherited;
    if (root.userData.pddRoot && !root.userData.pddFrameChecked) {
      root.updateWorldMatrix(true, false);
      const m = root.matrixWorld.elements;
      // Direction of the root's local +X in texture axes.
      const ux = frame.a * m[0] + frame.b * m[2], uz = frame.c * m[0] + frame.d * m[2];
      const angle = Math.atan2(uz, ux);
      if (Math.abs(Math.sin(2 * angle)) > 1e-3) frame = frameOfObject(root);
      root.userData.pddFrameId = frame.id; root.userData.pddFrameChecked = true;
    }
    return frame;
  }

  // ---- Classification and UV bake ----------------------------------------
  function kindOf(mesh) {
    const m = mesh.material;
    if (!m || Array.isArray(m) || !m.isMeshLambertMaterial) return null;
    if (m.userData.pddKind) return m.userData.pddKind;
    const u = mesh.userData;
    if (m.map || u.roadMarking || u.actor || u.dirtSurface || u.puddle) return null;
    const hex = m.color.getHex();
    if (u.roadDeck || hex === 0x9C9B94) return 'deck';
    if (u.surface === 'road' || m.userData.asphalt || hex === ASPHALT) return 'asphalt';
    if (u.surface === 'sidewalk' || m.userData.seasonal === 'sidewalk' || SIDEWALKS.has(hex)) return 'pavement';
    if (u.roadShoulder || hex === 0xB4AD92) return 'gravel';
    if (u.ballast || hex === 0x8C867C) return 'ballast';
    if (u.sleepers || hex === 0x5E4B3B) return 'sleeper';
    return null;
  }
  const P = new THREE.Vector3(), N = new THREE.Vector3(), normalMatrix = new THREE.Matrix3();
  function bake(mesh, kind, frame) {
    let geometry = mesh.geometry;
    if (!geometry || !geometry.attributes.position) return false;
    // A geometry shared with another, differently placed mesh gets a copy.
    if (geometry.userData.pddBakedFor && geometry.userData.pddBakedFor !== mesh.uuid && !mesh.userData.pddSkinned) {
      geometry = mesh.geometry = geometry.clone();
    }
    const k = KINDS[kind], pos = geometry.attributes.position, nor = geometry.attributes.normal;
    if (k.object || k.geometry) return false; // baked by skinObject at creation
    mesh.updateWorldMatrix(true, false);
    const M = mesh.matrixWorld; normalMatrix.getNormalMatrix(M);
    const uv = new Float32Array(pos.count * 2), side = new Float32Array(pos.count);
    const joints = k.joints && geometry.type === 'BoxGeometry';
    for (let i = 0; i < pos.count; i++) {
      if (k.local) {
        // Deck panels follow the plane itself: 1.4 m across, full depth in V.
        const p = geometry.parameters || {};
        uv[2 * i] = pos.getX(i) / k.panel; uv[2 * i + 1] = p.height ? pos.getY(i) / p.height + 0.5 : pos.getY(i);
        continue;
      }
      P.fromBufferAttribute(pos, i).applyMatrix4(M);
      const lx = frame.a * P.x + frame.b * P.z + frame.e, lz = frame.c * P.x + frame.d * P.z + frame.f;
      if (nor) N.fromBufferAttribute(nor, i).applyMatrix3(normalMatrix).normalize();
      if (!nor || Math.abs(N.y) >= 0.6) {
        uv[2 * i] = lx / k.period; uv[2 * i + 1] = lz / k.period;
      } else {
        // Vertical face: along the face in the road frame, height in V.
        const nx = frame.a * N.x + frame.b * N.z, nz = frame.c * N.x + frame.d * N.z, len = Math.hypot(nx, nz) || 1;
        const along = joints ? (lx * -nz + lz * nx) / len : 0.37 * (k.side || k.period);
        uv[2 * i] = along / (k.side || k.period);
        uv[2 * i + 1] = 0.02 + 0.96 * Math.min(1, Math.max(0, P.y / KERB));
        side[i] = 1;
      }
    }
    geometry.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
    geometry.setAttribute('pddSide', new THREE.BufferAttribute(side, 1));
    geometry.userData.pddBakedFor = mesh.uuid;
    mesh.userData.pddSkinned = kind;
    mesh.userData.pddFrame = k.local ? 0 : frame.id;
    return true;
  }

  // Bake everything new under the road roots. Runs right before a render,
  // only after a road change, so builders may place their parts freely first.
  function sweep(force = false) {
    if (!hooks || (!dirty && !force)) return 0;
    dirty = false;
    let baked = 0;
    const used = new Set([defaultFrame().id]);
    const visit = (obj, frame) => {
      if (obj.userData.actor || obj.userData.sceneryObject) return;
      if (obj.userData.pddRoot || obj.userData.pddFrameId !== undefined) frame = resolveFrame(obj, frame);
      used.add(frame.id);
      if (obj.isMesh) {
        const kind = kindOf(obj);
        if (kind) {
          decorate(obj.material, kind);
          if (!obj.userData.pddSkinned || !obj.geometry.attributes.pddSide) { if (bake(obj, kind, frame)) baked++; }
        }
      }
      for (const child of obj.children) visit(child, frame);
    };
    for (const root of hooks.roots()) {
      // Groups without a road of their own (road events) continue the road
      // they were placed on, as of their first bake.
      if (root.userData.pddFrameId === undefined) root.userData.pddFrameId = frameIdOf(hooks.lineage() || null);
      visit(root, frameById(root.userData.pddFrameId));
    }
    const lineage = hooks.lineage();
    if (lineage) used.add(frameIdOf(lineage));
    frames.forEach((_, id) => { if (!used.has(id)) frames.delete(id); });
    return baked;
  }

  // Bake an object-mapped kind into a mesh's geometry. Box-like geometry:
  // vertical faces get (metres along the face, metres up) in B, tops their
  // plan position in R. Geometry kinds scale the existing uv (su, sv).
  // opts.u0 / opts.v0 shift the pattern (panel seams between windows).
  function skinObject(mesh, kind, opts = {}) {
    const k = KINDS[kind], g = mesh.geometry;
    if (!g || !g.attributes.position) return mesh;
    decorate(mesh.material, kind);
    const pos = g.attributes.position, nor = g.attributes.normal, count = pos.count;
    const uv = new Float32Array(count * 2), side = new Float32Array(count);
    if (k.geometry) {
      const src = g.attributes.uv;
      for (let i = 0; i < count; i++) { uv[2 * i] = (src ? src.getX(i) : 0) * (opts.su || 1); uv[2 * i + 1] = (src ? src.getY(i) : 0) * (opts.sv || 1); }
    } else {
      if (!g.boundingBox) g.computeBoundingBox();
      const min = g.boundingBox.min, u0 = opts.u0 || 0, v0 = opts.v0 || 0;
      for (let i = 0; i < count; i++) {
        const x = pos.getX(i), y = pos.getY(i), z = pos.getZ(i);
        const ny = nor ? nor.getY(i) : 1, nx = nor ? nor.getX(i) : 0;
        if (Math.abs(ny) > 0.6) { uv[2 * i] = (x - min.x) / k.u; uv[2 * i + 1] = (z - min.z) / k.u; continue; }
        const along = Math.abs(nx) > 0.5 ? z - min.z : x - min.x;
        uv[2 * i] = (along + u0) / k.u; uv[2 * i + 1] = (y - min.y + v0) / k.v; side[i] = 1;
      }
    }
    g.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
    g.setAttribute('pddSide', new THREE.BufferAttribute(side, 1));
    mesh.userData.pddSkinned = kind;
    return mesh;
  }

  window.PDD_ROADS = {
    kinds: KINDS,
    // hooks: { roots(): live road groups, lineage(): the road being driven }
    attach(r, h) {
      renderer = r; hooks = h;
      if (r.render.pddRoads) return;
      const render = r.render.bind(r);
      r.render = (s, c) => { sweep(); return render(s, c); };
      r.render.pddRoads = true;
    },
    adopt, rebase, sweep, invalidate() { dirty = true; }, skinObject,
    reset() { frames = new Map(); nextFrame = 1; makeFrame(); dirty = true; },
    texture, decorate, kindOf,
    frame: id => { const f = frames.get(id); return f && { ...f }; },
    frameCount: () => frames.size,
    sharedTextures: () => [...textures.values()],
  };
  window.PDD_ROADS.reset();
})();
