// Small, deterministic surface atlases shared by every vehicle and garage view.
// Painted details keep the existing silhouettes, physics and mesh edit indices.
(function () {
  const cache = new Map();
  function noise(ctx, width, height, seed, strength = 8) {
    let n = seed;
    const pixels = ctx.getImageData(0, 0, width, height);
    for (let i = 0; i < pixels.data.length; i += 4) {
      n = (Math.imul(n, 1664525) + 1013904223) >>> 0;
      const delta = (n >>> 24) / 255 * strength - strength / 2;
      for (let k = 0; k < 3; k++) pixels.data[i + k] += delta;
    }
    ctx.putImageData(pixels, 0, 0);
  }
  function texture(key, draw, width = 128, height = width) {
    if (cache.has(key)) return cache.get(key);
    const canvas = document.createElement('canvas'); canvas.width = width; canvas.height = height;
    const ctx = canvas.getContext('2d'); ctx.fillStyle = '#ffffff'; ctx.fillRect(0, 0, width, height);
    draw(ctx, width, height);
    const map = new THREE.CanvasTexture(canvas);
    map.anisotropy = 4;
    map.userData = { pddVehicleShared: true };
    map.name = 'vehicle:' + key;
    cache.set(key, map);
    return map;
  }
  const grain = () => texture('paint-grain', (c, w, h) => { c.fillStyle = '#eeeeee'; c.fillRect(0, 0, w, h); noise(c, w, h, 19, 5); });
  const metal = () => texture('brushed-metal', (c, w, h) => {
    const g = c.createLinearGradient(0, 0, w, h); g.addColorStop(0, '#eeeeee'); g.addColorStop(.42, '#ffffff'); g.addColorStop(1, '#dddddd');
    c.fillStyle = g; c.fillRect(0, 0, w, h);
    c.strokeStyle = 'rgba(80,90,100,.055)'; c.lineWidth = 1;
    for (let y = 2; y < h; y += 3) { c.beginPath(); c.moveTo(0, y); c.lineTo(w, y); c.stroke(); }
  });
  const glass = () => texture('glass', (c, w, h) => {
    const g = c.createLinearGradient(0, 0, w * .15, h);
    g.addColorStop(0, '#b4c8d5'); g.addColorStop(.42, '#708895'); g.addColorStop(1, '#33434d');
    c.fillStyle = g; c.fillRect(0, 0, w, h);
    c.fillStyle = 'rgba(235,246,255,.16)'; c.beginPath(); c.moveTo(w * .1, 0); c.lineTo(w * .3, 0); c.lineTo(w * .87, h); c.lineTo(w * .74, h); c.fill();
    c.fillStyle = 'rgba(235,246,255,.08)'; c.beginPath(); c.moveTo(w * .39, 0); c.lineTo(w * .43, 0); c.lineTo(w, h * .94); c.lineTo(w, h * .85); c.fill();
    c.strokeStyle = 'rgba(12,22,29,.5)'; c.lineWidth = 5; c.strokeRect(2, 2, w - 4, h - 4);
  }, 256);
  const lens = () => texture('lamp-lens', (c, w, h) => {
    const g = c.createLinearGradient(0, 0, 0, h); g.addColorStop(0, '#ffffff'); g.addColorStop(1, '#c9cdd0');
    c.fillStyle = g; c.fillRect(0, 0, w, h);
    c.strokeStyle = 'rgba(70,80,90,.14)'; c.lineWidth = 1;
    for (let x = 4; x < w; x += 8) { c.beginPath(); c.moveTo(x, 0); c.lineTo(x, h); c.stroke(); }
    for (let y = 4; y < h; y += 8) { c.beginPath(); c.moveTo(0, y); c.lineTo(w, y); c.stroke(); }
    c.fillStyle = 'rgba(255,255,255,.4)'; c.fillRect(3, 3, w - 6, 4);
  }, 128, 64);
  const tyre = () => texture('tyre-atlas', (c, w, h) => {
    c.fillStyle = '#e0e0e0'; c.fillRect(0, 0, w, h); noise(c, w, h, 47, 5);
    // The upper half is the rolling surface, the lower half is a sidewall.
    c.strokeStyle = '#a4a7a9'; c.lineWidth = 4;
    for (let x = -12; x < w + 12; x += 16) {
      c.beginPath(); c.moveTo(x, 0); c.lineTo(x + 9, 48); c.lineTo(x, 64); c.lineTo(x + 9, 80); c.lineTo(x, 128); c.stroke();
    }
    c.strokeStyle = '#acb0b2'; c.lineWidth = 3;
    for (const y of [12, 45, 83, 116]) { c.beginPath(); c.moveTo(0, y); c.lineTo(w, y); c.stroke(); }
    c.fillStyle = '#dddddd'; c.fillRect(0, 128, w, 128);
    for (const r of [56, 48, 39]) { c.strokeStyle = r === 48 ? '#bfc2c4' : '#a6aaae'; c.lineWidth = r === 48 ? 2 : 3; c.beginPath(); c.ellipse(128, 192, r * 2, r, 0, 0, Math.PI * 2); c.stroke(); }
  }, 256);
  const rim = () => texture('alloy-rim', (c, w, h) => {
    c.fillStyle = '#9ca8b0'; c.fillRect(0, 0, w, h);
    const g = c.createRadialGradient(64, 64, 3, 64, 64, 62); g.addColorStop(0, '#ffffff'); g.addColorStop(.45, '#c2ccd3'); g.addColorStop(.85, '#f3f6f8'); g.addColorStop(1, '#9aa4ac');
    c.fillStyle = g; c.beginPath(); c.arc(64, 64, 62, 0, Math.PI * 2); c.fill();
    for (let i = 0; i < 5; i++) { const a = i * Math.PI * 2 / 5;
      c.save(); c.translate(64, 64); c.rotate(a); c.fillStyle = '#5b6872'; c.beginPath(); c.moveTo(20, -7); c.lineTo(47, -9); c.lineTo(45, 8); c.lineTo(22, 5); c.fill(); c.restore();
      c.fillStyle = '#59636a'; c.beginPath(); c.arc(64 + Math.cos(a) * 13, 64 + Math.sin(a) * 13, 2.2, 0, Math.PI * 2); c.fill();
    }
    c.strokeStyle = '#f5f7f8'; c.lineWidth = 2; c.beginPath(); c.arc(64, 64, 59, 0, Math.PI * 2); c.stroke();
  });
  const grille = () => texture('grille', (c, w, h) => {
    c.fillStyle = '#bbbbbb'; c.fillRect(0, 0, w, h); c.fillStyle = '#5d6266';
    for (let y = 4; y < h; y += 12) c.fillRect(0, y, w, 5);
    c.fillStyle = '#d9dfe2'; for (let x = 6; x < w; x += 24) c.fillRect(x, 0, 2, h);
  });
  const plate = () => texture('plate', (c, w, h) => {
    c.strokeStyle = '#9ca7ae'; c.lineWidth = 2; c.strokeRect(2, 2, w - 4, h - 4);
    c.fillStyle = '#6c777d'; for (const x of [8, w - 8]) { c.beginPath(); c.arc(x, h / 2, 2, 0, Math.PI * 2); c.fill(); }
    // Neutral fasteners only: country markings and invented registration text
    // do not belong in shared vehicle art.
  }, 128, 32);
  const steelRim = () => texture('steel-wheel', (c, w, h) => {
    c.fillStyle = '#a8b2b9'; c.fillRect(0, 0, w, h);
    const g = c.createRadialGradient(64, 64, 4, 64, 64, 62);
    g.addColorStop(0, '#dbe2e6'); g.addColorStop(.58, '#c0cbd2'); g.addColorStop(.9, '#eff3f5'); g.addColorStop(1, '#8f9da6');
    c.fillStyle = g; c.beginPath(); c.arc(64, 64, 62, 0, Math.PI * 2); c.fill();
    for (let i = 0; i < 8; i++) { const a = i / 8 * Math.PI * 2;
      c.fillStyle = '#6d7b86'; c.beginPath(); c.arc(64 + Math.cos(a) * 43, 64 + Math.sin(a) * 43, 4, 0, Math.PI * 2); c.fill();
      c.fillStyle = '#5a6771'; c.beginPath(); c.arc(64 + Math.cos(a) * 20, 64 + Math.sin(a) * 20, 2.2, 0, Math.PI * 2); c.fill();
    }
    c.strokeStyle = '#83929b'; c.lineWidth = 2; c.beginPath(); c.arc(64, 64, 29, 0, Math.PI * 2); c.stroke();
  });
  const rubberRound = () => texture('round-tyre', (c, w, h) => {
    c.fillStyle = '#dedede'; c.fillRect(0, 0, w, h); noise(c, w, h, 71, 4);
    c.strokeStyle = '#b1b4b7'; c.lineWidth = 3;
    for (let x = -8; x < w; x += 16) { c.beginPath(); c.moveTo(x, 0); c.lineTo(x + 7, h / 2); c.lineTo(x, h); c.stroke(); }
    c.strokeStyle = '#bfc2c4'; c.lineWidth = 2;
    for (const y of [h * .28, h * .72]) { c.beginPath(); c.moveTo(0, y); c.lineTo(w, y); c.stroke(); }
  }, 256, 64);
  const rubberFarm = () => texture('farm-tyre', (c, w, h) => {
    c.drawImage(tyre().image, 0, 0); c.fillStyle = '#d9dbdd'; c.fillRect(0, 0, w, h / 2);
    c.strokeStyle = '#92999e'; c.lineWidth = 10;
    for (let x = -12; x < w + 24; x += 32) { c.beginPath(); c.moveTo(x, 4); c.lineTo(x + 22, 58); c.moveTo(x + 22, 70); c.lineTo(x, 124); c.stroke(); }
  }, 256);
  const leather = () => texture('seat-vinyl', (c, w, h) => {
    c.fillStyle = '#e5e5e5'; c.fillRect(0, 0, w, h); noise(c, w, h, 81, 11);
    c.strokeStyle = 'rgba(80,80,80,.13)'; c.setLineDash([2, 3]); c.strokeRect(5, 5, w - 10, h - 10);
  });
  const wood = () => texture('cart-timber', (c, w, h) => {
    c.fillStyle = '#eee9df'; c.fillRect(0, 0, w, h);
    c.strokeStyle = 'rgba(88,66,42,.13)'; c.lineWidth = 1;
    for (let y = 4; y < h; y += 7) { c.beginPath(); for (let x = 0; x <= w; x += 4) { const yy = y + Math.sin(x / 25 + y) * 2; x ? c.lineTo(x, yy) : c.moveTo(x, yy); } c.stroke(); }
  }, 256, 128);
  const fabric = () => texture('woven-sack', (c, w, h) => {
    c.fillStyle = '#ece8de'; c.fillRect(0, 0, w, h); c.fillStyle = 'rgba(74,65,52,.12)';
    for (let y = 0; y < h; y += 4) for (let x = y % 8; x < w; x += 8) c.fillRect(x, y, 2, 2);
  });
  const tankMap = () => texture('tank-shell', (c, w, h) => {
    const g = c.createLinearGradient(0, 0, w, 0);
    g.addColorStop(0, '#e2e6e8'); g.addColorStop(.22, '#f6f8f9');
    g.addColorStop(.62, '#ffffff'); g.addColorStop(1, '#e2e6e8');
    c.fillStyle = g; c.fillRect(0, 0, w, h); noise(c, w, h, 93, 3);
    c.strokeStyle = 'rgba(70,84,94,.22)'; c.lineWidth = 1;
    // Welds on the cylinder shell; no invented cargo labels or country text.
    for (const y of [h * .17, h * .5, h * .83]) {
      c.beginPath(); c.moveTo(0, y); c.lineTo(w, y); c.stroke();
      c.strokeStyle = 'rgba(255,255,255,.4)'; c.beginPath(); c.moveTo(0, y + 2); c.lineTo(w, y + 2); c.stroke();
      c.strokeStyle = 'rgba(70,84,94,.22)';
    }
  }, 256, 128);
  // Five face tiles: side, nose, tail, roof and underside. One texture and
  // one material per mesh keep commercial vehicles inexpensive to draw.
  function transportMap(kind) {
    return texture('transport:' + kind, (c, w, h) => {
      const tw = w / 3, th = h / 2;
      for (let face = 0; face < 5; face++) {
        c.save(); c.translate(face % 3 * tw, Math.floor(face / 3) * th);
        c.beginPath(); c.rect(0, 0, tw, th); c.clip();
        c.fillStyle = '#ffffff'; c.fillRect(0, 0, tw, th);
        const stroke = (alpha = .2) => { c.strokeStyle = `rgba(35,46,55,${alpha})`; c.lineWidth = 1.25; };
        if (kind.endsWith('windows')) {
          const n = face === 0 ? (kind.startsWith('tram') ? 7 : 6) : 1;
          c.fillStyle = '#263640'; c.fillRect(0, 0, tw, th);
          for (let i = 0; i < n; i++) {
            const x = 4 + i * (tw - 8) / n, ww = (tw - 8) / n - 3;
            const g = c.createLinearGradient(x, 4, x + ww * .12, th - 4);
            g.addColorStop(0, '#b4c8d5'); g.addColorStop(.42, '#708895'); g.addColorStop(1, '#33434d');
            c.fillStyle = g; c.fillRect(x, 4, ww, th - 8);
            c.fillStyle = 'rgba(235,246,255,.14)'; c.beginPath(); c.moveTo(x + ww * .2, 4); c.lineTo(x + ww * .38, 4); c.lineTo(x + ww * .86, th - 4); c.lineTo(x + ww * .71, th - 4); c.fill();
          }
        } else if (kind === 'van-profile') {
          c.fillStyle = '#eeeeee'; c.fillRect(0,0,tw,th);
          stroke(.25);
          if (face === 0) {
            const X=z=>(z/4.9+.5)*tw,Y=y=>th-(y-.35)/1.75*th;
            const path=points=>{c.beginPath();points.forEach(([z,y],i)=>i?c.lineTo(X(z),Y(y)):c.moveTo(X(z),Y(y)));c.stroke();};
            path([[.38,1.94],[.38,.60],[1.75,.60],[1.76,1.30]]);
            path([[-1.72,.60],[-1.72,1.94],[.20,1.94],[.20,.60],[-1.72,.60]]);
            path([[-2.25,.57],[2.25,.57]]);
            c.fillStyle='#a7afb4';for(const z of [.58,-.10])c.fillRect(X(z),Y(1.21),tw*.055,2.5);
          } else if (face === 2) {
            c.strokeRect(8,8,tw-16,th-16);c.beginPath();c.moveTo(tw/2,8);c.lineTo(tw/2,th-8);c.stroke();
            c.fillStyle='#a7afb4';for(const x of [.43,.54])c.fillRect(tw*x,th*.53,3,12);
          } else if (face === 3) {stroke(.12);c.strokeRect(12,12,tw-24,th-24);}
        } else if (kind === 'cargo' || kind === 'wagon') {
          if (face === 0 || face === 1) {
            for (let x = 7; x < tw - 5; x += 9) { c.fillStyle = '#d4dadd'; c.fillRect(x, 5, 2, th - 10); c.fillStyle = '#f4f6f7'; c.fillRect(x + 2, 5, 2, th - 10); }
          }
          stroke(); c.strokeRect(5, 5, tw - 10, th - 10);
          if (face === 2) { c.beginPath(); c.moveTo(tw / 2, 5); c.lineTo(tw / 2, th - 5); c.stroke();
            for (const x of [tw * .27, tw * .73]) { c.fillStyle = '#a7b1b8'; c.fillRect(x, 10, 2, th - 20); for (const y of [th * .28, th * .72]) c.fillRect(x - 3, y, 8, 3); }
          }
        } else if (kind === 'bogie') {
          c.fillStyle = '#9ca5aa'; c.fillRect(0, 0, tw, th); c.fillStyle = '#626d75';
          if (face === 0) for (const x of [tw * .24, tw * .76]) { c.beginPath(); c.ellipse(x, th * .62, tw * .16, th * .35, 0, 0, Math.PI * 2); c.fill(); }
          c.fillStyle = '#c2cbd0'; c.fillRect(6, th * .25, tw - 12, th * .07);
        } else {
          stroke();
          if (face === 0) {
            if (kind === 'bus-body' || kind === 'tram-body') {
              for (let x = 6; x < tw - 20; x += 28) c.strokeRect(x, th * .47, 25, th * .35);
              c.beginPath(); c.moveTo(5, th * .9); c.lineTo(tw - 5, th * .9); c.stroke();
            } else { c.strokeRect(10, 8, tw - 20, th - 16); c.fillStyle = '#aeb9c0'; c.fillRect(tw * .2, th * .45, 10, 3); }
            if (kind === 'tractor' || kind === 'locomotive') { c.fillStyle = '#b3bdc3'; for (let x = tw * .35; x < tw * .88; x += 6) c.fillRect(x, th * .4, 2, th * .33); }
          } else if (face === 1 && kind !== 'roof') {
            c.strokeRect(tw * .13, th * .6, tw * .74, th * .23);
            c.fillStyle = '#a7b0b6'; for (let y = th * .65; y < th * .8; y += 6) c.fillRect(tw * .18, y, tw * .64, 2);
          } else if (face === 2) {
            c.strokeRect(8, 8, tw - 16, th - 16);
            if (kind === 'van') { c.beginPath(); c.moveTo(tw / 2, 8); c.lineTo(tw / 2, th - 8); c.stroke();
              c.fillStyle = '#a8b3ba'; for (const x of [tw * .42, tw * .55]) c.fillRect(x, th * .5, 3, 13);
            }
          } else if (face === 3) {
            c.strokeRect(10, 10, tw - 20, th - 20);
            if (kind === 'hvac' || kind === 'locomotive') { c.fillStyle = '#b0b9bf'; for (let y = 20; y < th - 18; y += 8) c.fillRect(20, y, tw - 40, 3); }
          }
        }
        c.restore();
      }
    }, 512, 256);
  }
  function transportBoxUV(geometry) {
    const uv = geometry.attributes.uv, seen = new Set();
    const faces = [0, 0, 3, 4, 1, 2];
    for (const group of geometry.groups) {
      const face = faces[group.materialIndex];
      for (let n = group.start; n < group.start + group.count; n++) {
        const i = geometry.index ? geometry.index.getX(n) : n;
        if (seen.has(i)) continue; seen.add(i);
        uv.setXY(i, (face % 3 + .025 + uv.getX(i) * .95) / 3,
          (1 - Math.floor(face / 3) + .025 + uv.getY(i) * .95) / 2);
      }
    }
    uv.needsUpdate = true;
  }
  function transportProfileUV(geometry, width, length, bottom, top) {
    const p=geometry.attributes.position,n=geometry.attributes.normal,uv=new Float32Array(p.count*2);
    for(let i=0;i<p.count;i++) {
      const side=Math.abs(n.getX(i))>.8,roof=!side&&n.getY(i)>.45;
      const face=side?0:roof?3:n.getZ(i)>0?1:2;
      const u=side?p.getZ(i)/length+.5:p.getX(i)/width+.5;
      const v=roof?p.getZ(i)/length+.5:(p.getY(i)-bottom)/(top-bottom);
      uv[i*2]=(face%3+.025+THREE.MathUtils.clamp(u,0,1)*.95)/3;
      uv[i*2+1]=(1-Math.floor(face/3)+.025+THREE.MathUtils.clamp(v,0,1)*.95)/2;
    }
    geometry.setAttribute('uv',new THREE.BufferAttribute(uv,2));
  }
  function material(role, color, map) {
    const maps = { paint: grain, glass, rubber: tyre, rubberFarm, rubberRound, metal, rim, steelRim, grille, plate, lens, leather, wood, fabric };
    const textureMap = map || maps[role]?.();
    const matte = role.startsWith('rubber') || ['grille', 'plate', 'leather', 'wood', 'fabric'].includes(role);
    const metallic = ['metal', 'rim', 'steelRim'].includes(role);
    const m = matte
      ? new THREE.MeshLambertMaterial({ color, map: textureMap })
      : role === 'lens' ? new THREE.MeshBasicMaterial({ color, map: textureMap })
      : new THREE.MeshPhongMaterial({ color, map: textureMap,
        specular: role === 'glass' ? 0x70828D : metallic ? 0x88939C : 0x090A0B,
        shininess: role === 'glass' ? 75 : metallic ? 55 : 36 });
    if (role === 'glass') m.side = THREE.DoubleSide;
    m.userData.vehicleSurface = role;
    return m;
  }
  function panelMap(id, s, b) {
    return texture('panels:' + id, (c, w, h) => {
      const lowerY = b.ground || .3, upperY = id === 'cyber' ? s.height : b.belt;
      const X = z => (z / s.length + .5) * w / 2, Y = y => h - (y - lowerY) / (upperY - lowerY) * h;
      const cabF = b.cabF * s.length, cabR = b.cabR * s.length;
      const mid = (Math.max(cabR, b.roofR * s.length) + Math.min(cabF, b.roofF * s.length)) / 2 - .05;
      const seams = id === 'coupe' || id === 'pickup' ? [cabR + .12, cabF - .17] : [cabR + .12, mid, cabF - .17];
      c.strokeStyle = 'rgba(29,39,46,.24)'; c.lineWidth = 1.8;
      for (const z of seams) { c.beginPath(); c.moveTo(X(z), Y(b.belt - .018)); c.lineTo(X(z), Y(lowerY + .065)); c.stroke(); }
      // A stamped belt and sill, with the same paint colour under the atlas.
      c.strokeStyle = 'rgba(29,39,46,.12)'; c.lineWidth = 1.4;
      for (const y of [lowerY + .09, b.belt - .11]) { c.beginPath(); c.moveTo(X(-s.length * .43), Y(y)); c.lineTo(X(s.length * .42), Y(y)); c.stroke(); }
      c.strokeStyle = 'rgba(29,39,46,.2)'; c.lineWidth = 1.5;
      // The right half is a plan view: panel joints on bonnet and boot.
      const topX = x => w * (.75 + x / s.width / 2), topZ = z => h * (.5 - z / s.length);
      for (const [from, to] of [[cabF + .08, s.length * .43], [-s.length * .43, cabR - .08]]) {
        if (to <= from || id === 'pickup' && from < 0) continue;
        c.beginPath(); c.moveTo(topX(-s.width * .36), topZ(from)); c.lineTo(topX(-s.width * .34), topZ(to));
        c.lineTo(topX(s.width * .34), topZ(to)); c.lineTo(topX(s.width * .36), topZ(from)); c.stroke();
      }
      // The clear corner is sampled by vertical faces and rounded edges.
      c.clearRect(w - 6, h - 6, 6, 6); c.fillStyle = '#ffffff'; c.fillRect(w - 6, h - 6, 6, 6);
    }, 512, 256);
  }
  function panelUV(geometry, length, fromY, toY, width) {
    const p = geometry.attributes.position, normal = geometry.attributes.normal;
    const uv = new Float32Array(p.count * 2);
    for (let i = 0; i < p.count; i++) {
      const side = Math.abs(normal.getX(i)) > .99;
      const top = !side && normal.getY(i) > .45;
      uv[2 * i] = side ? (p.getZ(i) / length + .5) / 2 : top ? .75 + p.getX(i) / width / 2 : .995;
      uv[2 * i + 1] = side ? (p.getY(i) - fromY) / (toY - fromY) : top ? p.getZ(i) / length + .5 : .005;
    }
    geometry.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
  }
  function glassUV(geometry, uAxis = 'z', vAxis = 'y') {
    const p = geometry.attributes.position, get = axis => axis === 'z' ? i => p.getZ(i) : axis === 'y' ? i => p.getY(i) : i => p.getX(i);
    const U = get(uAxis), V = get(vAxis); let u0 = Infinity, u1 = -Infinity, v0 = Infinity, v1 = -Infinity;
    for (let i = 0; i < p.count; i++) { u0 = Math.min(u0, U(i)); u1 = Math.max(u1, U(i)); v0 = Math.min(v0, V(i)); v1 = Math.max(v1, V(i)); }
    const uv = new Float32Array(p.count * 2);
    for (let i = 0; i < p.count; i++) { uv[2 * i] = (U(i) - u0) / (u1 - u0 || 1); uv[2 * i + 1] = (V(i) - v0) / (v1 - v0 || 1); }
    geometry.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
  }
  function tyreUV(geometry) {
    const uv = geometry.attributes.uv, seen = new Set();
    for (const group of geometry.groups) for (let n = group.start; n < group.start + group.count; n++) {
      const i = geometry.index ? geometry.index.getX(n) : n;
      if (seen.has(i)) continue; seen.add(i);
      uv.setY(i, uv.getY(i) * .5 + (group.materialIndex === 0 ? .5 : 0));
    }
    uv.needsUpdate = true;
  }
  function glowMap() {
    return texture('signal-halo', (c, w, h) => {
      c.clearRect(0, 0, w, h); const g = c.createRadialGradient(w / 2, h / 2, 0, w / 2, h / 2, w / 2);
      g.addColorStop(0, 'rgba(255,255,255,1)'); g.addColorStop(.15, 'rgba(255,255,255,.9)');
      g.addColorStop(.38, 'rgba(255,255,255,.35)'); g.addColorStop(1, 'rgba(255,255,255,0)');
      c.fillStyle = g; c.fillRect(0, 0, w, h);
    }, 64);
  }
  window.PDD_VEHICLE_MATERIALS = { material, panelMap, panelUV, glassUV, tyreUV, glowMap, transportMap, transportBoxUV, transportProfileUV, tankMap,
    cacheInfo: () => [...cache.values()].map(t => ({ name: t.name, width: t.image.width, height: t.image.height })) };
})();
