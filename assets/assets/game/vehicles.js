// Shared procedural vehicle models: the garage thumbnails use these same meshes.
(function () {
  const surfaces = window.PDD_VEHICLE_MATERIALS;
  // Camera-facing halo: readable in daylight without expensive bloom/lights.
  function addGlow(lamp, color, size = 1.15) {
    const glow = new THREE.Sprite(new THREE.SpriteMaterial({
      map: surfaces.glowMap(), color, transparent: true,
      blending: THREE.AdditiveBlending, depthWrite: false, fog: false,
    }));
    glow.scale.set(size, size, 1);
    glow.userData.signalGlow = true;
    lamp.add(glow);
    return glow;
  }
  // Indicators blink front AND rear: the rear lamp rides on the front one, so
  // every turn signal and the hazard lights show from behind too.
  function addRearBlinker(front, length) {
    const rear = new THREE.Mesh(front.geometry, front.material);
    rear.position.set(0, 0, -(length / 2 + front.position.z + .06));
    front.add(rear);
    addGlow(rear, 0xFFB329, 1.25);
  }
  // Six passenger cars (any paint colour) plus the premium-only gold wedge.
  const specs = {
    hatch: { color: 0xED4621, width: 1.72, length: 3.5, height: 1.4, cabin: 2.0, cabinZ: -0.3 },
    sedan: { color: 0x317ED4, width: 1.8, length: 4.2, height: 1.35, cabin: 2.05, cabinZ: -0.1 },
    coupe: { color: 0x2B2F36, width: 1.8, length: 4.3, height: 1.25, cabin: 1.7, cabinZ: -0.25 },
    wagon: { color: 0x6E8E6A, width: 1.8, length: 4.5, height: 1.45, cabin: 2.9, cabinZ: -0.45 },
    suv: { color: 0x4D7768, width: 1.9, length: 4.25, height: 1.85, cabin: 2.7, cabinZ: -0.35 },
    pickup: { color: 0xD7AA60, width: 1.9, length: 4.6, height: 1.65, cabin: 1.65, cabinZ: 0.55 },
    cyber: { color: 0xD4AF37, width: 2.0, length: 5.0, height: 1.75, cabin: 2.4, cabinZ: 0.1, premium: true },
  };
  // Paint colours a car can come in (hex). Names are shown in the garage.
  const paints = {
    red: 0xED4621, blue: 0x317ED4, green: 0x4D7768, sand: 0xD7AA60, white: 0xF2F3F5, black: 0x2B2F36,
    silver: 0xB9C0C7, orange: 0xF08A24, purple: 0x7A5BC6, teal: 0x2FA3A0, yellow: 0xE8C547, wine: 0x8B1E2D, gold: 0xD4AF37,
  };
  // Hand edits from the game lab's model workshop (model-edits.js):
  // PDD_MODEL_EDITS[modelId] = { spec, scale: [x, y, z], colors: { 'hex': 'hex' },
  // parts: { meshIndex: { color, hidden } } }. Mesh indices follow the build order.
  function hex(value) { return parseInt(String(value).replace('#', ''), 16); }
  function applyModelEdits(modelId, root) {
    const e = (window.PDD_MODEL_EDITS || {})[modelId];
    if (!e || !root) return root;
    const remap = Object.fromEntries(Object.entries(e.colors || {}).map(([a, b]) => [hex(a), hex(b)]));
    const meshes = [];
    root.traverse(o => { if (o.isMesh) meshes.push(o); });
    meshes.forEach((m, i) => {
      const part = (e.parts || {})[i];
      const own = () => { if (!m.userData.ownMaterial) { m.material = m.material.clone(); m.userData.ownMaterial = true; } return m.material; };
      if (m.material?.color && remap[m.material.color.getHex()] !== undefined) own().color.setHex(remap[m.material.color.getHex()]);
      const attr = m.geometry?.attributes?.color;
      if (attr && Object.keys(remap).length) {
        const c = new THREE.Color();
        for (let k = 0; k < attr.count; k++) {
          c.setRGB(attr.getX(k), attr.getY(k), attr.getZ(k));
          const to = remap[c.getHex()];
          if (to !== undefined) { c.setHex(to); attr.setXYZ(k, c.r, c.g, c.b); }
        }
        attr.needsUpdate = true;
      }
      if (part?.color && m.material?.color) {
        own().color.setHex(hex(part.color));
        if (m.material.vertexColors) m.material.vertexColors = false, m.material.needsUpdate = true;
      }
      if (part?.hidden) m.visible = false;
    });
    if (e.scale) root.scale.multiply(new THREE.Vector3(...e.scale));
    return root;
  }
  function create(id = 'hatch', paint) {
    const edited = (window.PDD_MODEL_EDITS || {})['vehicle:' + id]?.spec;
    const s = { ...(specs[id] || specs.hatch), ...(edited || {}) }, car = new THREE.Group();
    return applyModelEdits('vehicle:' + (specs[id] ? id : 'hatch'), build(id, s, car, paint));
  }
  // --- Car bodies -------------------------------------------------------
  // Every car is modelled from its side profile like a real body: the lower
  // body (bumpers, bonnet, doors, boot) and the greenhouse (pillars and roof)
  // are extruded outlines with rounded edges; glass is inset into the
  // pillars; wheels sit in dark arches. Z is forward, X is the car's left.
  // Per model: lower-body outline, greenhouse, wheel size and extras.
  const bodies = {
    hatch: { r: 0.33, base: 0.64, hood: 0.8, belt: 0.9, tail: 0.92, cabF: 0.12, roofF: -0.06, roofR: -0.40, cabR: -0.47, roofH: 1.40 },
    sedan: { r: 0.33, base: 0.6, hood: 0.8, belt: 0.88, tail: 0.9, cabF: 0.12, roofF: -0.02, roofR: -0.2, cabR: -0.29, roofH: 1.35 },
    coupe: { r: 0.34, base: 0.6, hood: 0.72, belt: 0.8, tail: 0.84, cabF: 0.07, roofF: -0.08, roofR: -0.2, cabR: -0.4, roofH: 1.25 },
    wagon: { r: 0.33, base: 0.62, hood: 0.8, belt: 0.9, tail: 0.94, cabF: 0.13, roofF: 0.0, roofR: -0.46, cabR: -0.48, roofH: 1.45 },
    suv: { r: 0.42, base: 0.62, hood: 1.16, belt: 1.24, tail: 1.26, cabF: 0.12, roofF: 0.02, roofR: -0.45, cabR: -0.47, roofH: 1.85, ground: 0.46 },
    pickup: { r: 0.42, base: 0.64, hood: 1.1, belt: 1.16, tail: 1.1, cabF: 0.22, roofF: 0.12, roofR: -0.05, cabR: -0.08, roofH: 1.72, ground: 0.46, bedFront: -0.1 },
  };
  function paintOf(s, paint) {
    return paint === undefined || paint === null ? s.color
      : (typeof paint === 'string' ? (paints[paint] ?? parseInt(paint.replace('#', ''), 16)) : paint);
  }
  // An outline in (z, y) extruded across the car (X), centred, rounded.
  function extrudeSide(points, width, mat, bevel = 0.05) {
    const shape = new THREE.Shape();
    shape.moveTo(points[0][0], points[0][1]);
    points.slice(1).forEach(p => shape.lineTo(p[0], p[1]));
    shape.closePath();
    const depth = Math.max(0.01, width - 2 * bevel);
    const g = new THREE.ExtrudeGeometry(shape, { depth, bevelEnabled: bevel > 0, bevelThickness: bevel, bevelSize: bevel,
      bevelSegments: 2, curveSegments: 4 });
    g.rotateY(-Math.PI / 2);            // shape x -> car z, extrusion -> -x
    g.translate(depth / 2, 0, 0);       // centred across the car
    const m = new THREE.Mesh(g, mat); m.castShadow = true; m.receiveShadow = true;
    return m;
  }
  // A quad from four 3D points (glass on sloped screens).
  function quad(a, b, c, d, mat) {
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.Float32BufferAttribute([...a, ...b, ...c, ...a, ...c, ...d], 3));
    g.computeVertexNormals();
    return new THREE.Mesh(g, mat);
  }
  // Shrink a polygon towards its centroid by roughly `inset`.
  function inset(points, amount) {
    const cx = points.reduce((t, p) => t + p[0], 0) / points.length;
    const cy = points.reduce((t, p) => t + p[1], 0) / points.length;
    return points.map(([x, y]) => {
      const dx = cx - x, dy = cy - y, len = Math.hypot(dx, dy) || 1;
      return [x + dx / len * amount, y + dy / len * amount];
    });
  }
  function wheel(car, r, width, x, z, mats, spokes = 5) {
    const axle = new THREE.Group(); axle.position.set(x, r, z); car.add(axle);
    const tyre = new THREE.Mesh(new THREE.CylinderGeometry(r, r, width, 22), mats.tyre);
    surfaces.tyreUV(tyre.geometry);
    tyre.geometry.rotateZ(Math.PI / 2); tyre.castShadow = true; axle.add(tyre);
    const side = Math.sign(x);
    const rim = new THREE.Mesh(new THREE.CylinderGeometry(r * 0.64, r * 0.64, 0.04, 20), mats.rim);
    rim.geometry.rotateZ(Math.PI / 2); rim.position.x = side * (width / 2 + 0.005); tyre.add(rim);
    const hub = new THREE.Mesh(new THREE.CylinderGeometry(r * 0.2, r * 0.2, 0.05, 10), mats.dark);
    hub.geometry.rotateZ(Math.PI / 2); hub.position.x = side * (width / 2 + 0.015); tyre.add(hub);
    for (let i = 0; i < spokes; i++) {
      const a = i / spokes * Math.PI * 2;
      const hole = new THREE.Mesh(new THREE.BoxGeometry(0.02, r * 0.26, r * 0.14), mats.dark);
      hole.position.set(side * (width / 2 + 0.012), Math.cos(a) * r * 0.42, Math.sin(a) * r * 0.42);
      hole.rotation.x = -a; tyre.add(hole);
    }
    return { axle, tyre };
  }

  function build(id, s, car, paint) {
    const L = s.length, W = s.width;
    const mats = {
      paint: surfaces.material('paint', paintOf(s, paint)),
      glass: surfaces.material('glass', 0x8497A3),
      dark: new THREE.MeshLambertMaterial({ color: 0x23282D }),
      trim: new THREE.MeshLambertMaterial({ color: 0x3A4148 }),
      tyre: surfaces.material('rubber', 0x22272C),
      metal: surfaces.material('metal', 0xC4CBD0),
      rim: surfaces.material('rim', 0xC4CBD0),
      head: surfaces.material('lens', 0xFFF3CC),
      plate: surfaces.material('plate', 0xF4F4F0),
      grille: surfaces.material('grille', 0x23282D),
    };
    if (id === 'cyber') return buildCyber(car, s, mats);
    const b = bodies[id] || bodies.hatch;
    const add = m => { car.add(m); return m; };
    const box = (w, h, d, x, y, z, mat) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat); m.position.set(x, y, z); m.castShadow = true; return add(m); };
    const zf = L / 2, zr = -L / 2;                    // bumpers
    const ground = b.ground || 0.3;                    // body bottom (sill)
    const H = s.height;
    const cabF = b.cabF * L, roofF = b.roofF * L, roofR = b.roofR * L, cabR = b.cabR * L;
    const bed = id === 'pickup' ? b.bedFront * L : null;

    // Lower body: front bumper, bonnet line, belt, boot / tailgate, rear.
    const lower = bed === null ? [
      [zr + 0.04, ground], [zf - 0.04, ground],
      [zf, ground + 0.16], [zf - 0.02, b.base], [zf - 0.3, b.hood], [cabF + 0.05, b.belt],
      [cabR - 0.02, b.belt], [zr + 0.22, b.tail], [zr + 0.02, b.tail - 0.1], [zr, ground + 0.16],
    ] : [
      [zr + 0.04, ground], [zf - 0.04, ground],
      [zf, ground + 0.16], [zf - 0.02, b.base], [zf - 0.32, b.hood], [cabF + 0.05, b.belt],
      [cabR, b.belt], [bed, 0.86], [zr + 0.04, 0.86], [zr, 0.8], [zr, ground + 0.16],
    ];
    const panels = surfaces.material('paint', paintOf(s, paint), surfaces.panelMap(id, s, b));
    const lowerBody = extrudeSide(lower, W, panels, 0.06);
    surfaces.panelUV(lowerBody.geometry, L, ground, b.belt, W);
    add(lowerBody);

    // Greenhouse in body colour; the glass is inset into it (pillars stay).
    const green = [[cabR, b.belt - 0.02], [cabF, b.belt - 0.02], [roofF, H], [roofR, H]];
    const Wg = W * 0.86;
    add(extrudeSide(green, Wg, mats.paint, 0.05));
    // Side windows, split by the B-pillar.
    const mid = (Math.max(cabR, roofR) + Math.min(cabF, roofF)) / 2 - 0.05;
    const winTop = H - 0.07, winBot = b.belt + 0.04;
    const frontWin = inset([[mid + 0.05, winBot], [cabF - 0.02, winBot], [roofF, winTop], [mid + 0.05, winTop]], 0.05);
    const rearWin = inset([[cabR + 0.02, winBot], [mid - 0.05, winBot], [mid - 0.05, winTop], [roofR, winTop]], 0.05);
    for (const sx of [-1, 1]) for (const pts of [frontWin, rearWin]) {
      const shape = new THREE.Shape(); shape.moveTo(pts[0][0], pts[0][1]); pts.slice(1).forEach(p => shape.lineTo(p[0], p[1])); shape.closePath();
      const g = new THREE.ShapeGeometry(shape);
      // Shape (z, y) onto the plane x = ±(Wg/2 + 0.004), facing outwards.
      const pos = g.attributes.position;
      for (let i = 0; i < pos.count; i++) { const zz = pos.getX(i), yy = pos.getY(i); pos.setXYZ(i, sx * (Wg / 2 + 0.015), yy, zz); }
      g.computeVertexNormals();
      surfaces.glassUV(g);
      add(new THREE.Mesh(g, mats.glass));
    }
    // Windscreen and rear screen on the sloped faces, just proud of them.
    const gw = Wg / 2 - 0.08;
    const slope = (za, ya, zb, yb, lift) => {
      const n = new THREE.Vector3(0, zb - za, -(yb - ya)).normalize().multiplyScalar(lift);
      return (x, z, y) => [x + n.x, y + n.y, z + n.z];
    };
    const ws = slope(cabF, b.belt, roofF, H, -0.065); // proud of the rounded edge (bevel 0.05)
    const windscreen = quad(ws(-gw, cabF - 0.06, b.belt + 0.05), ws(gw, cabF - 0.06, b.belt + 0.05), ws(gw, roofF + 0.05, H - 0.05), ws(-gw, roofF + 0.05, H - 0.05), mats.glass);
    surfaces.glassUV(windscreen.geometry, 'x', 'y'); add(windscreen);
    const rs = slope(roofR, H, cabR, b.belt, -0.065);
    const rearScreen = quad(rs(-gw, roofR - 0.05, H - 0.05), rs(gw, roofR - 0.05, H - 0.05), rs(gw, cabR + 0.05, b.belt + 0.05), rs(-gw, cabR + 0.05, b.belt + 0.05), mats.glass);
    surfaces.glassUV(rearScreen.geometry, 'x', 'y'); add(rearScreen);

    // Wheel arches: dark half discs on both flanks, then the wheels.
    const r = b.r, wb = L * 0.31, tw = W / 2 - 0.1; // tyre face 2 cm outside the arch
    const zFrontAxle = id === 'pickup' ? L * 0.33 : wb, zRearAxle = -wb;
    for (const z of [zFrontAxle, zRearAxle]) for (const sx of [-1, 1]) {
      const arch = new THREE.Mesh(new THREE.CircleGeometry(r + 0.08, 20, 0, Math.PI), mats.dark);
      arch.rotation.y = sx * Math.PI / 2; arch.position.set(sx * (W / 2 + 0.02), r, z); add(arch);
    }
    car.userData.wheels = []; car.userData.frontAxles = [];
    for (const z of [zFrontAxle, zRearAxle]) for (const sx of [-1, 1]) {
      const w = wheel(car, r, 0.24, sx * tw, z, mats);
      car.userData.wheels.push(w.tyre);
      if (z > 0) car.userData.frontAxles.push(w.axle);
    }

    // Front: grille, headlights, bumper, plate. Rear: lamps, bumper, plate.
    const faceY = (ground + 0.16 + b.base) / 2;
    box(W * 0.46, 0.14, 0.04, 0, faceY, zf + 0.065, mats.grille);
    box(W * 0.42, 0.025, 0.045, 0, faceY + 0.02, zf + 0.065, mats.metal);
    box(W + 0.06, 0.14, 0.16, 0, ground + 0.08, zf - 0.04, mats.trim);
    box(W + 0.06, 0.14, 0.16, 0, ground + 0.08, zr + 0.04, mats.trim);
    box(0.46, 0.1, 0.02, 0, ground + 0.1, zf + 0.065, mats.plate);
    box(0.46, 0.1, 0.02, 0, (b.tail + ground) / 2, zr - 0.065, mats.plate);
    for (const sx of [-1, 1]) {
      box(0.3, 0.1, 0.05, sx * W * 0.34, faceY + 0.06, zf + 0.065, mats.head);
      // Mirrors on the doors at the A-pillar; a door seam and a handle.
      const mirror = box(0.08, 0.1, 0.18, sx * (W / 2 + 0.07), b.belt + 0.1, cabF - 0.18, mats.paint);
      mirror.rotation.y = sx * 0.15;
      box(0.03, 0.03, 0.12, sx * (W / 2 + 0.02), b.belt - 0.12, mid + 0.35, mats.metal);
      const rearHandle = box(0.03, 0.03, 0.12, sx * (W / 2 + 0.02), b.belt - 0.12, mid - 0.35, mats.metal);
      rearHandle.visible = id !== 'coupe' && id !== 'pickup';
    }
    car.brakeLights = [];
    for (const sx of [-1, 1]) {
      const y = (bed === null ? b.tail : 0.8) - 0.16;
      car.brakeLights.push(box(0.28, 0.12, 0.04, sx * W * 0.35, y, zr - 0.065, surfaces.material('lens', 0xD33D38)));
    }

    // Model extras.
    if (id === 'hatch') box(Wg - 0.1, 0.05, 0.28, 0, H + 0.02, roofR - 0.08, mats.paint);            // roof spoiler
    if (id === 'coupe') box(W * 0.8, 0.04, 0.26, 0, b.tail + 0.08, zr + 0.2, mats.dark);               // boot-lid spoiler
    if (id === 'wagon' || id === 'suv') for (const sx of [-1, 1]) box(0.06, 0.06, (roofF - roofR) * 0.9, sx * (Wg / 2 - 0.08), H + 0.06, (roofF + roofR) / 2, mats.dark); // roof rails
    if (id === 'suv') {
      const spare = new THREE.Mesh(new THREE.CylinderGeometry(0.34, 0.34, 0.2, 18), mats.tyre);
      surfaces.tyreUV(spare.geometry);
      spare.geometry.rotateX(Math.PI / 2); spare.position.set(0, (b.tail + ground) / 2 + 0.2, zr - 0.12); add(spare);
      const cover = new THREE.Mesh(new THREE.CylinderGeometry(0.26, 0.26, 0.21, 18), mats.paint);
      cover.geometry.rotateX(Math.PI / 2); cover.position.copy(spare.position); add(cover);
      box(W * 0.5, 0.06, 0.3, 0, ground - 0.02, zf - 0.12, mats.metal);                             // skid plate
    }
    if (id === 'pickup') {
      // An open load bed: floor, sides and tailgate in body colour.
      const bedLen = bed - zr - 0.06, bedMid = (bed + zr) / 2;
      box(W - 0.2, 0.04, bedLen, 0, 0.88, bedMid, mats.dark);
      for (const sx of [-1, 1]) box(0.1, 0.3, bedLen, sx * (W / 2 - 0.05), 1.01, bedMid, mats.paint);
      box(W - 0.02, 0.3, 0.08, 0, 1.01, zr + 0.04, mats.paint);
      box(W - 0.02, 0.3, 0.06, 0, 1.01, bed - 0.02, mats.paint);
      box(0.5, 0.06, 0.02, 0, 1.08, zr - 0.005, mats.trim);                                            // tailgate handle
    }

    // Indicators (front, with repeaters at the rear) — the game drives them.
    car.blinkerL = box(0.12, 0.09, 0.05, W / 2 - 0.08, faceY + 0.06, zf + 0.065, surfaces.material('lens', 0xFFAE25));
    addRearBlinker(car.blinkerL, L + 0.01);
    car.blinkerR = car.blinkerL.clone(); car.blinkerR.position.x *= -1; car.add(car.blinkerR);
    car.blinkerL.visible = car.blinkerR.visible = false;
    addGlow(car.blinkerL, 0xFFB329, 1.25);
    addGlow(car.blinkerR, 0xFFB329, 1.25);

    car.userData.vehicle = id;
    car.userData.halfWidth = W / 2;
    car.userData.halfLength = L / 2;
    car.userData.height = H;
    car.userData.lampSpec = { front: { x: W * 0.34, y: faceY + 0.06, z: zf }, rear: { x: W * 0.35, y: (bed === null ? b.tail : 0.8) - 0.16, z: zr } };
    return car;
  }

  // Premium: an angular stainless wedge (the Cybertruck idea) — one sloped
  // roof line from the nose to the peak and straight down to the tail,
  // a glass band, a full-width light bar front and rear, square arches and
  // a covered load bed.
  function buildCyber(car, s, mats) {
    const L = s.length, W = s.width, H = s.height;
    const zf = L / 2, zr = -L / 2, ground = 0.42, peakZ = L * 0.06;
    const add = m => { car.add(m); return m; };
    const box = (w, h, d, x, y, z, mat) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat); m.position.set(x, y, z); m.castShadow = true; return add(m); };
    const noseY = 0.9, tailY = 1.12;
    const panels = surfaces.material('paint', mats.paint.color.getHex(), surfaces.panelMap('cyber', s,
      { ground, belt: 1.08, cabF: .28, cabR: -.2, roofF: .06, roofR: -.12 }));
    const lowerBody = extrudeSide([[zr, ground], [zf, ground], [zf, noseY], [peakZ, H], [zr, tailY]], W, panels, .02);
    surfaces.panelUV(lowerBody.geometry, L, ground, H, W); add(lowerBody);
    // Glass band: an inset triangle-ish window along the roof line.
    const topAt = z => z >= peakZ ? H - (z - peakZ) / (zf - peakZ) * (H - noseY) : H - (peakZ - z) / (peakZ - zr) * (H - tailY);
    const zA = L * 0.28, zC = -L * 0.2, band = 1.08;
    const win = [[zC, band], [zA, band], [zA - 0.05, topAt(zA) - 0.07], [peakZ, H - 0.07], [zC, topAt(zC) - 0.07]];
    for (const sx of [-1, 1]) {
      const shape = new THREE.Shape(); shape.moveTo(win[0][0], win[0][1]); win.slice(1).forEach(p => shape.lineTo(p[0], p[1])); shape.closePath();
      const g = new THREE.ShapeGeometry(shape); const pos = g.attributes.position;
      for (let i = 0; i < pos.count; i++) pos.setXYZ(i, sx * (W / 2 + 0.015), pos.getY(i), pos.getX(i));
      g.computeVertexNormals(); surfaces.glassUV(g); add(new THREE.Mesh(g, mats.glass));
    }
    // Windscreen on the front slope.
    const slopeN = new THREE.Vector3(0, zf - peakZ, H - noseY).normalize().multiplyScalar(0.035);
    const P = (x, z) => [x + slopeN.x, topAt(z) + slopeN.y, z + slopeN.z];
    const gw = W / 2 - 0.14;
    const windscreen = quad(P(-gw, zA), P(gw, zA), P(gw, peakZ + 0.1), P(-gw, peakZ + 0.1), mats.glass);
    surfaces.glassUV(windscreen.geometry, 'x', 'y'); add(windscreen);
    // Light bars and a vault-like tonneau line.
    box(W - 0.06, 0.05, 0.04, 0, noseY - 0.04, zf + 0.03, mats.head);
    car.brakeLights = [box(W - 0.06, 0.05, 0.04, 0, tailY - 0.05, zr - 0.03, surfaces.material('lens', 0xD33D38))];
    box(W - 0.2, 0.012, 0.012, 0, (tailY + topAt(zC)) / 2 + 0.02, zC - 0.6, mats.trim);
    box(W + 0.04, 0.16, 0.2, 0, ground + 0.06, zf - 0.08, mats.trim);
    box(W + 0.04, 0.16, 0.2, 0, ground + 0.06, zr + 0.08, mats.trim);
    // Square, angular wheel arches and big wheels.
    const r = 0.44, wb = L * 0.32;
    for (const z of [wb, -wb]) for (const sx of [-1, 1]) {
      const shape = new THREE.Shape();
      shape.moveTo(-r - 0.16, 0); shape.lineTo(-r - 0.02, r + 0.16); shape.lineTo(r + 0.02, r + 0.16); shape.lineTo(r + 0.16, 0); shape.closePath();
      const g = new THREE.ShapeGeometry(shape); const pos = g.attributes.position;
      for (let i = 0; i < pos.count; i++) pos.setXYZ(i, sx * (W / 2 + 0.02), r + pos.getY(i) - 0.02, z + pos.getX(i));
      g.computeVertexNormals(); add(new THREE.Mesh(g, mats.dark));
    }
    car.userData.wheels = []; car.userData.frontAxles = [];
    for (const z of [wb, -wb]) for (const sx of [-1, 1]) {
      const w = wheel(car, r, 0.28, sx * (W / 2 - 0.11), z, mats, 6);
      car.userData.wheels.push(w.tyre);
      if (z > 0) car.userData.frontAxles.push(w.axle);
    }
    car.blinkerL = box(0.14, 0.06, 0.05, W / 2 - 0.1, noseY - 0.12, zf + 0.01, surfaces.material('lens', 0xFFAE25));
    addRearBlinker(car.blinkerL, L + 0.02);
    car.blinkerR = car.blinkerL.clone(); car.blinkerR.position.x *= -1; car.add(car.blinkerR);
    car.blinkerL.visible = car.blinkerR.visible = false;
    addGlow(car.blinkerL, 0xFFB329, 1.25); addGlow(car.blinkerR, 0xFFB329, 1.25);
    car.userData.vehicle = 'cyber';
    car.userData.halfWidth = W / 2; car.userData.halfLength = L / 2; car.userData.height = H;
    car.userData.lampSpec = { front: { x: W * 0.4, y: noseY - 0.04, z: zf }, rear: { x: W * 0.4, y: tailY - 0.05, z: zr } };
    return car;
  }
  window.PDD_VEHICLES = { specs, paints, create, addGlow, applyModelEdits };
})();
