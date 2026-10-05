// Installed only by the Flutter web host. Native FlutterChannel is unchanged.
(() => {
  if (new URLSearchParams(location.search).get('flutterWeb') !== '1' || parent === window) return;
  window.FlutterChannel = { postMessage(payload) {
    parent.postMessage(JSON.stringify({ bridge: 'pdd-game', type: 'event', payload }), location.origin);
  } };
  for (const type of ['keydown', 'keyup']) window.addEventListener(type, event => {
    if (event.ctrlKey || event.metaKey || event.altKey || !['ArrowUp','ArrowDown','ArrowLeft','ArrowRight','KeyW','KeyA','KeyS','KeyD','Space'].includes(event.code)) return;
    event.preventDefault();
    parent.postMessage(JSON.stringify({ bridge: 'pdd-game', type: 'key', key: event.code, down: type === 'keydown', repeat: event.repeat }), location.origin);
  });
  window.addEventListener('blur', () => parent.postMessage(JSON.stringify({ bridge: 'pdd-game', type: 'blur' }), location.origin));
  window.addEventListener('message' , event => {
    if (event.source !== parent || event.origin !== location.origin || typeof event.data !== 'string') return;
    let data;
    try { data = JSON.parse(event.data); } catch (_) { return; }
    if (data.bridge !== 'pdd-game' || typeof data.code !== 'string') return;
    try {
      const value = (0, eval)(data.code);
      parent.postMessage(JSON.stringify({ bridge: 'pdd-game', type: 'result', id: data.id, value: value ?? '' }), location.origin);
    } catch (_) {
      parent.postMessage(JSON.stringify({ bridge: 'pdd-game', type: 'result', id: data.id, error: true }), location.origin);
    }
  });
})();
