(async () => {
  const SELECTOR = "#one-up > div.content.ze-active > div.container > img";
  const CHANGE_TIMEOUT_MS = 2000;
  const STABLE_MS = 800;
  const MAX_SETTLE_MS = 10000;
  const POLL_MS = 100;

  const pressRight = () => {
    const opts = { key: "ArrowRight", code: "ArrowRight", keyCode: 39, which: 39, bubbles: true, cancelable: true };
    document.dispatchEvent(new KeyboardEvent("keydown", opts));
    document.dispatchEvent(new KeyboardEvent("keyup", opts));
  };

  const waitForSrcChange = async (oldSrc) => {
    const start = Date.now();
    while (Date.now() - start < CHANGE_TIMEOUT_MS) {
      const el = document.querySelector(SELECTOR);
      if (el && el.src && el.src !== oldSrc) return el;
      await new Promise(r => setTimeout(r, POLL_MS));
    }
    return null;
  };

  const waitForHighRes = async () => {
    const start = Date.now();
    let lastSrc = null;
    let stableSince = Date.now();
    while (Date.now() - start < MAX_SETTLE_MS) {
      const el = document.querySelector(SELECTOR);
      if (!el) { await new Promise(r => setTimeout(r, POLL_MS)); continue; }
      const src = el.src;
      const loaded = el.complete && el.naturalWidth > 0;
      if (src !== lastSrc) {
        lastSrc = src;
        stableSince = Date.now();
      }
      if (loaded && Date.now() - stableSince >= STABLE_MS) return el;
      await new Promise(r => setTimeout(r, POLL_MS));
    }
    return document.querySelector(SELECTOR);
  };

  const downloadCurrent = async () => {
    const img = document.querySelector(SELECTOR);
    if (!img || !img.src) return null;
    const src = img.src;
    const filename = src.split("/").pop().split("?")[0] || "image";
    try {
      const res = await fetch(src, { credentials: "include" });
      const blob = await res.blob();
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = filename;
      document.body.appendChild(a);
      a.click();
      a.remove();
      URL.revokeObjectURL(url);
      console.log(`downloaded: ${filename} (${img.naturalWidth}x${img.naturalHeight})`);
    } catch (e) {
      console.error("download failed:", filename, e);
    }
    return src;
  };

  let count = 0;
  await waitForHighRes();
  while (true) {
    const src = await downloadCurrent();
    if (!src) { console.log("no image, stopping"); break; }
    count++;
    pressRight();
    const changed = await waitForSrcChange(src);
    if (!changed) { console.log(`src didn't change — stopping. downloaded ${count}.`); break; }
    await waitForHighRes();
  }
})();
