# Proof Map

One connected picture of the verifier-soundness proof.

<style>
.proofmap-shell {
  position: relative;
  left: 50%;
  width: min(1680px, calc(100vw - 12rem));
  transform: translateX(-50%);
  margin: 0.6rem 0;
}
html.sidebar-visible .proofmap-shell {
  width: min(1680px, calc(100vw - var(--sidebar-width, 300px) - 12rem));
}
.proofmap-shell iframe {
  display: block;
  width: 100%;
  height: min(1250px, calc(100vh - 6rem));
  min-height: 700px;
  border: 1px solid rgba(128,140,170,.35);
  border-radius: 8px;
}
@media (max-width: 1080px) {
  .proofmap-shell { width: calc(100vw - 1.5rem); }
}
</style>

<div class="proofmap-shell">
  <iframe id="proofmap-frame" src="proof-map-embed.html" title="Interactive proof structure map"
    loading="lazy">
  </iframe>
</div>

Watch the [**Proof Journey**](proof-journey.md). &nbsp;·&nbsp; New to the terms? See the [**Definitions**](definitions.md).

<script>
// Theme sync: forward the book's active theme (mdBook toggle) to the embedded map iframe.
(function () {
  var f = document.getElementById('proofmap-frame');
  if (!f) return;
  function theme() { return /coal|navy|ayu/.test(document.documentElement.className) ? 'dark' : 'light'; }
  function send() { try { f.contentWindow.postMessage({ iwtheme: theme() }, '*'); } catch (e) {} }
  f.addEventListener('load', send);
  new MutationObserver(send).observe(document.documentElement, { attributes: true, attributeFilter: ['class'] });
  window.addEventListener('message', function (event) {
    if (event.source !== f.contentWindow || !event.data || !event.data.iwmapHeight) return;
    f.style.height = (event.data.iwmapHeight + 2) + 'px';
  });
})();
</script>
