# Proof Map

One connected picture of the verifier-soundness proof.

<iframe id="proofmap-frame" src="proof-map-embed.html" title="Interactive proof structure map"
  loading="lazy"
  style="width:100%; height:760px; border:1px solid rgba(128,140,170,.35); border-radius:12px; margin:0.6rem 0;">
</iframe>

[Open the full-width map ↗](proof-map-embed.html) &nbsp;·&nbsp; New to the terms? See the [**Glossary**](glossary.md).

<script>
// Theme sync: forward the book's active theme (mdBook toggle) to the embedded map iframe.
(function () {
  var f = document.getElementById('proofmap-frame');
  if (!f) return;
  function theme() { return /coal|navy|ayu/.test(document.documentElement.className) ? 'dark' : 'light'; }
  function send() { try { f.contentWindow.postMessage({ iwtheme: theme() }, '*'); } catch (e) {} }
  f.addEventListener('load', send);
  new MutationObserver(send).observe(document.documentElement, { attributes: true, attributeFilter: ['class'] });
})();
</script>
