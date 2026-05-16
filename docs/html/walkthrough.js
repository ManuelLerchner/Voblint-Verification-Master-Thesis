/**
 * Shared init for docs/html walkthrough pages:
 * - Mermaid (theme follows prefers-color-scheme)
 * - TOC scroll-spy (only in-page # anchors)
 */
(function () {
  const prefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;

  if (typeof mermaid !== 'undefined') {
    mermaid.initialize({
      startOnLoad: true,
      theme: prefersDark ? 'dark' : 'default',
      securityLevel: 'loose',
      flowchart: { curve: 'basis', htmlLabels: true, padding: 12 },
      themeVariables: prefersDark
        ? {
            fontFamily: 'Inter, system-ui, sans-serif',
            primaryColor: '#1b1f2a',
            primaryTextColor: '#e6e9ef',
            primaryBorderColor: '#7aa2f7',
            lineColor: '#a9b1c2',
            tertiaryColor: '#161922',
          }
        : { fontFamily: 'Inter, system-ui, sans-serif' },
    });
  }

  const sections = Array.from(
    document.querySelectorAll('section.stage, header.hero')
  );
  const links = Array.from(
    document.querySelectorAll('nav.toc a[href^="#"]')
  );

  if (!sections.length || !links.length) return;

  const byId = (id) =>
    links.find((a) => a.getAttribute('href') === '#' + id);

  const onScroll = () => {
    const y = window.scrollY + 120;
    let current = null;
    for (const s of sections) {
      if (s.offsetTop <= y) current = s.id;
    }
    links.forEach((a) => a.classList.remove('active'));
    if (current) {
      const a = byId(current);
      if (a) a.classList.add('active');
    }
  };

  window.addEventListener('scroll', onScroll, { passive: true });
  onScroll();
})();
