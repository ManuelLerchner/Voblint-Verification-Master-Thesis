/*
 * Scenes animate by default and pause only once known to be offscreen, so a failed
 * or missing script leaves the page moving rather than frozen on a first frame.
 */

/* Renders prose whose code fragments are marked with backticks. */
function withCode(text) {
  const escapeHtml = (part) =>
    part.replace(/[&<>]/g, (ch) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[ch]);

  return text
    .split("`")
    .map((part, i) => (i % 2 === 1 ? `<code>${escapeHtml(part)}</code>` : escapeHtml(part)))
    .join("");
}

/* The home page used to hold the analyzer and these sections; old links still land. */
const movedAnchors = {
  "#analyzer": "playground.html",
  "#soundness": "#theorems",
  "#reports": "playground.html#reading",
  "#reading": "playground.html#reading",
};

if (movedAnchors[location.hash]) {
  const target = movedAnchors[location.hash];

  if (target.startsWith("#")) {
    history.replaceState(null, "", target);
    document.querySelector(target)?.scrollIntoView();
  } else {
    location.replace(target);
  }
}

const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

if ("IntersectionObserver" in window) {
  const observer = new IntersectionObserver((entries) => {
    for (const entry of entries) {
      entry.target.classList.toggle("is-offscreen", !entry.isIntersecting);
    }
  });

  for (const scene of document.querySelectorAll(".scene")) {
    observer.observe(scene);
  }
}

/* Helpers the figure scripts in figures/ share; each figure script is its own block. */
const mod = (x, m) => ((x % m) + m) % m;
const SVG_NS = "http://www.w3.org/2000/svg";

const escapeText = (text) =>
  text.replace(/[&<>]/g, (ch) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[ch]);

const REPO_URL = "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis";

/* -------------------------------------------------------------------------- */
/* Reading progress, and the commit the site was built from                   */
/* -------------------------------------------------------------------------- */

/* Repository figures are never written into the markup by hand: scripts/pages_stats.py
   derives them at site-build time and the page fills every [data-stat] from that.
   The literal in the markup is the fallback a source checkout renders, so it goes
   stale silently -- data-stat is what keeps the published page honest. The figure
   scripts fill their own scopes too; filling twice writes the same value. */
for (const element of document.querySelectorAll("[data-stat]")) {
  const value = element.dataset.stat
    .split(".")
    .reduce((obj, key) => obj?.[key], window.VOBLINT_STATS);

  if (value !== undefined) {
    element.textContent = typeof value === "number" ? value.toLocaleString("en-US") : value;
  }
}

/* The site build writes the commit into window.VOBLINT_STATS; without it the link stays hidden. */
for (const build of document.querySelectorAll(".doc-toc-build")) {
  const stats = window.VOBLINT_STATS;

  if (stats?.commit_sha) {
    const link = build.querySelector("a");
    link.href = `${REPO_URL}/commit/${stats.commit_sha}`;
    link.title = `Built on ${stats.date} from ${stats.commit_sha}`;
    link.querySelector("code").textContent = stats.commit;
    build.hidden = false;
  }
}

for (const toc of document.querySelectorAll(".doc-toc")) {
  const fill = toc.querySelector(".doc-toc-fill");
  const percent = toc.querySelector(".doc-toc-percent span");
  const main = document.querySelector(".doc-main");
  const links = [...toc.querySelectorAll("a[data-target]")]
    .map((link) => ({ link, section: document.getElementById(link.dataset.target) }))
    .filter(({ section }) => section);
  let frame = 0;

  const update = () => {
    frame = 0;
    const probe = window.innerHeight * 0.35;
    const box = main.getBoundingClientRect();

    /* The bar fills as the article passes the probe, but its last screenful never
       reaches it: nothing below the article is tall enough to scroll that far. So
       the range ends wherever scrolling stops, and the foot of the page reads 100%. */
    const top = box.top + window.scrollY;
    const start = top - probe;
    const end = Math.min(
      top + box.height - probe,
      document.documentElement.scrollHeight - window.innerHeight,
    );
    const read =
      end > start ? Math.min(1, Math.max(0, (window.scrollY - start) / (end - start))) : 1;
    fill.style.height = `${(read * 100).toFixed(1)}%`;
    percent.textContent = String(Math.round(read * 100));

    let current = 0;

    links.forEach(({ section }, i) => {
      if (section.getBoundingClientRect().top <= probe) {
        current = i;
      }
    });

    links.forEach(({ link }, i) => {
      link.classList.toggle("is-read", i < current);
      link.classList.toggle("is-current", i === current);
    });
  };

  const schedule = () => {
    if (!frame) {
      frame = requestAnimationFrame(update);
    }
  };

  window.addEventListener("scroll", schedule, { passive: true });
  window.addEventListener("resize", schedule);
  update();
}

/* -------------------------------------------------------------------------- */
/* Shared stepper                                                             */
/* -------------------------------------------------------------------------- */

/*
 * Wires a play button and step chips to a render function. Chips either ship in the
 * markup (data-goto) or are created here, one per step; the controls stay hidden
 * without script, so the figure's final state is what a no-script reader sees.
 */
function makeStepper(
  figure,
  { count, render, controls, chipsBox, interval = 3200, autoplay = !reducedMotion },
) {
  const toggle = controls.querySelector(".loop-play");
  const icon = toggle.querySelector("i");
  let step = 0;
  let timer = null;

  let chips = [...chipsBox.querySelectorAll("[data-goto]")];

  if (!chips.length) {
    chips = Array.from({ length: count }, (_, i) => {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.dataset.goto = String(i);
      chip.textContent = String(i + 1);
      chipsBox.append(chip);
      return chip;
    });
  }

  const show = (next) => {
    step = (next + count) % count;
    figure.dataset.step = String(step);
    chips.forEach((chip) => {
      chip.setAttribute("aria-pressed", String(Number(chip.dataset.goto) === step));
    });
    render(step);
  };

  const setPlaying = (playing) => {
    clearInterval(timer);
    timer = playing
      ? setInterval(() => {
          if (!figure.classList.contains("is-offscreen")) {
            show(step + 1);
          }
        }, interval)
      : null;
    icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
    toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
  };

  for (const chip of chips) {
    chip.addEventListener("click", () => {
      setPlaying(false);
      show(Number(chip.dataset.goto));
    });
  }

  toggle.addEventListener("click", () => setPlaying(timer === null));
  controls.hidden = false;
  show(0);
  setPlaying(autoplay);

  return {
    show: (i) => {
      setPlaying(false);
      show(i);
    },
    stop: () => setPlaying(false),
    current: () => step,
  };
}

/* Draws dots for the integers low..high into an SVG row, classed by a predicate. */
function drawDots(svg, { low, high, x0, dx, y, classOf, radius = 6 }) {
  svg.replaceChildren();

  for (let n = low; n <= high; n++) {
    const circle = document.createElementNS(SVG_NS, "circle");
    const kind = classOf(n);
    circle.setAttribute("cx", String(x0 + (n - low) * dx));
    circle.setAttribute("cy", String(y));
    circle.setAttribute("r", String(kind === "out" ? radius * 0.55 : radius));
    circle.setAttribute("class", `dot-${kind}`);
    svg.append(circle);
  }
}
