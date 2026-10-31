const $ = (id) => document.getElementById(id);
const canvas = $("wheel");
const ctx = canvas.getContext("2d");
const pageBackground = getComputedStyle(document.body).backgroundColor;
const tau = Math.PI * 2;
const reduced = matchMedia("(prefers-reduced-motion: reduce)");

const mainResults = new Map([
  ["Analysis_Certified.run_voblint_source_sound", "Source-level soundness"],
  ["Analysis_Certified.run_voblint_check_sound", "Source check soundness"],
  ["Analysis_Certified.run_voblint_proved", "PROVED verdict soundness"],
  ["Analysis_Certified.run_voblint_dead_check_unreached", "DEAD check unreachability"],
]);
const documentationBase = "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/";
const kinds = { thm: "Fact", const: "Constant", type: "Type", locale: "Locale" };

const state = {
  nodes: [],
  groups: [],
  theories: [],
  selected: -1,
  hover: -1,
  mode: 0,
  target: 0,
  zoom: 1,
  x: 0,
  y: 0,
  growth: 1,
  width: 0,
  height: 0,
  base: 1,
  visible: new Set(),
  related: new Set(),
};
let frame = 0;
let animation = null;
let pointer = null;
let filterTimer;
const format = (n) => n.toLocaleString("en-US");
const shortSession = (s) =>
  s
    .replace(/^Voblint_/, "")
    .replace(/^Analysis_/, "")
    .replaceAll("_", " ");
const element = (tag, text, className) => {
  const el = document.createElement(tag);
  el.textContent = text;
  if (className) el.className = className;
  return el;
};

// Squarified rectangles preserve area while avoiding long, narrow theory tiles.
function partition(items, box, assign) {
  if (!items.length) return;
  let [x, y, w, h] = box;
  const total = items.reduce((sum, item) => sum + item.weight, 0);
  const pending = [...items]
    .sort((a, b) => b.weight - a.weight)
    .map((item) => ({ item, area: (item.weight / total) * w * h }));
  const quality = (row, side) => {
    if (!row.length) return Infinity;
    const sum = row.reduce((s, n) => s + n.area, 0);
    const areas = row.map((n) => n.area);
    return Math.max(
      (side * side * Math.max(...areas)) / (sum * sum),
      (sum * sum) / (side * side * Math.min(...areas)),
    );
  };
  while (pending.length) {
    const side = Math.min(w, h);
    const row = [pending.shift()];
    while (pending.length && quality([...row, pending[0]], side) <= quality(row, side))
      row.push(pending.shift());
    const area = row.reduce((sum, n) => sum + n.area, 0);
    const thickness = area / side;
    let offset = 0;
    for (const node of row) {
      const length = node.area / thickness;
      assign(
        node.item,
        w >= h ? [x, y + offset, thickness, length] : [x + offset, y, length, thickness],
      );
      offset += length;
    }
    if (w >= h) {
      x += thickness;
      w -= thickness;
    } else {
      y += thickness;
      h -= thickness;
    }
  }
}

function layout(data) {
  state.layers = data.layers || {};
  state.theories = data.theories.map(([name, session, url]) => ({
    name,
    session,
    url,
    nodes: [],
    weight: 0,
  }));
  state.nodes = data.nodes.map(([id, theory, deps, external, anchored, cited], i) => {
    const kind = id.split(":", 1)[0];
    const name = id.slice(kind.length + 1);
    const node = {
      id,
      name,
      kind,
      main: kind === "thm" && mainResults.has(name),
      theory,
      deps,
      external,
      anchored,
      location: data.locations?.[id],
      cited: cited && kind === "thm",
      i,
      incoming: [],
      wx: 0,
      wy: 0,
      tx: 0,
      ty: 0,
      size: 1.6,
    };
    state.theories[theory].nodes.push(node);
    return node;
  });
  for (const n of state.nodes) for (const d of n.deps) state.nodes[d].incoming.push(n.i);
  const sessions = new Map();
  for (const theory of state.theories) {
    if (!theory.nodes.length) continue;
    theory.weight = theory.nodes.length;
    if (!sessions.has(theory.session))
      sessions.set(theory.session, { name: theory.session, theories: [], weight: 0 });
    const group = sessions.get(theory.session);
    group.theories.push(theory);
    group.weight += theory.weight;
  }
  state.groups = [...sessions.values()].sort((a, b) => b.weight - a.weight);
  layoutWheel();
  partition(state.groups, [-500, -360, 1000, 720], (group, box) => {
    group.box = box;
    const [x, y, w, h] = box;
    const header = Math.min(100, h * 0.14);
    partition(group.theories, [x + 3, y + header, w - 6, h - header - 3], (theory, rect) => {
      theory.box = rect;
      const [tx, ty, tw, th] = rect;
      const title = th > 30 ? 14 : 0;
      const width = Math.max(1, tw - 5),
        height = Math.max(1, th - title - 4);
      const columns = Math.max(1, Math.ceil(Math.sqrt((theory.weight * width) / height)));
      const rows = Math.ceil(theory.weight / columns);
      theory.nodes.forEach((node, j) => {
        node.tx = tx + 2 + (((j % columns) + 0.5) * width) / columns;
        node.ty = ty + title + ((Math.floor(j / columns) + 0.5) * height) / rows;
        node.size = Math.max(0.4, Math.min(width / columns, height / rows) * 0.4);
      });
    });
  });
}

// Folder sectors, file streaks and stable zoom sampling follow the CFSG corpus
// wheel. Radial layers here are statement-reference distances, not proof depth.
function layoutWheel() {
  const weights = state.groups.map((g) => g.weight ** 0.62);
  const total = weights.reduce((a, b) => a + b, 0);
  const gap = 0.03;
  let angle = -Math.PI / 2;
  // Start from the public results, then place disconnected declarations in outer
  // bands. This records only paths supported by the exported reference edges.
  const queue = state.nodes.filter((n) => n.main);
  for (const n of state.nodes) n.depth = Infinity;
  for (const n of queue) n.depth = 0;
  for (let at = 0; at < queue.length; at++) {
    const n = queue[at];
    for (const i of n.deps)
      if (state.nodes[i].depth > n.depth + 1) {
        state.nodes[i].depth = n.depth + 1;
        queue.push(state.nodes[i]);
      }
  }
  const maxDepth = Math.max(1, ...queue.map((n) => n.depth));
  for (const n of state.nodes) if (!Number.isFinite(n.depth)) n.depth = maxDepth + 1;
  state.groups.forEach((group, gi) => {
    const layer = group.name.startsWith("Voblint_Examples")
      ? "examples"
      : `d${Math.min(11, state.layers[group.name] || 1)}`;
    const base = getComputedStyle(document.body).getPropertyValue(`--strata-${layer}`).trim();
    const mix = (amount, target) => {
      const rgb = [1, 3, 5].map((at) => parseInt(base.slice(at, at + 2), 16));
      return `rgb(${rgb.map((v, i) => Math.round(v * (1 - amount) + target[i] * amount)).join(" ")})`;
    };
    group.color = mix(0.24, [32, 48, 56]);
    group.tint = mix(0.65, [255, 255, 255]);
    group.faint = mix(0.91, [255, 255, 255]);
    group.pale = mix(0.3, [255, 255, 255]);
    group.start = angle;
    group.end = angle + ((tau - gap * state.groups.length) * weights[gi]) / total;
    const width = group.end - group.start;
    group.theories.sort((a, b) => a.name.localeCompare(b.name));
    const members = group.theories.flatMap((t) =>
      [...t.nodes].sort((a, b) => a.depth - b.depth || a.name.localeCompare(b.name)),
    );
    const slots = members.length + group.theories.length * 6;
    const target = new Map();
    let slot = 0;
    for (const theory of group.theories) {
      slot += 6;
      theory.start = group.start + (width * slot) / slots;
      theory.color = group.color;
      theory.group = group;
      for (const n of members.filter((n) => state.theories[n.theory] === theory)) {
        target.set(n.i, group.start + (width * (slot + 0.5)) / slots);
        slot++;
      }
      theory.end = group.start + (width * slot) / slots;
    }
    const levels = new Map();
    for (const n of members) {
      if (!levels.has(n.depth)) levels.set(n.depth, []);
      levels.get(n.depth).push(n);
    }
    let radius = 1.5;
    for (const [, nodes] of [...levels].sort((a, b) => a[0] - b[0])) {
      nodes.sort((a, b) => target.get(a.i) - target.get(b.i));
      const crowd = nodes.length / ((radius + 0.5) * width);
      // Capacity grows with radius; using only the inner circumference creates
      // thousands of near-empty rows when a large layer starts near the centre.
      const rows = Math.max(
        1,
        Math.ceil(Math.sqrt(radius ** 2 + (2 * nodes.length) / width) - radius),
      );
      const thickness = crowd < 1 ? Math.max(0.3, crowd) : rows;
      for (let row = 0; row < rows; row++) {
        const r = radius + (thickness * (row + 0.5)) / rows;
        const line = nodes.filter((_, j) => j % rows === row);
        const spacing = 1 / r;
        const angles = [];
        line.forEach((n, j) => {
          angles.push(
            line.length * spacing > width
              ? group.start + (width * (j + 0.5)) / line.length
              : Math.max(target.get(n.i), j ? angles[j - 1] + spacing : -Infinity),
          );
        });
        if (angles.length && angles[angles.length - 1] > group.end - spacing / 2) {
          angles[angles.length - 1] = group.end - spacing / 2;
          for (let j = angles.length - 2; j >= 0; j--)
            angles[j] = Math.min(angles[j], angles[j + 1] - spacing);
        }
        line.forEach((n, j) => {
          n.radius = r + (((hash(n.i) - 0.5) * thickness) / rows) * 0.9;
          n.angle = angles[j] + (hash(n.i * 7 + 1) - 0.5) * spacing * 0.6;
        });
      }
      radius += thickness;
    }
    group.radialEnd = radius;
    angle = group.end + gap;
  });
  for (const group of state.groups)
    for (const theory of group.theories)
      for (const n of theory.nodes) {
        const unit = Math.max(0, (n.radius - 1.5) / Math.max(1, group.radialEnd - 1.5));
        const radius = 55 + 383 * unit ** 0.8;
        n.wx = Math.cos(n.angle) * radius;
        n.wy = Math.sin(n.angle) * radius;
        n.color = group.color;
        n.pale = group.pale;
      }
  // Important marks need their own breathing room, as in the reference wheel.
  const important = state.nodes.filter((n) => n.main || n.cited);
  for (let pass = 0; pass < 20; pass++)
    for (let a = 0; a < important.length; a++)
      for (let b = a + 1; b < important.length; b++) {
        const n = important[a],
          m = important[b];
        const dx = m.wx - n.wx,
          dy = m.wy - n.wy,
          distance = Math.hypot(dx, dy) || 1;
        const reach = n.main || m.main ? 22 : 10;
        if (distance >= reach) continue;
        const push = (reach - distance) / 2;
        n.wx -= (dx / distance) * push;
        n.wy -= (dy / distance) * push;
        m.wx += (dx / distance) * push;
        m.wy += (dy / distance) * push;
      }
}

function position(n) {
  const t = state.mode;
  return [(n.wx * (1 - t) + n.tx * t) * state.growth, (n.wy * (1 - t) + n.ty * t) * state.growth];
}
function scale() {
  return state.base * state.zoom;
}
function screen(n) {
  const [x, y] = position(n);
  return [state.width / 2 + state.x + x * scale(), state.height / 2 + state.y + y * scale()];
}
function invalidate() {
  if (!frame) frame = requestAnimationFrame(draw);
}
function animate(to, duration = 700) {
  animation = { from: {}, to, start: performance.now(), duration: reduced.matches ? 0 : duration };
  for (const key of Object.keys(to)) animation.from[key] = state[key];
  invalidate();
}
function reset() {
  animate({ zoom: 1, x: 0, y: 0 });
}
function arcBand(start, end, inner, outer, fill) {
  ctx.beginPath();
  ctx.arc(0, 0, outer, start, end);
  ctx.arc(0, 0, inner, end, start, true);
  ctx.closePath();
  ctx.fillStyle = fill;
  ctx.fill();
}
function label(text, x, y, width, font = 10) {
  if (width < 20) return;
  ctx.font = `500 ${font}px system-ui, sans-serif`;
  while (text.length > 3 && ctx.measureText(text).width > width) text = `${text.slice(0, -2)}…`;
  ctx.fillText(text, x, y);
}
function drawWheel(alpha) {
  ctx.globalAlpha = alpha;
  for (const group of state.groups) {
    arcBand(group.start + 0.004, group.end - 0.004, 454, 479, group.tint);
    for (const theory of group.theories) {
      arcBand(theory.start, theory.end - 0.001, 67, 445, group.faint);
      arcBand(theory.start, theory.end - 0.002, 443, 447, group.tint);
    }
    const angle = (group.start + group.end) / 2;
    const space = (group.end - group.start) * 494;
    if (space > 32) {
      ctx.save();
      ctx.translate(Math.cos(angle) * 495, Math.sin(angle) * 495);
      ctx.rotate(angle + Math.PI / 2 + (Math.sin(angle) > 0 ? Math.PI : 0));
      ctx.fillStyle = "#646a75";
      ctx.textAlign = "center";
      label(shortSession(group.name), 0, 0, space - 8, 10);
      ctx.restore();
    }
  }
  ctx.globalAlpha = 1;
}
function drawTree(alpha) {
  ctx.globalAlpha = alpha;
  ctx.textAlign = "left";
  for (const group of state.groups) {
    const [x, y, w, h] = group.box;
    ctx.fillStyle = group.tint;
    ctx.fillRect(x, y, w, h);
    ctx.strokeStyle = "#ffffff";
    ctx.lineWidth = 2;
    ctx.strokeRect(x, y, w, h);
    ctx.fillStyle = "#3f4858";
    if (h > 26) label(shortSession(group.name), x + 5, y + 13, w - 10, 10);
    for (const theory of group.theories) {
      const [tx, ty, tw, th] = theory.box;
      ctx.strokeStyle = "#ffffffaa";
      ctx.lineWidth = 1;
      ctx.strokeRect(tx + 1, ty + 1, tw - 2, th - 2);
      if (tw > 45 && th > 30) {
        ctx.fillStyle = "#656c7a";
        label(theory.name, tx + 4, ty + 10, tw - 8, 7);
      }
    }
  }
  ctx.globalAlpha = 1;
}
function hash(i) {
  return ((Math.imul(i, 2654435761) >>> 0) % 100003) / 100003;
}
function overviewAlpha(n) {
  if (
    n.cited ||
    n.main ||
    state.visible.size < state.nodes.length ||
    n.i === state.selected ||
    n.i === state.hover
  )
    return 1;
  if (state.mode > 0.5) return 1;
  const keep = Math.min(1, 0.12 * state.zoom ** 2);
  return Math.max(0, Math.min(1, (keep - hash(n.i * 3 + 2)) * 18));
}
function documentationURL(n) {
  const theory = state.theories[n.theory];
  const anchor = n.anchored
    ? `#${encodeURIComponent(`${n.name}|${n.kind === "thm" ? "fact" : n.kind}`)}`
    : "";
  return new URL(theory.url + anchor, documentationBase).href;
}
let cardRects = [];
function card(n, x, y, width, height, alpha) {
  const sx = state.width / 2 + state.x + x * scale();
  const sy = state.height / 2 + state.y + y * scale();
  const box = [sx - width / 2, sy - height / 2, sx + width / 2, sy + height / 2];
  if (
    cardRects.some(
      (r) =>
        box[0] < r.box[2] + 3 &&
        box[2] > r.box[0] - 3 &&
        box[1] < r.box[3] + 3 &&
        box[3] > r.box[1] - 3,
    )
  )
    return false;
  cardRects.push({ box, i: n.i });
  ctx.save();
  ctx.translate(x, y);
  ctx.scale(1 / scale(), 1 / scale());
  ctx.globalAlpha = alpha;
  ctx.fillStyle = "#fff";
  ctx.strokeStyle = n.main ? "#be573b" : n.color;
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.roundRect(-width / 2, -height / 2, width, height, 4);
  ctx.fill();
  ctx.stroke();
  ctx.fillStyle = n.main ? "#be573b" : n.color;
  ctx.fillRect(-width / 2, -height / 2 + 4, 3, height - 8);
  ctx.textAlign = "left";
  ctx.font = "600 9px system-ui, sans-serif";
  ctx.fillText(n.main ? "Main result" : kinds[n.kind], -width / 2 + 10, -height / 2 + 15);
  ctx.beginPath();
  ctx.rect(-width / 2 + 7, -height / 2 + 22, width - 14, height - 26);
  ctx.clip();
  ctx.fillStyle = "#303b48";
  const fontSize = Math.max(9, Math.min(11, width / 10));
  const leading = fontSize * 1.25;
  ctx.font = `600 ${fontSize}px system-ui, sans-serif`;
  const title = mainResults.get(n.name) || n.name.split(".").slice(1).join(".");
  const lines = Math.max(1, Math.floor((height - 27) / leading));
  let rest = title;
  for (let row = 0; row < lines && rest; row++) {
    let count = 1;
    while (count < rest.length && ctx.measureText(rest.slice(0, count + 1)).width <= width - 20)
      count++;
    let text = rest.slice(0, count);
    rest = rest.slice(count);
    if (row === lines - 1 && rest) {
      while (text.length && ctx.measureText(`${text}…`).width > width - 20)
        text = text.slice(0, -1);
      text += "…";
    }
    ctx.fillText(text, -width / 2 + 10, -height / 2 + 24 + fontSize + row * leading);
  }
  ctx.restore();
  return true;
}
function mark(n, alpha = 1) {
  if (cardRects.some((r) => r.i === n.i)) return;
  const [x, y] = position(n);
  const diamond = n.cited;
  const sx = state.width / 2 + state.x + x * scale(),
    sy = state.height / 2 + state.y + y * scale();
  if (sx < -200 || sx > state.width + 200 || sy < -100 || sy > state.height + 100 || alpha <= 0)
    return;
  if (
    alpha > 0.5 &&
    ((state.mode < 0.5 && (n.main || n.cited) && state.zoom >= 12) ||
      (state.mode > 0.5 && n.size * scale() * 2.5 >= 64))
  ) {
    const width = Math.min(180, state.mode < 0.5 ? state.zoom * 10 : n.size * scale() * 2.2);
    if (card(n, x, y, width, width * 0.65, alpha)) return;
  }
  const r = n.main
    ? 7 / scale()
    : diamond
      ? 3.5 / scale()
      : Math.min(2.5 / scale(), 1.45) * (1 - state.mode) +
        Math.min(18 / scale(), n.size) * state.mode;
  ctx.globalAlpha = alpha;
  ctx.fillStyle = n.main ? "#be573b" : diamond ? "#bc963d" : n.kind === "const" ? n.pale : n.color;
  ctx.beginPath();
  if (n.main) {
    for (let k = 0; k < 10; k++) {
      const a = -Math.PI / 2 + (k * Math.PI) / 5;
      const radius = k % 2 ? r * 0.46 : r;
      if (!k) ctx.moveTo(x + Math.cos(a) * radius, y + Math.sin(a) * radius);
      else ctx.lineTo(x + Math.cos(a) * radius, y + Math.sin(a) * radius);
    }
    ctx.closePath();
  } else if (diamond) {
    ctx.moveTo(x, y - r);
    ctx.lineTo(x + r, y);
    ctx.lineTo(x, y + r);
    ctx.lineTo(x - r, y);
    ctx.closePath();
  } else if (n.kind === "const") ctx.rect(x - r, y - r, r * 2, r * 2);
  else if (n.kind === "type") {
    ctx.moveTo(x, y - r * 1.2);
    ctx.lineTo(x + r, y + r);
    ctx.lineTo(x - r, y + r);
    ctx.closePath();
  } else if (n.kind === "locale") {
    ctx.moveTo(x, y - r * 1.2);
    ctx.lineTo(x + r, y);
    ctx.lineTo(x, y + r * 1.2);
    ctx.lineTo(x - r, y);
    ctx.closePath();
  } else ctx.arc(x, y, r, 0, tau);
  if (n.kind === "locale" && !diamond && !n.main) {
    ctx.strokeStyle = n.color;
    ctx.lineWidth = Math.min(r * 0.5, 1 / scale());
    ctx.stroke();
  } else ctx.fill();
  if (diamond || n.main) {
    ctx.strokeStyle = "#fff";
    ctx.lineWidth = 1 / scale();
    ctx.stroke();
  }
}
function draw(now) {
  frame = 0;
  cardRects = [];
  if (animation) {
    const t = animation.duration ? Math.min(1, (now - animation.start) / animation.duration) : 1;
    const ease = t < 0.5 ? 4 * t ** 3 : 1 - (-2 * t + 2) ** 3 / 2;
    for (const key of Object.keys(animation.to))
      state[key] = animation.from[key] + (animation.to[key] - animation.from[key]) * ease;
    if (t === 1) animation = null;
  }
  const dpr = Math.min(devicePixelRatio || 1, 2);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, state.width, state.height);
  ctx.translate(state.width / 2 + state.x, state.height / 2 + state.y);
  ctx.scale(scale(), scale());
  if (state.mode < 1) drawWheel(1 - state.mode);
  if (state.mode > 0) drawTree(state.mode);
  if (state.mode < 0.99) {
    ctx.save();
    const size = Math.min(1, 1 / scale());
    ctx.scale(size, size);
    ctx.globalAlpha = 1 - state.mode;
    ctx.fillStyle = pageBackground;
    ctx.beginPath();
    ctx.arc(0, 0, 58, 0, tau);
    ctx.fill();
    ctx.strokeStyle = "#bc963d55";
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(0, 0, 46, 0, tau);
    ctx.stroke();
    ctx.fillStyle = "#213b43";
    ctx.beginPath();
    ctx.arc(0, 0, 25, 0, tau);
    ctx.fill();
    ctx.fillStyle = "#c6a24a";
    ctx.beginPath();
    ctx.arc(0, 0, 5, 0, tau);
    ctx.fill();
    ctx.fillStyle = "#334951";
    ctx.font = "16px Georgia, serif";
    ctx.textAlign = "center";
    ctx.fillText("Voblint", 0, 71);
    ctx.restore();
  }
  const focus = state.hover >= 0 ? state.hover : state.selected;
  const related =
    focus >= 0
      ? new Set([focus, ...state.nodes[focus].deps, ...state.nodes[focus].incoming])
      : null;
  for (const n of state.nodes) {
    if (n.cited || n.main || !overviewAlpha(n)) continue;
    const active = state.visible.has(n.i);
    mark(n, (!active ? 0.025 : related && !related.has(n.i) ? 0.12 : 0.9) * overviewAlpha(n));
  }
  if (focus >= 0) {
    const node = state.nodes[focus];
    const [x, y] = position(node);
    ctx.globalAlpha = 0.5;
    ctx.lineWidth = 0.75 / Math.sqrt(state.zoom);
    for (const [neighbors, color] of [
      [node.deps, "#435fc5"],
      [node.incoming, "#b28c3d"],
    ]) {
      ctx.strokeStyle = color;
      for (const i of neighbors) {
        const [dx, dy] = position(state.nodes[i]);
        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.quadraticCurveTo(
          (x + dx) / 2 - (dy - y) * 0.06,
          (y + dy) / 2 + (dx - x) * 0.06,
          dx,
          dy,
        );
        ctx.stroke();
      }
    }
    for (const i of related) mark(state.nodes[i]);
    ctx.globalAlpha = 1;
    ctx.beginPath();
    ctx.arc(x, y, 9 / scale(), 0, tau);
    ctx.strokeStyle = "#242f4c";
    ctx.lineWidth = 1.3 / scale();
    ctx.stroke();
  }
  for (const n of state.nodes)
    if (n.cited && !n.main) mark(n, (state.visible.has(n.i) ? 1 : 0.07) * overviewAlpha(n));
  const occupied = [];
  for (const n of state.nodes)
    if (n.main) {
      mark(n, state.visible.has(n.i) ? 1 : 0.1);
      if (!state.visible.has(n.i) || cardRects.some((r) => r.i === n.i)) continue;
      const [x, y] = position(n);
      const [sx, sy] = screen(n);
      const title = mainResults.get(n.name);
      ctx.font = `600 ${11 / scale()}px system-ui, sans-serif`;
      const width = ctx.measureText(title).width * scale();
      const box = [sx + 12, sy - 9, sx + 12 + width, sy + 6];
      if (
        occupied.some(
          ([l, t, r, b]) => box[0] < r + 8 && box[2] > l - 8 && box[1] < b + 5 && box[3] > t - 5,
        )
      )
        continue;
      occupied.push(box);
      ctx.globalAlpha = 1;
      ctx.textAlign = "left";
      ctx.lineWidth = 3 / scale();
      ctx.strokeStyle = pageBackground;
      ctx.strokeText(title, x + 12 / scale(), y + 3 / scale());
      ctx.fillStyle = "#a34730";
      ctx.fillText(title, x + 12 / scale(), y + 3 / scale());
    }
  ctx.globalAlpha = 1;
  canvas.dataset.layout = state.mode === 1 ? "treemap" : state.mode === 0 ? "wheel" : "transition";
  canvas.dataset.animating = String(!!animation);
  canvas.dataset.zoom = String(state.zoom);
  if (animation) invalidate();
}
function resize() {
  const box = canvas.getBoundingClientRect();
  state.width = box.width;
  state.height = box.height;
  const dpr = Math.min(devicePixelRatio || 1, 2);
  canvas.width = Math.round(box.width * dpr);
  canvas.height = Math.round(box.height * dpr);
  state.base = Math.min((box.width - 42) / 1060, (box.height - 155) / 1050);
  invalidate();
}
function resultButton(node) {
  const button = element(
    "button",
    node.name.split(".").slice(1).join(".") || node.name,
    "proof-result",
  );
  button.type = "button";
  button.setAttribute("aria-pressed", String(state.selected === node.i));
  button.append(element("small", `${kinds[node.kind]} · ${state.theories[node.theory].name}`));
  button.addEventListener("click", () => select(node.i, true));
  return button;
}
function filter() {
  const query = $("search").value.trim().toLowerCase();
  const session = $("session").value;
  const kind = $("kind").value;
  const cited = $("cited").checked;
  const matches = state.nodes.filter(
    (n) =>
      (!query || n.name.toLowerCase().includes(query)) &&
      (!session || state.theories[n.theory].session === session) &&
      (!kind || n.kind === kind) &&
      (!cited || n.cited),
  );
  state.visible = new Set(matches.map((n) => n.i));
  $("visible-count").textContent =
    `${format(matches.length)} / ${format(state.nodes.length)} entities`;
  const browsing = query || session || kind || cited;
  const listed = browsing ? matches : state.nodes.filter((n) => n.main);
  $("result-count").textContent = browsing
    ? `${format(matches.length)} matches${matches.length > 60 ? " · first 60 listed" : ""}`
    : "Main results · select to explore";
  $("results").replaceChildren(...listed.slice(0, 60).map(resultButton));
  if (browsing && !matches.length)
    $("results").append(element("p", "No declarations match these filters.", "proof-muted"));
  invalidate();
}
function select(i, focus = false) {
  state.selected = i;
  state.hover = -1;
  $("tooltip").hidden = true;
  const panel = $("selection");
  panel.hidden = i < 0;
  panel.replaceChildren();
  if (i >= 0) {
    const n = state.nodes[i],
      theory = state.theories[n.theory];
    const close = element("button", "×", "proof-close");
    close.type = "button";
    close.setAttribute("aria-label", "Clear selection");
    close.addEventListener("click", () => select(-1));
    panel.append(
      close,
      element("p", `${kinds[n.kind]}${n.cited ? " · cited in thesis" : ""}`),
      element("h2", n.name),
    );
    panel.append(element("p", `${theory.name} · ${shortSession(theory.session)}`));
    const link = element(
      "a",
      n.location?.kind === "interpretation"
        ? "Open interpretation in Isabelle ↗"
        : n.anchored
          ? "Open source command in Isabelle ↗"
          : "Open containing theory ↗",
    );
    link.href = documentationURL(n);
    link.target = "_blank";
    link.rel = "noreferrer";
    panel.append(link);
    if (n.location?.kind === "interpretation") {
      panel.append(
        element(
          "p",
          "Isabelle generates this entity at the interpretation command; its statement is not displayed there.",
          "proof-muted",
        ),
      );
      if (n.location.generic !== undefined) {
        const generic = state.nodes[n.location.generic];
        const source = element("a", "Open generic source ↗");
        source.href = documentationURL(generic);
        source.target = "_blank";
        source.rel = "noreferrer";
        panel.append(source, element("p", generic.name, "proof-muted"));
      }
    }
    panel.append(
      element(
        "p",
        `Mentions ${n.deps.length} project entities and ${n.external} library entities. Mentioned by ${n.incoming.length} project declarations. Blue lines: mentions; gold lines: mentioned by. These are statement/specification references, not proof dependencies.`,
      ),
    );
    if (n.deps.length) {
      const list = element("div", "", "proof-dependencies");
      list.append(...n.deps.map((j) => resultButton(state.nodes[j])));
      panel.append(list);
    }
    if (focus) {
      const [x, y] = position(n);
      const zoom = 2.6;
      animate({ zoom, x: -x * state.base * zoom, y: -y * state.base * zoom });
    }
    history.replaceState(null, "", `#${encodeURIComponent(n.id)}`);
  } else history.replaceState(null, "", location.pathname + location.search);
  filter();
  invalidate();
}
function hit(x, y) {
  for (const { box, i } of cardRects)
    if (x >= box[0] && x <= box[2] && y >= box[1] && y <= box[3]) return i;
  let best = -1,
    distance = 9 ** 2;
  for (const n of state.nodes) {
    if (!state.visible.has(n.i) || overviewAlpha(n) < 0.5) continue;
    const [nx, ny] = screen(n);
    const d = (x - nx) ** 2 + (y - ny) ** 2;
    if (d < distance) {
      distance = d;
      best = n.i;
    }
  }
  return best;
}
function hover(event) {
  const rect = canvas.getBoundingClientRect();
  const x = event.clientX - rect.left,
    y = event.clientY - rect.top;
  const found = hit(x, y);
  if (found !== state.hover) {
    state.hover = found;
    invalidate();
  }
  const tooltip = $("tooltip");
  tooltip.hidden = found < 0;
  if (found >= 0) {
    const n = state.nodes[found];
    tooltip.replaceChildren(
      element("strong", n.name),
      element(
        "span",
        `${n.main ? mainResults.get(n.name) : kinds[n.kind]} · ${state.theories[n.theory].name} · Click to open documentation ↗`,
      ),
    );
    tooltip.style.left = `${Math.max(8, Math.min(x + 16, state.width - tooltip.offsetWidth - 12))}px`;
    tooltip.style.top = `${Math.max(60, Math.min(y + 16, state.height - tooltip.offsetHeight - 12))}px`;
  }
}
function zoomBy(factor, x = state.width / 2, y = state.height / 2) {
  const zoom = Math.max(0.65, Math.min(100, state.zoom * factor));
  const ratio = zoom / state.zoom;
  animate(
    {
      zoom,
      x: x - state.width / 2 - (x - state.width / 2 - state.x) * ratio,
      y: y - state.height / 2 - (y - state.height / 2 - state.y) * ratio,
    },
    180,
  );
}
function setMode(mode) {
  state.target = mode;
  state.hover = -1;
  $("tooltip").hidden = true;
  $("view-wheel").setAttribute("aria-pressed", String(!mode));
  $("view-tree").setAttribute("aria-pressed", String(!!mode));
  canvas.setAttribute(
    "aria-label",
    `${mode ? "Treemap" : "Declaration wheel"}. Drag to pan, scroll to zoom. Search and results provide keyboard access to declarations.`,
  );
  animate({ mode, zoom: 1, x: 0, y: 0, growth: 1 }, 1000);
}
$("view-wheel").addEventListener("click", () => setMode(0));
$("view-tree").addEventListener("click", () => setMode(1));
$("zoom-in").addEventListener("click", () => zoomBy(1.5));
$("zoom-out").addEventListener("click", () => zoomBy(1 / 1.5));
$("reset").addEventListener("click", reset);
$("grow").addEventListener("click", () => {
  state.growth = 0.05;
  animate({ growth: 1, zoom: 1, x: 0, y: 0 }, 1400);
});
$("search").addEventListener("input", () => {
  clearTimeout(filterTimer);
  filterTimer = setTimeout(filter, 100);
});
for (const id of ["session", "kind", "cited"]) $(id).addEventListener("change", filter);
canvas.addEventListener(
  "wheel",
  (e) => {
    e.preventDefault();
    animation = null;
    state.hover = -1;
    $("tooltip").hidden = true;
    const units = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? state.height : 1;
    if (e.ctrlKey || e.metaKey) {
      const box = canvas.getBoundingClientRect();
      const x = e.clientX - box.left - state.width / 2;
      const y = e.clientY - box.top - state.height / 2;
      const zoom = Math.max(0.65, Math.min(100, state.zoom * Math.exp(-e.deltaY * units * 0.01)));
      const ratio = zoom / state.zoom;
      state.x = x - (x - state.x) * ratio;
      state.y = y - (y - state.y) * ratio;
      state.zoom = zoom;
    } else {
      state.x -= e.deltaX * units;
      state.y -= e.deltaY * units;
    }
    invalidate();
  },
  { passive: false },
);
canvas.addEventListener("pointerdown", (e) => {
  animation = null;
  pointer = {
    id: e.pointerId,
    x: e.clientX,
    y: e.clientY,
    startX: e.clientX,
    startY: e.clientY,
    moved: false,
  };
  canvas.setPointerCapture(e.pointerId);
});
canvas.addEventListener("pointermove", (e) => {
  if (pointer && pointer.id === e.pointerId) {
    state.x += e.clientX - pointer.x;
    state.y += e.clientY - pointer.y;
    pointer.x = e.clientX;
    pointer.y = e.clientY;
    pointer.moved ||= Math.hypot(e.clientX - pointer.startX, e.clientY - pointer.startY) > 4;
    state.hover = -1;
    $("tooltip").hidden = true;
    invalidate();
  } else if (!pointer) hover(e);
});
canvas.addEventListener("pointerup", (e) => {
  if (!pointer || pointer.id !== e.pointerId) return;
  if (!pointer.moved) {
    const box = canvas.getBoundingClientRect();
    const found = hit(e.clientX - box.left, e.clientY - box.top);
    select(found);
    if (found >= 0)
      window.open(documentationURL(state.nodes[found]), "_blank", "noopener,noreferrer");
  }
  pointer = null;
});
canvas.addEventListener("pointercancel", () => {
  pointer = null;
});
canvas.addEventListener("pointerleave", () => {
  state.hover = -1;
  $("tooltip").hidden = true;
  invalidate();
});
canvas.addEventListener("dblclick", (e) => {
  const box = canvas.getBoundingClientRect();
  zoomBy(1.8, e.clientX - box.left, e.clientY - box.top);
});
canvas.addEventListener("keydown", (e) => {
  if (
    ["+", "=", "-", "0", "Escape", "ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(
      e.key,
    )
  )
    e.preventDefault();
  if (e.key === "+" || e.key === "=") zoomBy(1.5);
  if (e.key === "-") zoomBy(1 / 1.5);
  if (e.key === "0") reset();
  if (e.key === "Escape") select(-1);
  if (e.key.startsWith("Arrow")) {
    animation = null;
    state.x += e.key === "ArrowLeft" ? 40 : e.key === "ArrowRight" ? -40 : 0;
    state.y += e.key === "ArrowUp" ? 40 : e.key === "ArrowDown" ? -40 : 0;
    invalidate();
  }
});
new ResizeObserver(resize).observe(canvas);

async function start() {
  try {
    const response = await fetch("assets/proof-map.json");
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const data = await response.json();
    layout(data);
    for (const group of [...state.groups].sort((a, b) => a.name.localeCompare(b.name))) {
      const option = element("option", shortSession(group.name));
      option.value = group.name;
      $("session").append(option);
    }
    const usedTheories = state.theories.filter((t) => t.nodes.length).length;
    $("stats").replaceChildren(
      ...[
        [state.nodes.length, "entities"],
        [usedTheories, "theories"],
        [state.groups.length, "sessions"],
      ].map(([value, text]) => {
        const item = element("div", text);
        item.prepend(element("strong", format(value)));
        return item;
      }),
    );
    $("snapshot").textContent =
      `Isabelle export: ${data.exported}. Library declarations outside the exported sessions are not included. Source links without an individual anchor open the containing theory.`;
    if (new URLSearchParams(location.search).get("view") === "treemap") {
      state.mode = 1;
      state.target = 1;
      $("view-wheel").setAttribute("aria-pressed", "false");
      $("view-tree").setAttribute("aria-pressed", "true");
    }
    $("map-status").hidden = true;
    filter();
    resize();
    const id = decodeURIComponent(location.hash.slice(1));
    const selected = state.nodes.findIndex((n) => n.id === id);
    if (selected >= 0) select(selected, true);
    else {
      state.growth = reduced.matches ? 1 : 0.08;
      animate({ growth: 1 }, 1200);
    }
  } catch (error) {
    $("map-status").textContent =
      `The declaration data could not be loaded (${error.message}). Please reload or try again after the site build finishes.`;
    $("stats").textContent = "Declaration data unavailable.";
    console.error("Proof map:", error);
  }
}
start();
