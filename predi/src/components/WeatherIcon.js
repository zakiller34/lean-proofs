// Icônes météo SVG inline (viewBox 64x64). Les couleurs sont gérées en CSS via les classes.

const CLOUD = 'M19 44h27a9 9 0 0 0 .6-18 13 13 0 0 0-25-3.4A10.5 10.5 0 0 0 19 44z';
const MOON = 'M40 14a16 16 0 1 0 12 26 13 13 0 0 1-12-26z';

const rays = (cx, cy, r1, r2) =>
  Array.from({ length: 8 }, (_, i) => {
    const a = (i * Math.PI) / 4;
    const p = (r) => [cx + r * Math.cos(a), cy + r * Math.sin(a)].map((n) => n.toFixed(1));
    const [x1, y1] = p(r1);
    const [x2, y2] = p(r2);
    return `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>`;
  }).join('');

const sun = (cx = 32, cy = 32, r = 11) =>
  `<g class="i-sun"><circle cx="${cx}" cy="${cy}" r="${r}"/>${rays(cx, cy, r + 5, r + 10)}</g>`;
const smallSun = `<g class="i-sun"><circle cx="22" cy="22" r="8"/>${rays(22, 22, 12, 16)}</g>`;
const moon = `<path class="i-moon" d="${MOON}"/>`;
const smallMoon = `<path class="i-moon" d="${MOON}" transform="translate(-4 -4) scale(.7)"/>`;
const cloud = (dy = 0) => `<path class="i-cloud" d="${CLOUD}" transform="translate(0 ${dy})"/>`;

const lines = (coords) =>
  `<g class="i-rain">${coords.map(([x, y, l]) => `<line x1="${x}" y1="${y}" x2="${x - 3}" y2="${y + l}"/>`).join('')}</g>`;
const dots = (coords, cls) =>
  `<g class="${cls}">${coords.map(([x, y]) => `<circle cx="${x}" cy="${y}" r="1.8"/>`).join('')}</g>`;

const SHAPES = {
  clear: sun(),
  'clear-night': moon,
  partly: smallSun + cloud(4),
  'partly-night': smallMoon + cloud(4),
  cloudy: cloud(-2),
  fog: `${cloud(-8)}<g class="i-fog"><line x1="14" y1="46" x2="50" y2="46"/><line x1="18" y1="53" x2="46" y2="53"/></g>`,
  drizzle: cloud(-8) + dots([[24, 46], [34, 46], [44, 46], [29, 54], [39, 54]], 'i-drop'),
  rain: cloud(-8) + lines([[25, 44, 8], [35, 44, 8], [45, 44, 8]]),
  'heavy-rain': cloud(-8) + lines([[22, 43, 12], [30, 45, 12], [38, 43, 12], [46, 45, 12]]),
  showers: smallSun + cloud(-2) + lines([[28, 48, 8], [38, 48, 8]]),
  sleet: cloud(-8) + lines([[26, 44, 8], [42, 44, 8]]) + dots([[34, 48], [34, 56]], 'i-snow'),
  snow: cloud(-8) + dots([[24, 46], [34, 46], [44, 46], [29, 54], [39, 54]], 'i-snow'),
  thunder: `${cloud(-8)}<path class="i-bolt" d="M34 38l-7 12h7l-3 10 10-14h-7l4-8z"/>`,
  unknown: `<path class="i-cloud i-unknown" d="${CLOUD}"/>`,
};

/** Retourne le markup SVG de l'icône. */
export function WeatherIcon(icon, { size = 48, label = '' } = {}) {
  const shape = SHAPES[icon] ?? SHAPES.unknown;
  const a11y = label ? `role="img" aria-label="${label}"` : 'aria-hidden="true"';
  return `<svg class="wx-icon" viewBox="0 0 64 64" width="${size}" height="${size}" ${a11y}>${shape}</svg>`;
}

export const ICON_NAMES = Object.keys(SHAPES);
