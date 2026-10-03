// Génère les icônes PNG (PWA : 192, 512, maskable ; Android : lanceur classique et adaptatif)
// à partir de icons/icon.svg via Chromium (Playwright).
// Usage : node scripts/build-icons.mjs   (nécessite le paquet "playwright" disponible)
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const dir = fileURLToPath(new URL('../icons/', import.meta.url));
const mipmap = fileURLToPath(new URL('../android/res/mipmap-xxxhdpi/', import.meta.url));
const svg = await readFile(`${dir}icon.svg`, 'utf8');
const toDataUrl = (s) => `data:image/svg+xml;base64,${Buffer.from(s).toString('base64')}`;
const dataUrl = toDataUrl(svg);
// Premier plan de l'icône adaptative Android : motif sans fond, réduit dans la zone sûre (66/108).
const foregroundUrl = toDataUrl(svg.replace(/<rect[^>]*\/>/, ''));

// Maskable : fond plein bord à bord et motif réduit à 80 % (zone de sécurité Android).
const page = (src, size, scale, background) => [size, background === 'transparent', `
  <html><body style="margin:0;background:${background}">
    <img src="${src}" style="display:block;width:${size * scale}px;margin:${(size * (1 - scale)) / 2}px">
  </body></html>`];

const targets = [
  [`${dir}icon-192.png`, page(dataUrl, 192, 1, 'transparent')],
  [`${dir}icon-512.png`, page(dataUrl, 512, 1, 'transparent')],
  [`${dir}icon-maskable-512.png`, page(dataUrl, 512, 0.8, '#0b1220')],
  [`${mipmap}ic_launcher.png`, page(dataUrl, 192, 1, 'transparent')],
  [`${mipmap}ic_launcher_foreground.png`, page(foregroundUrl, 432, 0.6, 'transparent')],
];

const browser = await chromium.launch();
for (const [path, [size, transparent, html]] of targets) {
  const p = await browser.newPage({ viewport: { width: size, height: size } });
  await p.setContent(html);
  await p.screenshot({ path, omitBackground: transparent });
  await p.close();
  console.log(`✔ ${path}`);
}
await browser.close();
