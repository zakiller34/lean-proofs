// Génère les icônes PNG (192, 512, maskable) à partir de icons/icon.svg via Chromium (Playwright).
// Usage : node scripts/build-icons.mjs   (nécessite le paquet "playwright" disponible)
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const dir = fileURLToPath(new URL('../icons/', import.meta.url));
const svg = await readFile(`${dir}icon.svg`, 'utf8');
const dataUrl = `data:image/svg+xml;base64,${Buffer.from(svg).toString('base64')}`;

// Maskable : fond plein bord à bord et motif réduit à 80 % (zone de sécurité Android).
const page = (size, maskable) => `
  <html><body style="margin:0;background:${maskable ? '#0b1220' : 'transparent'}">
    <img src="${dataUrl}" style="display:block;width:${maskable ? size * 0.8 : size}px;
      margin:${maskable ? size * 0.1 : 0}px">
  </body></html>`;

const targets = [
  ['icon-192.png', 192, false],
  ['icon-512.png', 512, false],
  ['icon-maskable-512.png', 512, true],
];

const browser = await chromium.launch();
for (const [name, size, maskable] of targets) {
  const p = await browser.newPage({ viewport: { width: size, height: size } });
  await p.setContent(page(size, maskable));
  await p.screenshot({ path: `${dir}${name}`, omitBackground: !maskable });
  await p.close();
  console.log(`✔ icons/${name}`);
}
await browser.close();
