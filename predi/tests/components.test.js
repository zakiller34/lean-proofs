import { test } from 'node:test';
import assert from 'node:assert/strict';
import { ICON_NAMES, WeatherIcon } from '../src/components/WeatherIcon.js';
import { CurrentWeather } from '../src/components/CurrentWeather.js';
import { ForecastList } from '../src/components/ForecastList.js';
import { slot } from './helpers.js';

const weather = { label: 'Pluie faible', icon: 'rain' };

test('WeatherIcon produit un SVG accessible pour chaque icône', () => {
  for (const name of ICON_NAMES) {
    const svg = WeatherIcon(name, { label: 'x' });
    assert.match(svg, /^<svg class="wx-icon" viewBox="0 0 64 64"/);
    assert.match(svg, /role="img" aria-label="x"/);
  }
  assert.match(WeatherIcon('inexistant'), /i-unknown/);
  assert.match(WeatherIcon('clear'), /aria-hidden="true"/);
});

test('CurrentWeather affiche température, détails et probabilité si disponible', () => {
  const html = CurrentWeather({ ...slot('2026-10-03T14:15', { temperature: 21.6, precipitationProbability: 40 }), weather });
  assert.match(html, /22°/);
  assert.match(html, /14h15/);
  assert.match(html, /Pluie faible/);
  assert.match(html, /40 %/);
  const noProba = CurrentWeather({ ...slot('2026-10-03T14:15'), weather });
  assert.doesNotMatch(noProba, /Risque de pluie/);
});

test('ForecastList affiche les créneaux, la pluie et le pas', () => {
  const html = ForecastList(
    [
      { ...slot('2026-10-03T14:30', { precipitation: 0.4 }), weather },
      { ...slot('2026-10-03T15:00'), weather },
    ],
    30,
  );
  assert.equal(html.match(/<li class="slot">/g).length, 2);
  assert.match(html, /0,4 mm/);
  assert.match(html, /pas de 30 min/);
});

test('ForecastList sans créneau affiche la fin de prévision', () => {
  assert.match(ForecastList([], 15), /Fin de la prévision du jour/);
});
