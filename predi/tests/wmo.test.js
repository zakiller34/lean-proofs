import { test } from 'node:test';
import assert from 'node:assert/strict';
import { codeFromPrecipitation, describeWeather } from '../src/utils/wmo.js';
import { ICON_NAMES } from '../src/components/WeatherIcon.js';

test('describeWeather mappe les codes WMO principaux', () => {
  assert.deepEqual(describeWeather(0), { label: 'Ciel dégagé', icon: 'clear' });
  assert.deepEqual(describeWeather(3), { label: 'Couvert', icon: 'cloudy' });
  assert.equal(describeWeather(45).icon, 'fog');
  assert.equal(describeWeather(63).icon, 'rain');
  assert.equal(describeWeather(82).icon, 'heavy-rain');
  assert.equal(describeWeather(95).icon, 'thunder');
});

test('describeWeather utilise la variante nuit seulement quand elle existe', () => {
  assert.equal(describeWeather(0, { isDay: false }).icon, 'clear-night');
  assert.equal(describeWeather(2, { isDay: false }).icon, 'partly-night');
  assert.equal(describeWeather(61, { isDay: false }).icon, 'rain');
});

test('describeWeather déduit un code des précipitations si le code est absent', () => {
  assert.equal(describeWeather(null, { precipitation: 1.2 }).icon, 'rain');
  assert.equal(describeWeather(null, { precipitation: 0 }).icon, 'unknown');
  assert.equal(describeWeather(1234).label, 'Indisponible');
});

test('codeFromPrecipitation', () => {
  assert.equal(codeFromPrecipitation(null), null);
  assert.equal(codeFromPrecipitation(0.05), null);
  assert.equal(codeFromPrecipitation(0.3), 61);
  assert.equal(codeFromPrecipitation(1), 63);
  assert.equal(codeFromPrecipitation(5), 65);
});

test('chaque code WMO pointe vers une icône SVG existante', () => {
  const codes = [0, 1, 2, 3, 45, 48, 51, 53, 55, 56, 57, 61, 63, 65, 66, 67, 71, 73, 75, 77, 80, 81, 82, 85, 86, 95, 96, 99];
  for (const code of codes) {
    for (const isDay of [true, false]) {
      const { icon } = describeWeather(code, { isDay });
      assert.ok(ICON_NAMES.includes(icon), `icône manquante : ${icon} (code ${code})`);
    }
  }
});
