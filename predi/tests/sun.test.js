import { test } from 'node:test';
import assert from 'node:assert/strict';
import { isDaytime, localTimeToDate } from '../src/utils/sun.js';

const LAT = 43.627;
const LON = 3.86;

test('localTimeToDate applique le décalage UTC de l’API', () => {
  assert.equal(localTimeToDate('2026-10-03T14:30', 7200).toISOString(), '2026-10-03T12:30:00.000Z');
  assert.equal(localTimeToDate('2026-01-10T00:15', 3600).toISOString(), '2026-01-09T23:15:00.000Z');
});

test('isDaytime à Montpellier : lever ~7h46 et coucher ~19h25 le 3 octobre (CEST)', () => {
  assert.equal(isDaytime('2026-10-03T13:00', 7200, LAT, LON), true);
  assert.equal(isDaytime('2026-10-03T00:00', 7200, LAT, LON), false);
  assert.equal(isDaytime('2026-10-03T07:30', 7200, LAT, LON), false);
  assert.equal(isDaytime('2026-10-03T08:00', 7200, LAT, LON), true);
  assert.equal(isDaytime('2026-10-03T19:15', 7200, LAT, LON), true);
  assert.equal(isDaytime('2026-10-03T19:45', 7200, LAT, LON), false);
});

test('isDaytime en hiver (CET) : nuit à 17h45 le 21 décembre', () => {
  assert.equal(isDaytime('2026-12-21T12:00', 3600, LAT, LON), true);
  assert.equal(isDaytime('2026-12-21T17:45', 3600, LAT, LON), false);
});
