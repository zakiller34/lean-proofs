import { test } from 'node:test';
import assert from 'node:assert/strict';
import { currentSlotIndex, forecastSlots, formatSlotTime, nowInParis } from '../src/utils/time.js';
import { parseForecast } from '../src/api/openMeteo.js';
import { makePayload, slot } from './helpers.js';

test('nowInParis convertit l’heure UTC en heure de Paris (été et hiver)', () => {
  assert.equal(nowInParis(new Date('2026-07-14T10:05:00Z')), '2026-07-14T12:05');
  assert.equal(nowInParis(new Date('2026-12-31T23:30:00Z')), '2027-01-01T00:30');
});

test('formatSlotTime', () => {
  assert.equal(formatSlotTime('2026-10-03T09:45'), '9h45');
  assert.equal(formatSlotTime('2026-10-03T00:00'), '0h00');
});

test('currentSlotIndex trouve le créneau en cours', () => {
  const slots = ['10:00', '10:15', '10:30'].map((t) => slot(`2026-10-03T${t}`));
  assert.equal(currentSlotIndex(slots, '2026-10-03T10:20'), 1);
  assert.equal(currentSlotIndex(slots, '2026-10-03T10:15'), 1);
  assert.equal(currentSlotIndex(slots, '2026-10-03T09:00'), -1);
  assert.equal(currentSlotIndex(slots, '2026-10-03T23:00'), 2);
});

test('forecastSlots au pas de 15 min : créneaux futurs, limités', () => {
  const { slots } = parseForecast(makePayload());
  const out = forecastSlots(slots, '2026-10-03T14:20', 15, 4);
  assert.deepEqual(
    out.map((s) => s.time.slice(11)),
    ['14:30', '14:45', '15:00', '15:15'],
  );
});

test('forecastSlots au pas de 30 min : alignement sur :00/:30 et agrégation', () => {
  const slots = [
    slot('2026-10-03T14:15', { precipitation: 0.3, weatherCode: 61 }),
    slot('2026-10-03T14:30', { precipitation: 0.5, weatherCode: 3 }),
    slot('2026-10-03T14:45', { precipitation: null, weatherCode: null }),
    slot('2026-10-03T15:00', { precipitation: null, weatherCode: 2 }),
    slot('2026-10-03T15:15'),
  ];
  const out = forecastSlots(slots, '2026-10-03T14:10', 30, 10);
  assert.deepEqual(out.map((s) => s.time.slice(11)), ['14:30', '15:00']);
  assert.equal(out[0].precipitation, 0.8);
  assert.equal(out[0].weatherCode, 61);
  assert.equal(out[1].precipitation, null);
  assert.equal(out[1].weatherCode, 2);
});

test('forecastSlots renvoie une liste vide en fin de journée', () => {
  const { slots } = parseForecast(makePayload());
  assert.deepEqual(forecastSlots(slots, '2026-10-03T23:50', 30, 12), []);
});
