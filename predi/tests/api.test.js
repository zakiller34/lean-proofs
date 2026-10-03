import { test } from 'node:test';
import assert from 'node:assert/strict';
import { buildForecastUrl, fetchForecast, parseForecast } from '../src/api/openMeteo.js';
import { makePayload } from './helpers.js';

const SPEC_URL =
  'https://api.open-meteo.com/v1/meteofrance?latitude=43.627&longitude=3.860&hourly=precipitation_probability&minutely_15=temperature_2m,relative_humidity_2m,wind_speed_10m,precipitation,weathercode&timezone=Europe%2FParis&forecast_days=1';

test('buildForecastUrl produit exactement la requête de la spécification', () => {
  assert.equal(buildForecastUrl(), SPEC_URL);
});

test('parseForecast normalise les créneaux et associe la probabilité horaire', () => {
  const { slots, utcOffsetSeconds } = parseForecast(makePayload());
  assert.equal(utcOffsetSeconds, 7200);
  assert.equal(slots.length, 96);
  assert.deepEqual(slots[5], {
    time: '2026-10-03T01:15',
    temperature: 15.5,
    humidity: 70,
    windSpeed: 12.4,
    precipitation: 0,
    weatherCode: 2,
    precipitationProbability: 5,
  });
});

test('parseForecast tolère les valeurs nulles, absentes et la clé weather_code', () => {
  const payload = makePayload({ count: 2 });
  payload.minutely_15.temperature_2m = [null, 'x'];
  delete payload.minutely_15.weathercode;
  payload.minutely_15.weather_code = [61, null];
  delete payload.hourly;
  const { slots } = parseForecast(payload);
  assert.equal(slots[0].temperature, null);
  assert.equal(slots[1].temperature, null);
  assert.equal(slots[0].weatherCode, 61);
  assert.equal(slots[1].weatherCode, null);
  assert.equal(slots[0].precipitationProbability, null);
});

test('parseForecast rejette un payload sans données 15 min', () => {
  assert.throws(() => parseForecast({}), /invalide/);
  assert.throws(() => parseForecast({ minutely_15: { time: [] } }), /invalide/);
});

const fakeFetch = (status, body) => async (url) => {
  fakeFetch.lastUrl = url;
  return { ok: status >= 200 && status < 300, status, json: async () => body };
};

test('fetchForecast appelle l’URL de la spec et renvoie les données parsées', async () => {
  const data = await fetchForecast({ fetchImpl: fakeFetch(200, makePayload({ count: 4 })) });
  assert.equal(fakeFetch.lastUrl, SPEC_URL);
  assert.equal(data.slots.length, 4);
});

test('fetchForecast remonte le message d’erreur de l’API', async () => {
  await assert.rejects(
    fetchForecast({ fetchImpl: fakeFetch(400, { error: true, reason: 'Parameter invalide' }) }),
    /Parameter invalide/,
  );
  await assert.rejects(fetchForecast({ fetchImpl: fakeFetch(503, null) }), /HTTP 503/);
});
