// Fabrique un payload Open-Meteo réaliste (créneaux de 15 min à partir de `start`).
export function makePayload({ start = '2026-10-03T00:00', count = 96, overrides = {} } = {}) {
  const [date, clock] = start.split('T');
  const [h0, m0] = clock.split(':').map(Number);
  const time = Array.from({ length: count }, (_, i) => {
    const total = h0 * 60 + m0 + i * 15;
    const hh = String(Math.floor(total / 60)).padStart(2, '0');
    const mm = String(total % 60).padStart(2, '0');
    return `${date}T${hh}:${mm}`;
  });
  const hours = [...new Set(time.map((t) => `${t.slice(0, 13)}:00`))];
  return {
    latitude: 43.62,
    longitude: 3.86,
    utc_offset_seconds: 7200,
    timezone: 'Europe/Paris',
    hourly: { time: hours, precipitation_probability: hours.map((_, i) => (i * 5) % 100) },
    minutely_15: {
      time,
      temperature_2m: time.map((_, i) => 15 + i * 0.1),
      relative_humidity_2m: time.map(() => 70),
      wind_speed_10m: time.map(() => 12.4),
      precipitation: time.map(() => 0),
      weathercode: time.map(() => 2),
      ...overrides,
    },
  };
}

export const slot = (time, extra = {}) => ({
  time,
  temperature: 18,
  humidity: 60,
  windSpeed: 10,
  precipitation: 0,
  weatherCode: 0,
  precipitationProbability: null,
  ...extra,
});
