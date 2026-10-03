// Liste des prochains créneaux (pas de 15 ou 30 min).
import { WeatherIcon } from './WeatherIcon.js';
import { formatSlotTime } from '../utils/time.js';
import { formatPrecip, formatTemp, isWet } from '../utils/format.js';

function item(slot) {
  const { weather } = slot;
  const rain = isWet(slot.precipitation)
    ? `<span class="slot__rain">${formatPrecip(slot.precipitation)}</span>`
    : '<span class="slot__rain slot__rain--dry" aria-hidden="true">·</span>';
  return `
    <li class="slot">
      <time class="slot__time" datetime="${slot.time}">${formatSlotTime(slot.time)}</time>
      ${WeatherIcon(weather.icon, { size: 36, label: weather.label })}
      <span class="slot__label">${weather.label}</span>
      <span class="slot__temp">${formatTemp(slot.temperature)}</span>
      ${rain}
    </li>`;
}

export function ForecastList(slots, step) {
  const body = slots.length
    ? `<ol class="forecast__list">${slots.map(item).join('')}</ol>`
    : '<p class="forecast__empty">Fin de la prévision du jour.</p>';
  return `
    <section class="forecast" aria-labelledby="forecast-title">
      <h2 id="forecast-title" class="forecast__title">Prochaines heures <span>· pas de ${step} min</span></h2>
      ${body}
    </section>`;
}
