/*
 * Pitié app logic.
 * Single IIFE namespace — nothing here touches `window` except the final
 * `window.PitieApp` export, so this script can share a page with other
 * scripts (its own copies of chart instances, taxonomies, etc. never
 * collide with a host page's globals).
 *
 * Requires (loaded before this file, in this order): Fuse.js, PapaParse,
 * D3 v7, Chart.js, Plotly, lodash, mathjs, MapLibre and
 * assets/css/theme.css linked in <head> (chart colors are read from its
 * --pitie-chart-* custom properties at init time).
 *
 * To reuse on another site: change CONFIG below (data URLs, thresholds),
 * keep the .pitie-app wrapper + the DOM ids this file references.
 */
(function () {
    'use strict';

    // ---- Config -------------------------------------------------------
    const CONFIG = {
        csvUrl: 'https://raw.githubusercontent.com/Sidam31/ICA-APHP/refs/heads/main/Data/Relev%C3%A9s%20PIT%20-%20csv_export.csv',
        empireMapUrl: 'Data/empire_1811_departements.json',
        quartierGeoUrl: 'Data/quartier_paris.geojson',
        streetsJsonUrl: 'https://sidam31.github.io/Outils-genealogiques/assets/data/rues-paris-lazare-1844.json',
        targetEntries: 45000,
        dataYearRange: [1809, 1860],
        maxResultsShown: 200,
        fuzzyThreshold: 0.4,
        advancedStatsRetry: { maxAttempts: 10, delayMs: 1000 }
    };

    const SEARCH_CRITERIA = [
        { id: 'nom', key: 'NOM' },
        { id: 'prenom', key: 'Prénoms' },
        { id: 'date-deces', key: 'Date de décès' },
        { id: 'LieuNaissance', key: 'Lieu de naissance' }
    ];

    // ---- State ----------------------------------------------------------
    let dbData = [];
    let filteredData = [];
    let currentFilters = { sex: '', age: '', department: '', cause: '' };
    let fuseIndexes = {};
    const charts = {}; // Chart.js instances, by key
    let ADVANCED_DATA = [];
    let advancedStatsLoaded = false;
    let advancedStatsRetryCount = 0;
    let PALETTE = null;
    let parisStreets = [];
    let exactStreetLookup = null; // Map<normalized name/variant, street>
    let quartierInfo = new Map(); // Map<quart number, { nom, arr }> — the 48 quartiers of 1811-1849
    let domicileMatchByRow = null; // WeakMap<row, matchResult> — built once, reused across filter changes
    let parisMapInstance = null; // MapLibre GL instance, created once and reused across filter changes

    // ---- DA / theme -------------------------------------------------------
    // Reads the design tokens declared in assets/css/theme.css so chart
    // colors stay derived from the DA instead of being separate hardcoded
    // hex arrays scattered through this file.
    function readPalette() {
        const cs = getComputedStyle(document.documentElement);
        const v = (name) => cs.getPropertyValue(name).trim();
        return {
            s1: v('--pitie-chart-s1'),
            s2: v('--pitie-chart-s2'),
            other: v('--pitie-chart-other'),
            sequential: Array.from({ length: 7 }, (_, i) => v(`--pitie-chart-seq-${i + 1}`)),
            male: v('--pitie-chart-s1'),
            female: v('--pitie-chart-s2'),
            maleShades: [1, 2, 3].map((i) => v(`--pitie-chart-male-${i}`)),
            femaleShades: [1, 2, 3].map((i) => v(`--pitie-chart-female-${i}`)),
            bandFill: v('--pitie-chart-band-fill'),
            ink: v('--pitie-chart-ink'),
            ink2: v('--pitie-chart-ink-2'),
            muted: v('--pitie-chart-muted'),
            grid: v('--pitie-chart-grid'),
            axis: v('--pitie-chart-axis'),
            sea: v('--pitie-chart-sea'),
            mapEmpty: v('--pitie-map-empty'),
            mapForeign: v('--pitie-map-foreign'),
            mapStroke: v('--pitie-map-stroke'),
            brand: v('--pitie-blue')
        };
    }

    // ---- Helpers ----------------------------------------------------------
    function capitalizeFirstLetter(val) {
        return String(val).charAt(0).toUpperCase() + String(val).slice(1);
    }

    // Combining diacritical marks (U+0300-U+036F), stripped after NFD
    // normalization to remove accents while keeping base letters.
    const DIACRITICS_RE = new RegExp('[' + String.fromCharCode(0x0300) + '-' + String.fromCharCode(0x036f) + ']', 'g');

    function stripAccents(str) {
        return str.normalize('NFD').replace(DIACRITICS_RE, '');
    }

    // ---- Chart helpers ----------------------------------------------------
    const MONTH_NAMES = ['Jan', 'Fév', 'Mar', 'Avr', 'Mai', 'Juin', 'Juil', 'Aoû', 'Sep', 'Oct', 'Nov', 'Déc'];
    // Years with fewer indexed entries than this are left out of the time charts:
    // they are partially transcribed registers, so their "zeros" are missing data, not absence of deaths.
    const MIN_YEAR_ENTRIES = 100;
    const FONT = "'Inter', sans-serif";

    const fmtInt = (n) => Math.round(n).toLocaleString('fr-FR');
    const fmtPct = (n, digits = 1) => n.toLocaleString('fr-FR', { minimumFractionDigits: digits, maximumFractionDigits: digits }) + ' %';

    function median(values) {
        if (!values.length) return null;
        const v = [...values].sort((a, b) => a - b);
        const mid = Math.floor(v.length / 2);
        return v.length % 2 ? v[mid] : (v[mid - 1] + v[mid]) / 2;
    }

    // "64", "18,5", "21  1/2", "6 mois", "1 jour" -> years (null when unreadable)
    function parseAge(raw) {
        if (raw === undefined || raw === null) return null;
        const s = String(raw).trim().toLowerCase().replace(',', '.');
        if (!s) return null;
        const m = s.match(/^(\d+(?:\.\d+)?)(?:\s+(\d+)\/(\d+))?/);
        if (!m) return null;
        let age = parseFloat(m[1]);
        if (m[2] && m[3] && Number(m[3]) > 0) age += Number(m[2]) / Number(m[3]);
        if (/mois/.test(s)) age /= 12;
        else if (/semaine/.test(s)) age /= 52;
        else if (/jour/.test(s)) age = 0;
        return age >= 0 && age <= 110 ? age : null;
    }

    // Groups spellings that only differ by case / accents / spacing; the label shown is the
    // most frequent spelling. Returns [[label, count], ...] sorted by count.
    function tallyLabels(values) {
        const groups = new Map();
        values.forEach((raw) => {
            const key = stripAccents(raw.toLowerCase()).replace(/\s+/g, ' ');
            let g = groups.get(key);
            if (!g) { g = { n: 0, spellings: new Map() }; groups.set(key, g); }
            g.n++;
            g.spellings.set(raw, (g.spellings.get(raw) || 0) + 1);
        });
        return [...groups.values()]
            .map((g) => [capitalizeFirstLetter([...g.spellings.entries()].sort((a, b) => b[1] - a[1])[0][0]), g.n])
            .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0], 'fr'));
    }

    function applyChartDefaults() {
        Chart.defaults.font.family = FONT;
        Chart.defaults.font.size = 12;
        Chart.defaults.color = PALETTE.ink2;
        Chart.defaults.borderColor = PALETTE.grid;
        Chart.defaults.plugins.legend.labels.boxWidth = 12;
        Chart.defaults.plugins.legend.labels.boxHeight = 12;
    }

    // Value written at the end of a horizontal bar (only for the bars `format` returns text for).
    const endLabelsPlugin = {
        id: 'endLabels',
        afterDatasetsDraw(chart, args, opts) {
            if (!opts || typeof opts.format !== 'function') return;
            const { ctx } = chart;
            ctx.save();
            ctx.font = `500 11px ${FONT}`;
            ctx.fillStyle = PALETTE.ink2;
            ctx.textBaseline = 'middle';
            chart.getDatasetMeta(0).data.forEach((bar, i) => {
                const text = opts.format(chart.data.datasets[0].data[i], i);
                if (text) ctx.fillText(text, bar.x + 6, bar.y);
            });
            ctx.restore();
        }
    };

    const baseScales = (extraX = {}) => ({
        x: Object.assign({ beginAtZero: true, grid: { color: PALETTE.grid }, border: { display: false }, ticks: { callback: (v) => fmtInt(v) } }, extraX),
        y: {
            grid: { display: false },
            border: { color: PALETTE.axis },
            ticks: {
                autoSkip: false,
                callback(v) {
                    const l = String(this.getLabelForValue(v));
                    return l.length > 34 ? l.slice(0, 33) + '…' : l;
                }
            }
        }
    });

    // Ranked horizontal bars (one colour; optional muted "other" bar). entries: [[label, n], ...]
    function drawRankedBars(key, canvasId, entries, { total, otherIndex = -1, unit = 'décès', labelFormat } = {}) {
        const canvas = document.getElementById(canvasId);
        if (!canvas) return;
        if (charts[key]) charts[key].destroy();
        const values = entries.map((e) => e[1]);
        const pct = (n) => (total ? fmtPct((n / total) * 100) : '');
        charts[key] = new Chart(canvas.getContext('2d'), {
            type: 'bar',
            data: {
                labels: entries.map((e) => e[0]),
                datasets: [{
                    data: values,
                    backgroundColor: values.map((_, i) => (i === otherIndex ? PALETTE.other : PALETTE.s1)),
                    borderRadius: 4,
                    borderSkipped: 'start',
                    barPercentage: 0.7,
                    categoryPercentage: 1
                }]
            },
            options: {
                indexAxis: 'y',
                responsive: true,
                maintainAspectRatio: false,
                layout: { padding: { right: 96 } },
                plugins: {
                    legend: { display: false },
                    tooltip: { callbacks: { label: (c) => `${fmtInt(c.raw)} ${unit}${total ? ` (${pct(c.raw)})` : ''}` } },
                    endLabels: { format: labelFormat || ((v) => (total ? `${fmtInt(v)} · ${pct(v)}` : fmtInt(v))) }
                },
                scales: baseScales()
            },
            plugins: [endLabelsPlugin]
        });
    }

    // Keeps the `k` biggest entries and folds the rest into one "other" entry.
    function topWithOther(entries, k, otherLabel) {
        const top = entries.slice(0, k);
        const rest = entries.slice(k).reduce((s, e) => s + e[1], 0);
        return { top, rest, list: rest > 0 ? [...top, [otherLabel, rest]] : top };
    }

    function setNote(id, text) {
        const el = document.getElementById(id);
        if (el) el.textContent = text;
    }

    // Table twin of a chart: every value stays reachable without hover or colour.
    function setTableView(anchorId, viewId, headers, rows) {
        const anchor = document.getElementById(anchorId);
        const host = anchor && anchor.closest('.big-stat-card');
        if (!host) return;
        let d = host.querySelector(`details[data-view="${viewId}"]`);
        if (!d) {
            d = document.createElement('details');
            d.className = 'viz-table';
            d.dataset.view = viewId;
            host.appendChild(d);
        }
        const head = headers.map((h) => `<th>${escapeHtml(h)}</th>`).join('');
        const body = rows.map((r) => `<tr>${r.map((c) => `<td>${escapeHtml(c)}</td>`).join('')}</tr>`).join('');
        d.innerHTML = `<summary>Voir les données (tableau)</summary><div class="viz-table-scroll"><table><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
    }

    const PLOTLY_CONFIG = { responsive: true, displaylogo: false, modeBarButtonsToRemove: ['lasso2d', 'select2d', 'autoScale2d', 'toggleSpikelines'] };

    function plotlyLayout(extra) {
        const axis = { gridcolor: PALETTE.grid, linecolor: PALETTE.axis, zerolinecolor: PALETTE.axis, tickcolor: PALETTE.axis, automargin: true };
        return _.merge({
            font: { family: FONT, size: 12, color: PALETTE.ink2 },
            paper_bgcolor: 'rgba(0,0,0,0)',
            plot_bgcolor: 'rgba(0,0,0,0)',
            margin: { t: 16, r: 16, b: 48, l: 56 },
            xaxis: Object.assign({}, axis),
            yaxis: Object.assign({}, axis),
            hoverlabel: { font: { family: FONT, size: 12 } }
        }, extra);
    }

    // One-hue sequential colorscale for Plotly; an exact zero stays neutral so "0" never reads as "a little".
    function sequentialColorscale() {
        const seq = PALETTE.sequential;
        return [[0, '#f1f0eb'], [0.0001, seq[0]]].concat(seq.slice(1).map((c, i) => [(i + 1) / (seq.length - 1), c]));
    }

    // ---- Data loading -------------------------------------------------------
    function loadCSVData() {
        Papa.parse(CONFIG.csvUrl, {
            download: true,
            header: true,
            skipEmptyLines: true,
            complete: function (results) {
                dbData = results.data;
                filteredData = [...dbData];
                console.info(`${dbData.length} entrées chargées depuis le CSV`);
                buildFuseIndexes();
                populateFilterDropdowns();
                maybeBuildDomicileMatches();
                updateStatistics();
            },
            error: function (error) {
                console.error('Erreur lors du chargement du CSV:', error);
                document.getElementById('search-results').innerHTML =
                    '<p class="text-center" style="color: var(--pitie-danger);">Erreur de chargement de la base de données. Veuillez réessayer plus tard.</p>';
            }
        });
    }

    // Loaded independently of the CSV (different source, no reason to block on
    // each other) — whichever of the two finishes last triggers the domicile
    // matching pass, see maybeBuildDomicileMatches().
    function loadParisStreetsData() {
        fetch(CONFIG.streetsJsonUrl)
            .then((response) => response.json())
            .then((json) => {
                parisStreets = json.streets || [];
                // Plain exact-match index (name + variants) rather than a Fuse
                // fuzzy index: benchmarked against the real dataset, a Fuse
                // search per row (even deduplicated, even with a tightened
                // distance) took minutes and froze the page — a fuzzy pass
                // over 2500+ streets just isn't cheap enough to do per-row.
                // Unmatched streets are logged (like the department fix) for
                // manual alias cleanup instead of guessed at automatically.
                exactStreetLookup = new Map();
                parisStreets.forEach((s) => {
                    if (!exactStreetLookup.has(s.name.toLowerCase())) exactStreetLookup.set(s.name.toLowerCase(), s);
                    (s.variants || []).forEach((v) => {
                        if (!exactStreetLookup.has(v.toLowerCase())) exactStreetLookup.set(v.toLowerCase(), s);
                    });
                    // Former names (pre-1844 renames, Revolutionary-era names from
                    // Lacombe) — deaths recorded in 1809-1860 can predate a rename.
                    (s.ancien_noms || []).forEach((an) => {
                        if (an.nom && !exactStreetLookup.has(an.nom.toLowerCase())) {
                            exactStreetLookup.set(an.nom.toLowerCase(), s);
                        }
                    });
                    if (s.quart != null && !quartierInfo.has(s.quart)) {
                        quartierInfo.set(s.quart, { nom: s.quartier, arr: s.arr });
                    }
                });
                maybeBuildDomicileMatches();
                updateStatistics();
            })
            .catch((error) => {
                console.error('Erreur lors du chargement des rues de Paris:', error);
            });
    }

    // Built once when the dataset loads, reused for every search — avoids
    // rebuilding a Fuse index per field on every submit.
    function buildFuseIndexes() {
        fuseIndexes = {};
        SEARCH_CRITERIA.forEach((criterion) => {
            fuseIndexes[criterion.key] = new Fuse(dbData, {
                keys: [criterion.key],
                threshold: CONFIG.fuzzyThreshold,
                includeScore: true
            });
        });
    }

    function populateFilterDropdowns() {
        const departments = new Set();
        dbData.forEach((row) => {
            const birthplace = row['Lieu de naissance'];
            const historicalDept = extractHistoricalDeptRaw(birthplace);
            if (historicalDept) {
                departments.add(stripAccents(historicalDept));
            }
        });
        const deptSelect = document.getElementById('filter-department');
        Array.from(departments).sort().forEach((dept) => {
            const option = document.createElement('option');
            option.value = dept;
            option.textContent = dept;
            deptSelect.appendChild(option);
        });

        const causes = new Set();
        dbData.forEach((row) => {
            const cause = row['Cause de mort: espèce'] ? capitalizeFirstLetter(row['Cause de mort: espèce'].trim()) : 'N/C';
            if (cause && cause.trim()) {
                causes.add(stripAccents(cause.trim()));
            }
        });
        const causeSelect = document.getElementById('filter-cause');
        Array.from(causes).sort().forEach((cause) => {
            const option = document.createElement('option');
            option.value = cause;
            option.textContent = cause;
            causeSelect.appendChild(option);
        });
    }

    // ---- Filters --------------------------------------------------------
    function applyFilters() {
        currentFilters.sex = document.getElementById('filter-sex').value;
        currentFilters.age = document.getElementById('filter-age').value;
        currentFilters.department = document.getElementById('filter-department').value;
        currentFilters.cause = document.getElementById('filter-cause').value;

        filteredData = dbData.filter((row) => {
            if (currentFilters.sex && row['Sexe'] !== currentFilters.sex) {
                return false;
            }

            if (currentFilters.age) {
                const parsed = parseAge(row['Âge']);
                if (parsed === null) return false;
                const age = Math.floor(parsed); // 10,5 ans belongs to "0-10", not to the gap between bands
                const [min, max] = currentFilters.age.includes('+')
                    ? [81, 200]
                    : currentFilters.age.split('-').map(Number);
                if (age < min || age > max) {
                    return false;
                }
            }

            if (currentFilters.department) {
                const birthplace = row['Lieu de naissance'].trim();
                if (!birthplace) return false;
                const historicalDept = extractHistoricalDeptRaw(birthplace);
                if (!historicalDept || stripAccents(historicalDept) !== currentFilters.department) {
                    return false;
                }
            }

            if (currentFilters.cause) {
                const cause = row['Cause de mort: espèce'].trim();
                if (!cause || capitalizeFirstLetter(stripAccents(cause)) !== currentFilters.cause) {
                    return false;
                }
            }

            return true;
        });

        updateActiveFiltersDisplay();
        updateStatistics();
        refreshAdvancedStats();
    }

    function resetFilters() {
        document.getElementById('filter-sex').value = '';
        document.getElementById('filter-age').value = '';
        document.getElementById('filter-department').value = '';
        document.getElementById('filter-cause').value = '';
        currentFilters = { sex: '', age: '', department: '', cause: '' };
        filteredData = [...dbData];
        updateActiveFiltersDisplay();
        updateStatistics();
        refreshAdvancedStats();
    }

    function updateActiveFiltersDisplay() {
        const activeFiltersDiv = document.getElementById('active-filters');
        const filterTagsDiv = document.getElementById('filter-tags');

        const hasFilters = Object.values(currentFilters).some((val) => val !== '');

        if (!hasFilters) {
            activeFiltersDiv.style.display = 'none';
            return;
        }

        activeFiltersDiv.style.display = 'block';
        filterTagsDiv.innerHTML = '';

        const addTag = (text) => {
            const tag = document.createElement('span');
            tag.className = 'filter-tag';
            tag.textContent = text;
            filterTagsDiv.appendChild(tag);
        };

        if (currentFilters.sex) addTag(`Sexe: ${currentFilters.sex === 'M' ? 'Hommes' : 'Femmes'}`);
        if (currentFilters.age) addTag(`Âge: ${currentFilters.age} ans`);
        if (currentFilters.department) addTag(`Département: ${currentFilters.department}`);
        if (currentFilters.cause) addTag(`Cause: ${currentFilters.cause}`);
    }

    // ---- Basic stats & charts -------------------------------------------
    function updateStatistics() {
        if (filteredData.length > 0) {
            document.getElementById('total-entries').textContent = filteredData.length.toLocaleString('fr-FR');

            const completionRate = Math.min(100, (dbData.length / CONFIG.targetEntries) * 100);
            document.getElementById('completion-rate').textContent = completionRate.toFixed(1) + '%';

            generateSurnameChart(filteredData);
            generateAgeHistogram(filteredData);
            generateCausesChart(filteredData);
            generateProfChart(filteredData);
            generateDepartChart(filteredData);
            generateDomicileStats(filteredData);
        }
    }

    function generateSurnameChart(data) {
        const names = data.map((row) => (row['NOM'] || '').trim().toUpperCase()).filter(Boolean);
        const ranked = tallyLabels(names).map(([label, n]) => [label.toUpperCase(), n]);
        const top = ranked.slice(0, 20);

        document.getElementById('word-cloud-title').textContent = `Les ${top.length} noms de famille les plus fréquents`;
        drawRankedBars('surnames', 'surname-chart', top, { total: names.length, unit: 'défunts' });
        setTableView('surname-chart', 'surnames', ['Nom', 'Défunts', 'Part'],
            top.map(([l, n]) => [l, fmtInt(n), fmtPct((n / names.length) * 100)]));
    }

    function generateCausesChart(data) {
        const causes = data
            .map((row) => (row['Cause de mort: espèce'] || '').trim().replace(/\s+/g, ' '))
            .filter((c) => c && c.toLowerCase() !== 'n/c');
        const ranked = tallyLabels(causes);
        const { top, rest } = topWithOther(ranked, 15, 'Autres');
        const topShare = causes.length ? ((causes.length - rest) / causes.length) * 100 : 0;

        setNote('causes-summary',
            `${fmtInt(causes.length)} décès avec une cause indiquée, ${fmtInt(ranked.length)} formulations différentes. ` +
            `Les 15 premières couvrent ${fmtPct(topShare, 0)} des décès, les ${fmtInt(ranked.length - 15)} autres formulations se partagent le reste ` +
            `(« phtisie » et « phtisie pulmonaire » sont comptées séparément, comme écrit dans le registre).`);
        drawRankedBars('causes', 'causes-chart', top, { total: causes.length });
        setTableView('causes-chart', 'causes', ['Cause', 'Décès', 'Part'],
            ranked.slice(0, 40).map(([l, n]) => [l, fmtInt(n), fmtPct((n / causes.length) * 100)]));
    }

    // Spelling / gender variants folded together so that "Journalière" and "Journalier" count once.
    const PROFESSION_GROUPS = [
        [/^journali[eè]re?/i, 'Journalier.e'],
        [/^ouvri[eè]re?/i, 'Ouvrier.e'],
        [/^coutur/i, 'Couturier.e'],
        [/^tailleu(r|se)$/i, 'Tailleur.se'],
        [/^porteu(r|se) d'eau/i, "Porteur.se d'eau"],
        [/^(soldat|militaire|infanterie|fusilier|caporal|garde|dragon|cavalier|chasseur|artilleur|voltigeur)/i, 'Militaire'],
        [/^marchand/i, 'Marchand.e'],
        [/^agricult/i, 'Agriculteur.rice'],
        [/^revendeu/i, 'Revendeur.se']
    ];

    function normalizeProfession(raw) {
        const p = (raw || '').trim();
        if (!p || /^n\/c$/i.test(p) || /^sans [ée]tat$/i.test(p)) return null;
        const hit = PROFESSION_GROUPS.find(([re]) => re.test(p));
        return hit ? hit[1] : p;
    }

    function generateProfChart(data) {
        const jobs = data.map((row) => normalizeProfession(row['Profession'])).filter(Boolean);
        const ranked = tallyLabels(jobs);
        const { top, rest } = topWithOther(ranked, 15, 'Autres');
        const topShare = jobs.length ? ((jobs.length - rest) / jobs.length) * 100 : 0;

        setNote('prof-summary',
            `${fmtInt(jobs.length)} défunts avec une profession (hors « sans état »), ${fmtInt(ranked.length)} professions différentes. ` +
            `Les 15 premières couvrent ${fmtPct(topShare, 0)}, les autres se partagent le reste.`);
        drawRankedBars('professions', 'prof-chart', top, { total: jobs.length, unit: 'défunts' });
        setTableView('prof-chart', 'professions', ['Profession', 'Défunts', 'Part'],
            ranked.slice(0, 40).map(([l, n]) => [l, fmtInt(n), fmtPct((n / jobs.length) * 100)]));
    }

    function generateAgeHistogram(data) {
        const ages = { M: [], F: [] };
        data.forEach((row) => {
            const sex = row['Sexe'];
            if (sex !== 'M' && sex !== 'F') return;
            const age = parseAge(row['Âge']);
            if (age !== null) ages[sex].push(age);
        });

        const maxAge = Math.max(0, ...ages.M, ...ages.F);
        const binCount = Math.floor(maxAge / 5) + 1;
        const labels = Array.from({ length: binCount }, (_, i) => `${i * 5}–${i * 5 + 4}`);
        const bins = { M: Array(binCount).fill(0), F: Array(binCount).fill(0) };
        ['M', 'F'].forEach((sex) => ages[sex].forEach((a) => { bins[sex][Math.floor(a / 5)]++; }));

        const limit = Math.max(10, Math.ceil(Math.max(...bins.M, ...bins.F) / 50) * 50);
        const peak = (sex) => {
            const i = bins[sex].indexOf(Math.max(...bins[sex]));
            return `${labels[i]} ans (${fmtInt(bins[sex][i])})`;
        };
        const med = (sex) => (ages[sex].length ? `${fmtInt(median(ages[sex]))} ans` : '—');
        setNote('age-summary',
            `Âge médian : hommes ${med('M')} (n = ${fmtInt(ages.M.length)}), femmes ${med('F')} (n = ${fmtInt(ages.F.length)}). ` +
            `Classe la plus touchée : hommes ${ages.M.length ? peak('M') : '—'}, femmes ${ages.F.length ? peak('F') : '—'}.`);

        const canvas = document.getElementById('age-histogram-chart');
        if (charts.age) charts.age.destroy();
        const share = { M: ages.M.length, F: ages.F.length };
        charts.age = new Chart(canvas.getContext('2d'), {
            type: 'bar',
            data: {
                labels,
                datasets: [
                    { label: 'Hommes', data: bins.M.map((n) => -n), backgroundColor: PALETTE.male, borderRadius: 4, borderSkipped: 'start', barPercentage: 0.82, categoryPercentage: 1 },
                    { label: 'Femmes', data: bins.F, backgroundColor: PALETTE.female, borderRadius: 4, borderSkipped: 'start', barPercentage: 0.82, categoryPercentage: 1 }
                ]
            },
            options: {
                indexAxis: 'y',
                responsive: true,
                maintainAspectRatio: false,
                scales: {
                    x: { stacked: true, min: -limit, max: limit, grid: { color: PALETTE.grid }, border: { display: false }, ticks: { callback: (v) => fmtInt(Math.abs(v)) }, title: { display: true, text: 'Nombre de décès' } },
                    y: { stacked: true, reverse: true, grid: { display: false }, border: { color: PALETTE.axis }, ticks: { autoSkip: false }, title: { display: true, text: 'Âge au décès (ans)' } }
                },
                plugins: {
                    legend: { position: 'top' },
                    tooltip: {
                        callbacks: {
                            title: (items) => `${items[0].label} ans`,
                            label: (c) => {
                                const sex = c.datasetIndex === 0 ? 'M' : 'F';
                                const n = Math.abs(c.raw);
                                return `${c.dataset.label} : ${fmtInt(n)} (${fmtPct((n / share[sex]) * 100)} des ${sex === 'M' ? 'hommes' : 'femmes'})`;
                            }
                        }
                    }
                }
            }
        });

        setTableView('age-histogram-chart', 'age', ['Âge (ans)', 'Hommes', 'Femmes'],
            labels.map((l, i) => [l, fmtInt(bins.M[i]), fmtInt(bins.F[i])]));
    }

    // Revolutionary-era department names -> modern INSEE codes.
    const HISTORICAL_TO_MODERN_DEPTS = {
        'Ain': '01', 'Aisne': '02', 'Allier': '03', 'Basses-Alpes': '04', 'Hautes-Alpes': '05',
        'Alpes-Maritimes': '06', 'Ardèche': '07', 'Ardennes': '08', 'Ariège': '09', 'Aube': '10',
        'Aude': '11', 'Aveyron': '12', 'Bouches-du-Rhône': '13', 'Calvados': '14', 'Cantal': '15',
        'Charente': '16', 'Charente-Inférieure': '17', 'Cher': '18', 'Corrèze': '19', 'Corse': '2A',
        'Corse-du-Sud': '2B', "Côte-d'Or": '21', 'Côtes-du-Nord': '22', 'Creuse': '23', 'Dordogne': '24',
        'Doubs': '25', 'Drôme': '26', 'Eure': '27', 'Eure-et-Loir': '28', 'Finistère': '29',
        'Gard': '30', 'Haute-Garonne': '31', 'Gers': '32', 'Gironde': '33', 'Hérault': '34',
        'Ille-et-Vilaine': '35', 'Indre': '36', 'Indre-et-Loire': '37', 'Isère': '38', 'Jura': '39',
        'Landes': '40', 'Loir-et-Cher': '41', 'Loire': '42', 'Haute-Loire': '43', 'Loire-Inférieure': '44',
        'Loiret': '45', 'Lot': '46', 'Lot-et-Garonne': '47', 'Lozère': '48', 'Maine-et-Loire': '49',
        'Manche': '50', 'Marne': '51', 'Haute-Marne': '52', 'Mayenne': '53', 'Meurthe': '54',
        'Meuse': '55', 'Morbihan': '56', 'Moselle': '57', 'Nièvre': '58', 'Nord': '59',
        'Oise': '60', 'Orne': '61', 'Pas-de-Calais': '62', 'Puy-de-Dôme': '63', 'Basses-Pyrénées': '64',
        'Hautes-Pyrénées': '65', 'Pyrénées-Orientales': '66', 'Bas-Rhin': '67', 'Haut-Rhin': '68', 'Rhône': '69',
        'Haute-Saône': '70', 'Saône-et-Loire': '71', 'Sarthe': '72', 'Mont-Blanc': '73', 'Léman': '74',
        'Seine': '75', 'Seine-Inférieure': '76', 'Seine-et-Marne': '77', 'Seine-et-Oise': '78', 'Deux-Sèvres': '79',
        'Somme': '80', 'Tarn': '81', 'Tarn-et-Garonne': '82', 'Var': '83', 'Vaucluse': '84',
        'Vendée': '85', 'Vienne': '86', 'Haute-Vienne': '87', 'Vosges': '88', 'Yonne': '89',
        'Territoire de Belfort': '90', 'Essonne': '91', 'Hauts-de-Seine': '92', 'Seine-Saint-Denis': '93', 'Val-de-Marne': '94',
        "Val-d'Oise": '95',
        'Dyle': 'B01', 'Brabant Flamand': 'B02', 'Jemappes': 'B03', 'Escaut': 'B04', 'Meuse-Inférieure': 'B05',
        'Sambre-et-Meuse': 'B06', 'Forêts': 'B07', 'Lys': 'B08', 'Deux-Nèthes': 'B09', 'Ourthe': 'B10',
        'Brabant': 'B11'
    };

    // The register spells the same department several ways ("Seine et Oise" /
    // "Seine-et-Oise" / "Seine-inférieure" vs "Seine-Inférieure"...). Folding
    // whitespace to hyphens and lower-casing before lookup collapses almost
    // all of that onto the canonical keys above.
    function normalizeHistoricalDeptKey(name) {
        return name.trim().replace(/\s+/g, '-').replace(/-+/g, '-').toLowerCase();
    }

    // Transcription variants/typos that survive normalizeHistoricalDeptKey()
    // but still don't match their canonical dictionary key letter-for-letter.
    const HISTORICAL_DEPT_ALIASES = {
        'eure-et-loire': 'eure-et-loir', // "Eure et Loire" — official name is "Eure-et-Loir"
        'côtes-de-nord': 'côtes-du-nord', // "de" typo'd for "du"
        'seine-oise': 'seine-et-oise' // "et" dropped
    };

    const NORMALIZED_HISTORICAL_DEPTS = new Map(
        Object.entries(HISTORICAL_TO_MODERN_DEPTS).map(([name, code]) => [normalizeHistoricalDeptKey(name), code])
    );

    function resolveModernDeptCode(historicalDept) {
        const key = normalizeHistoricalDeptKey(historicalDept);
        return NORMALIZED_HISTORICAL_DEPTS.get(HISTORICAL_DEPT_ALIASES[key] || key);
    }

    // "Lieu de naissance" is "Commune (Département)", but some rows have an
    // illegible/placeholder first parenthetical ("...", "???") ahead of the
    // real one, or append a "{Commune (ModernName)}" transcriber's aside.
    // Braces are dropped and the last non-placeholder top-level parenthetical
    // is taken as the department.
    function extractHistoricalDeptRaw(birthplace) {
        if (!birthplace) return null;
        const withoutAsides = birthplace.replace(/\{[^}]*\}/g, '');
        const matches = withoutAsides.match(/\(([^)]*)\)/g) || [];
        for (let i = matches.length - 1; i >= 0; i--) {
            const candidate = matches[i].slice(1, -1).trim().replace(/[.,;]+$/, '');
            if (candidate && !/^[.?…]+$/.test(candidate)) {
                return candidate;
            }
        }
        return null;
    }

    // ---- Birthplace map: departments of the French Empire (1811) -------------
    // The register records the department as it was in 1809-1825, so the map is the 1811
    // empire (130 departments, Belgium, Rhineland, Netherlands and Italy included) instead of
    // today's France. Geometry comes from Data/empire_1811_departements.json
    // (built by scripts/build_empire_map.py from the Wikimedia SVG, one path per department).
    let empireData = null;
    let empireIndex = null; // normalized name -> { id, name, country, kind }
    let empirePromise = null;

    const empireKey = (s) => stripAccents(String(s)).toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '');

    // Transcription variants, modern names and areas that no longer exist -> 1811 department or state.
    const EMPIRE_ALIASES = {
        'dyles': 'dyle', 'rhour': 'roer', 'moers': 'roer', 'nether': 'deux-nethes',
        'haute-seine': 'seine', 'hauts-de-la-seine': 'seine', 'seine-saint-denis': 'seine', 'val-de-marne': 'seine',
        'yvelines': 'seine-et-oise', 'essonne': 'seine-et-oise', 'val-d-oise': 'seine-et-oise', 'seine-oise': 'seine-et-oise',
        'ile-et-vilaine': 'ille-et-vilaine', 'ille-et-villaine': 'ille-et-vilaine', 'ile-et-villaine': 'ille-et-vilaine',
        'eure-et-loir': 'eure-et-loire', 'cotes-de-nord': 'cotes-du-nord',
        'loire-interieure': 'loire-inferieure', 'seine-interieure': 'seine-inferieure',
        'savoie': 'mont-blanc', 'haute-savoie': 'mont-blanc', 'evian': 'leman',
        'corse': 'golo', 'corse-du-sud': 'golo', 'haute-corse': 'golo',
        'mont-tonnere': 'mont-tonnerre', 'zuyder-zee': 'zuiderzee', 'bouche-de-l-escaut': 'bouches-de-l-escaut',
        'wirtembourg': 'wurtemberg', 'wirtemberg': 'wurtemberg', 'duche-de-bergaers': 'berg', 'duche-de-bad': 'bade',
        'magdebourg': 'westphalie',
        'canton-de-fribourg': 'suisse', 'canton-de-schafthausen': 'suisse', 'canton-de-neuchatel': 'suisse',
        'neuchatel': 'suisse', 'helvetie': 'suisse',
        'silesie': 'prusse', 'pomeranie': 'prusse', 'friesland': 'frise'
    };

    function buildEmpireIndex() {
        empireIndex = new Map();
        const add = (key, entry) => { if (!empireIndex.has(key)) empireIndex.set(key, entry); };
        empireData.depts.forEach((d) => {
            const entry = {
                id: d.group || d.label,
                name: d.group === 'corse' ? 'Corse' : d.name,
                country: d.group === 'corse' ? 'France' : d.country,
                kind: 'dept'
            };
            d.entry = entry;
            add(empireKey(d.label), entry);
            add(empireKey(d.name), entry);
        });
        empireData.states.forEach((s) => {
            s.entry = { id: 'state:' + s.label, name: s.name, country: 'États alliés ou voisins', kind: 'state' };
            add(empireKey(s.name), s.entry);
        });
    }

    function loadEmpireMap() {
        if (!empirePromise) {
            empirePromise = fetch(CONFIG.empireMapUrl)
                .then((response) => response.json())
                .then((json) => { empireData = json; buildEmpireIndex(); return json; });
        }
        return empirePromise;
    }

    function resolveEmpireEntry(rawDept) {
        if (!empireIndex || !rawDept) return null;
        const key = empireKey(rawDept);
        return empireIndex.get(EMPIRE_ALIASES[key] || key) || null;
    }

    // Name as it appears on the 1811 map (merges "Seine-inférieure" / "Seine-Inférieure"...).
    function canonicalDeptName(rawDept) {
        const entry = resolveEmpireEntry(rawDept);
        return entry ? entry.name : rawDept;
    }

    // Class lower bounds: 1 | 2-4 | 5-9 | 10-24 | 25-49 | 50-99 | 100+
    const BIRTH_BINS = [1, 2, 5, 10, 25, 50, 100];
    const birthBin = (n) => BIRTH_BINS.reduce((acc, b, i) => (n >= b ? i : acc), -1);
    const birthBinLabel = (i) => (i === BIRTH_BINS.length - 1 ? `${BIRTH_BINS[i]} et plus`
        : BIRTH_BINS[i + 1] - 1 === BIRTH_BINS[i] ? `${BIRTH_BINS[i]}` : `${BIRTH_BINS[i]} à ${BIRTH_BINS[i + 1] - 1}`);

    function generateDepartChart(data) {
        const container = document.getElementById('france-map');
        loadEmpireMap().then(() => {
            const counts = new Map(); // id -> { entry, n }
            const unresolved = new Map();
            let withPlace = 0;
            data.forEach((row) => {
                const raw = extractHistoricalDeptRaw(row['Lieu de naissance']);
                if (!raw) return;
                withPlace++;
                const entry = resolveEmpireEntry(raw);
                if (!entry) { unresolved.set(raw, (unresolved.get(raw) || 0) + 1); return; }
                const c = counts.get(entry.id) || { entry, n: 0 };
                c.n++;
                counts.set(entry.id, c);
            });
            if (unresolved.size > 0) {
                console.warn('Départements non placés sur la carte:', Array.from(unresolved.entries()).map(([k, v]) => `${k} (${v})`).join(', '));
            }
            drawEmpireMap(counts, withPlace, unresolved);
        }).catch((error) => {
            console.error('Erreur lors du chargement de la carte:', error);
            container.innerHTML = '<p style="color: var(--pitie-danger);">Erreur lors du chargement de la carte.</p>';
        });
    }

    function drawEmpireMap(counts, withPlace, unresolved) {
        const wrap = d3.select('#france-map');
        wrap.html('');
        const [vx, vy, vw, vh] = empireData.viewBox;
        const tr = (t) => `translate(${t[0]},${t[1]})`;
        const countOf = (entry) => (counts.get(entry.id) ? counts.get(entry.id).n : 0);
        const colorOf = (entry) => {
            const bin = birthBin(countOf(entry));
            return bin < 0 ? (entry.kind === 'dept' ? PALETTE.mapEmpty : PALETTE.mapForeign) : PALETTE.sequential[bin];
        };
        const located = Array.from(counts.values()).reduce((s, c) => s + c.n, 0);

        const svg = wrap.append('svg')
            .attr('viewBox', `${vx} ${vy} ${vw} ${vh}`)
            .attr('role', 'img')
            .attr('aria-label', `Carte des départements de l'Empire français en 1811, colorée selon le nombre de personnes décédées à la Pitié qui y sont nées. Le détail est dans le tableau sous la carte.`);
        svg.append('rect').attr('x', vx).attr('y', vy).attr('width', vw).attr('height', vh).attr('fill', PALETTE.sea);

        const tooltip = wrap.append('div').attr('class', 'map-tooltip');
        const node = wrap.node();
        const showTip = (event, entry) => {
            const n = countOf(entry);
            const where = entry.kind === 'state' ? 'État hors Empire' : (entry.country === 'France' ? 'France actuelle' : entry.country);
            tooltip.html(`<strong>${escapeHtml(entry.name)}</strong><br>` +
                `${n ? `${fmtInt(n)} naissance${n > 1 ? 's' : ''} · ${fmtPct((n / located) * 100)}` : 'Aucune naissance connue'}<br>` +
                `<span class="muted">${escapeHtml(where)}</span>`);
            const [px, py] = d3.pointer(event, node);
            tooltip.style('left', px + 14 + 'px').style('top', py + 14 + 'px')
                .style('transform', px > node.clientWidth * 0.6 ? 'translateX(calc(-100% - 28px))' : 'none')
                .style('opacity', 1);
        };
        const hover = (sel, getEntry) => sel
            .on('mouseenter', function (event, d) {
                d3.select(this).raise().attr('stroke', PALETTE.ink).attr('stroke-width', 1.6);
                showTip(event, getEntry(d));
            })
            .on('mousemove', (event, d) => showTip(event, getEntry(d)))
            .on('mouseleave', function () {
                d3.select(this).attr('stroke', PALETTE.mapStroke).attr('stroke-width', 0.7);
                tooltip.style('opacity', 0);
            });

        hover(svg.append('g').selectAll('path').data(empireData.states).join('path')
            .attr('d', (d) => d.d).attr('transform', (d) => tr(d.tr))
            .attr('fill', (d) => colorOf(d.entry))
            .attr('stroke', PALETTE.mapStroke).attr('stroke-width', 0.7), (d) => d.entry);
        // Underlay: a stroke in the fill colour seals the hairline gaps between neighbouring departments.
        svg.append('g').attr('pointer-events', 'none').selectAll('path').data(empireData.depts).join('path')
            .attr('d', (d) => d.base || d.d).attr('transform', (d) => tr(d.btr || d.tr))
            .attr('fill', (d) => colorOf(d.entry)).attr('stroke', (d) => colorOf(d.entry)).attr('stroke-width', 1.8);
        const deptPaths = hover(svg.append('g').selectAll('path').data(empireData.depts).join('path')
            .attr('d', (d) => d.d).attr('transform', (d) => tr(d.tr))
            .attr('fill', (d) => colorOf(d.entry))
            .attr('stroke', PALETTE.mapStroke).attr('stroke-width', 0.7), (d) => d.entry);

        // Direct label for the biggest department (Seine is too small to find by colour alone).
        const top = Array.from(counts.values()).sort((a, b) => b.n - a.n)[0];
        if (top) {
            const topPath = deptPaths.filter((d) => d.entry.id === top.entry.id).node();
            if (topPath) {
                const topDatum = d3.select(topPath).datum();
                const bb = topPath.getBBox();
                const cx = bb.x + bb.width / 2 + topDatum.tr[0];
                const cy = bb.y + bb.height / 2 + topDatum.tr[1];
                const lx = cx - 70;
                const ly = cy - 52;
                svg.append('line').attr('x1', cx).attr('y1', cy).attr('x2', lx + 30).attr('y2', ly + 4).attr('stroke', PALETTE.ink).attr('stroke-width', 1);
                svg.append('circle').attr('cx', cx).attr('cy', cy).attr('r', 3).attr('fill', 'none').attr('stroke', PALETTE.ink).attr('stroke-width', 1.2);
                svg.append('text').attr('x', lx + 30).attr('y', ly).attr('text-anchor', 'end')
                    .attr('font-family', FONT).attr('font-size', 13).attr('font-weight', 600).attr('fill', PALETTE.ink)
                    .attr('paint-order', 'stroke').attr('stroke', '#fff').attr('stroke-width', 3)
                    .text(`${top.entry.name} : ${fmtInt(top.n)}`);
            }
        }

        // Legend (classes + the two neutral fills)
        const legend = document.getElementById('empire-legend');
        legend.innerHTML = PALETTE.sequential.map((c, i) =>
            `<li><span class="viz-swatch" style="background:${c}"></span>${birthBinLabel(i)}</li>`).join('') +
            `<li><span class="viz-swatch" style="background:${PALETTE.mapEmpty}; border:1px solid ${PALETTE.axis}"></span>aucune naissance connue</li>` +
            `<li><span class="viz-swatch" style="background:${PALETTE.mapForeign}"></span>hors Empire</li>`;

        // Summary: how much of the register comes from where
        const sum = (pred) => Array.from(counts.values()).filter(pred).reduce((s, c) => s + c.n, 0);
        const seine = sum((c) => c.entry.id === 'Seine');
        const otherFrance = sum((c) => c.entry.kind === 'dept' && c.entry.country === 'France' && c.entry.id !== 'Seine');
        const annexed = sum((c) => c.entry.kind === 'dept' && c.entry.country !== 'France');
        const states = sum((c) => c.entry.kind === 'state');
        const part = (n) => fmtPct(located ? (n / located) * 100 : 0, 0);
        const unplaced = withPlace - located;
        setNote('empire-summary',
            `${fmtInt(located)} lieux de naissance placés sur ${fmtInt(withPlace)} renseignés` +
            (unplaced > 0 ? ` (${fmtInt(unplaced)} non placés : communes sans département lisible, régions ou pays absents de la carte). ` : '. ') +
            `Seine (Paris et banlieue) : ${part(seine)} · autres départements de la France actuelle : ${part(otherFrance)} · ` +
            `départements annexés hors de la France actuelle (Belgique, Rhénanie, Pays-Bas, Italie…) : ${part(annexed)} · États alliés : ${part(states)}.`);

        // Ranking of the best-represented departments (Seine excluded: it would flatten every other bar)
        const ranked = Array.from(counts.values()).filter((c) => c.entry.id !== 'Seine').sort((a, b) => b.n - a.n);
        const rankTop = ranked.slice(0, 10);
        const rankMax = rankTop.length ? rankTop[0].n : 1;
        document.getElementById('empire-top').innerHTML = rankTop.length
            ? `<li style="display:block; font-weight:600; color:var(--pitie-chart-ink)">Départements les plus représentés (hors Seine)</li>` +
              rankTop.map((c) =>
                `<li><span>${escapeHtml(c.entry.name)}${c.entry.country !== 'France' ? ` <small>(${escapeHtml(c.entry.country)})</small>` : ''}</span>` +
                `<span><span class="rank-bar" style="display:block; width:${(c.n / rankMax) * 100}%"></span></span>` +
                `<span class="rank-val">${fmtInt(c.n)} · ${fmtPct((c.n / located) * 100)}</span></li>`).join('')
            : '';

        const all = Array.from(counts.values()).sort((a, b) => b.n - a.n);
        setTableView('france-map', 'empire', ['Département (1811)', 'Territoire actuel', 'Naissances', 'Part'],
            all.map((c) => [c.entry.name, c.entry.kind === 'state' ? 'État hors Empire' : c.entry.country, fmtInt(c.n), fmtPct((c.n / located) * 100)]));
    }

    // ---- Domicile / Paris streets -------------------------------------------
    // "Domicile" entries that describe something other than a residential
    // street address — hospital-transfer origins, evacuees, "no fixed abode"
    // — so they're excluded from the street match instead of being logged as
    // unrecognized addresses.
    const NON_ADDRESS_DOMICILE_RE = /^(n\/?c\.?$|sans\s+(domicile|asile)|venant\b|arrivant\b|par\s+[ée]vacuation|en\s+cet\s+h[oô]pital|h[oô]pital|hotel[\s-]dieu)/i;

    // "Domicile" is "N°, rue X (Quartier)". The parenthetical quartier name is
    // frequently a stale Revolutionary-era section name or just misspelled, so
    // matching is done on the street name (via the Lazare/Perrot dataset's own
    // curated `variants`) rather than on that quartier text.
    function extractParisStreetName(trimmed) {
        let rest = trimmed.replace(/^\d+\s*(bis|ter|quater)?\s*(et\s*\d+\s*(bis|ter|quater)?)?\s*,?\s*/i, '');
        const parenIdx = rest.indexOf('(');
        if (parenIdx !== -1) rest = rest.slice(0, parenIdx);
        return rest.trim();
    }

    // A handful of standard abbreviations the Lazare `variants` lists don't
    // always cover.
    function normalizeStreetQuery(name) {
        return name
            .replace(/\bSte\b\.?/gi, 'Sainte')
            .replace(/\bSt\b\.?/gi, 'Saint')
            .replace(/\bBd\b\.?/gi, 'Boulevard')
            .replace(/\bFg\b\.?/gi, 'Faubourg')
            .trim();
    }

    // Returns null (blank/not an address), { outsideParis: true } (bracketed
    // "[Commune (Département)]" entries), { unmatched: true, query } (looked
    // like a street but no exact/normalized match in the Lazare/Perrot
    // dataset), or { street } on a match.
    function matchParisStreet(domicile) {
        if (!domicile) return null;
        const trimmed = domicile.trim();
        if (!trimmed) return null;
        if (trimmed.startsWith('[')) return { outsideParis: true };
        if (NON_ADDRESS_DOMICILE_RE.test(trimmed)) return null;

        const streetName = extractParisStreetName(trimmed);
        if (!streetName) return null;

        const query = normalizeStreetQuery(streetName).toLowerCase();
        const street = exactStreetLookup.get(query);
        if (!street) return { unmatched: true, query: streetName };
        return { street };
    }

    // Done once when both sources are loaded and cached per row (by object
    // reference, stable across filter changes) rather than redone on every
    // generateDomicileStats() call.
    function maybeBuildDomicileMatches() {
        if (!exactStreetLookup || dbData.length === 0 || domicileMatchByRow) return;

        domicileMatchByRow = new WeakMap();
        dbData.forEach((row) => {
            domicileMatchByRow.set(row, matchParisStreet(row['Domicile']));
        });
    }

    function generateDomicileStats(data) {
        const summaryEl = document.getElementById('domicile-stats-summary');
        if (!domicileMatchByRow) {
            if (summaryEl) summaryEl.textContent = 'Chargement des données de rues de Paris...';
            return;
        }

        const quartierCounts = {};
        const streetPoints = new Map();
        let matchedCount = 0;
        let outsideParisCount = 0;
        let unmatchedCount = 0;
        const unmatchedSamples = new Set();

        data.forEach((row) => {
            const domicile = row['Domicile'];
            if (!domicile) return;
            const match = domicileMatchByRow.get(row);
            if (!match) return;

            if (match.outsideParis) {
                outsideParisCount++;
                return;
            }
            if (match.unmatched) {
                unmatchedCount++;
                unmatchedSamples.add(match.query);
                return;
            }

            const street = match.street;
            matchedCount++;
            quartierCounts[street.quart] = (quartierCounts[street.quart] || 0) + 1;

            // geoSource:'quartier' is a quartier-centroid fallback (one of only
            // 48 possible points, not the street's real location) — kept but
            // styled distinctly on the map rather than hidden, same convention
            // as rues-paris.html.
            if (street.lat && street.lon) {
                if (!streetPoints.has(street.name)) {
                    streetPoints.set(street.name, {
                        lat: street.lat,
                        lon: street.lon,
                        count: 0,
                        name: street.name,
                        geoSource: street.geoSource || null
                    });
                }
                streetPoints.get(street.name).count++;
            }
        });

        if (unmatchedCount > 0) {
            console.warn(
                `Adresses parisiennes non reconnues: ${unmatchedCount} entrées, ${unmatchedSamples.size} rues distinctes`,
                Array.from(unmatchedSamples)
            );
        }

        if (summaryEl) {
            const considered = matchedCount + outsideParisCount + unmatchedCount;
            summaryEl.textContent =
                `${fmtInt(matchedCount)} domiciles rattachés à un quartier (${fmtPct(considered ? (matchedCount / considered) * 100 : 0, 0)} des adresses lisibles) · ` +
                `${fmtInt(outsideParisCount)} hors Paris · ` +
                `${fmtInt(unmatchedCount)} rues non reconnues (absentes des sources Lazare/Perrot ou mal orthographiées). ` +
                'Seuls les quartiers de la liste sont comptés : un biais possible vers les rues les mieux documentées.';
        }

        if (matchedCount > 0) {
            drawQuartierChart(quartierCounts);
            drawQuartierMap(Array.from(streetPoints.values()));
            drawParisStreetMap(Array.from(streetPoints.values()));
        }
    }

    // 48 quartiers (1811-1849 scheme) rather than the coarser 12
    // arrondissements — horizontal bars since 48 labels don't fit legibly
    // side by side. Ordered by quartier number, which already groups them by
    // arrondissement (quart 1-4 = 1er, 5-8 = 2e, etc.)
    function drawQuartierChart(quartierCounts) {
        const labels = [];
        const values = [];
        Array.from(quartierInfo.keys()).sort((a, b) => a - b).forEach((quart) => {
            const info = quartierInfo.get(quart);
            labels.push(`${quart}. ${info.nom} (${info.arr}${info.arr === 1 ? 'er' : 'e'})`);
            values.push(quartierCounts[quart] || 0);
        });

        const total = values.reduce((sum, v) => sum + v, 0);
        const biggest = new Set(values.map((v, i) => [v, i]).sort((x, y) => y[0] - x[0]).slice(0, 5).map(([, i]) => i));
        drawRankedBars('quartiers', 'domicile-arr-chart', labels.map((l, i) => [l, values[i]]), {
            total,
            unit: 'domiciles',
            labelFormat: (v, i) => (biggest.has(i) && v > 0 ? `${fmtInt(v)} · ${fmtPct((v / total) * 100)}` : '')
        });
        setTableView('domicile-arr-chart', 'quartiers', ['Quartier', 'Domiciles', 'Part'],
            labels.map((l, i) => [l, fmtInt(values[i]), fmtPct(total ? (values[i] / total) * 100 : 0)]));
    }

    // ---- Quartier choropleth ---------------------------------------------------
    // Modern quartiers administratifs (80, Ville de Paris open data) rather than the 48 quartiers of
    // 1811-1849: each geolocated street is placed in the modern quartier that contains it.
    const QUARTIER_BINS = [1, 5, 10, 25, 50, 100, 200];
    let quartierMap = null;
    let quartierGeo = null;
    let quartierPending = null;

    function ringContains(ring, x, y) {
        let inside = false;
        for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
            const [xi, yi] = ring[i];
            const [xj, yj] = ring[j];
            if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
        }
        return inside;
    }

    function featureContains(feature, x, y) {
        const g = feature.geometry;
        const polys = g.type === 'Polygon' ? [g.coordinates] : g.coordinates;
        return polys.some((poly) => ringContains(poly[0], x, y) && !poly.slice(1).some((hole) => ringContains(hole, x, y)));
    }

    function quartierFeatures(points) {
        const counts = new Map();
        let outside = 0;
        let approx = 0;
        points.forEach((p) => {
            if (p.geoSource === 'quartier') { approx += p.count; return; }
            const hit = quartierGeo.features.find((f) => featureContains(f, p.lon, p.lat));
            if (hit) counts.set(hit.properties.c_qu, (counts.get(hit.properties.c_qu) || 0) + p.count);
            else outside += p.count;
        });
        const total = Array.from(counts.values()).reduce((a, b) => a + b, 0);
        setNote('quartier-map-note',
            `${fmtInt(total)} domiciles placés dans un quartier actuel d'après la position précise de leur rue ` +
            `(${fmtInt(approx)} adresses à position approximative et ${fmtInt(outside)} hors des limites actuelles de Paris ne sont pas comptées).`);
        return {
            type: 'FeatureCollection',
            features: quartierGeo.features.map((f) => {
                const n = counts.get(f.properties.c_qu) || 0;
                return Object.assign({}, f, {
                    properties: { nom: f.properties.l_qu, arr: f.properties.c_ar, count: n, share: total ? (n / total) * 100 : 0 }
                });
            })
        };
    }

    function drawQuartierMap(points) {
        quartierPending = points;
        const render = () => {
            const data = quartierFeatures(quartierPending);
            if (quartierMap.getSource('quartiers')) {
                quartierMap.getSource('quartiers').setData(data);
                return;
            }
            const fill = ['step', ['get', 'count'], PALETTE.mapEmpty];
            QUARTIER_BINS.forEach((b, i) => fill.push(b, PALETTE.sequential[i]));
            quartierMap.addSource('quartiers', { type: 'geojson', data });
            quartierMap.addLayer({ id: 'quartiers-fill', type: 'fill', source: 'quartiers', paint: { 'fill-color': fill, 'fill-opacity': 0.85 } });
            quartierMap.addLayer({ id: 'quartiers-line', type: 'line', source: 'quartiers', paint: { 'line-color': '#fff', 'line-width': 1 } });
            let popup = null;
            quartierMap.on('mousemove', 'quartiers-fill', (e) => {
                quartierMap.getCanvas().style.cursor = 'pointer';
                const p = e.features[0].properties;
                if (popup) popup.remove();
                popup = new maplibregl.Popup({ closeButton: false, closeOnClick: false, maxWidth: '260px' })
                    .setLngLat(e.lngLat)
                    .setHTML(`<strong>${escapeHtml(p.nom)}</strong> (${escapeHtml(p.arr + (Number(p.arr) === 1 ? 'er' : 'e'))} arr.)<br>${fmtInt(p.count)} domicile${p.count > 1 ? 's' : ''} · ${fmtPct(Number(p.share))}`)
                    .addTo(quartierMap);
            });
            quartierMap.on('mouseleave', 'quartiers-fill', () => {
                quartierMap.getCanvas().style.cursor = '';
                if (popup) { popup.remove(); popup = null; }
            });
        };

        if (quartierMap) {
            if (quartierMap.isStyleLoaded() && quartierGeo) render();
            return;
        }
        document.getElementById('quartier-legend').innerHTML =
            `<li><span class="viz-swatch" style="background:${PALETTE.mapEmpty}; border:1px solid ${PALETTE.axis}"></span>aucun</li>` +
            PALETTE.sequential.map((c, i) => {
                const label = i === QUARTIER_BINS.length - 1 ? `${QUARTIER_BINS[i]} et plus` : `${QUARTIER_BINS[i]} à ${QUARTIER_BINS[i + 1] - 1}`;
                return `<li><span class="viz-swatch" style="background:${c}"></span>${i === 0 ? '1 à 4' : label}</li>`;
            }).join('');
        quartierMap = new maplibregl.Map({
            container: 'quartier-map',
            style: {
                version: 8,
                sources: { osm: { type: 'raster', tiles: ['https://tile.openstreetmap.org/{z}/{x}/{y}.png'], tileSize: 256, attribution: '© <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap</a>' } },
                layers: [
                    { id: 'bg', type: 'background', paint: { 'background-color': '#fafaf8' } },
                    { id: 'osm', type: 'raster', source: 'osm', paint: { 'raster-saturation': -1, 'raster-opacity': 0.4 } }
                ]
            },
            center: [2.345, 48.858],
            zoom: 11.2
        });
        quartierMap.addControl(new maplibregl.NavigationControl(), 'top-right');
        Promise.all([
            fetch(CONFIG.quartierGeoUrl).then((r) => r.json()),
            new Promise((resolve) => quartierMap.on('load', resolve))
        ]).then(([geo]) => { quartierGeo = geo; render(); })
          .catch((error) => console.error('Erreur carte des quartiers:', error));
    }

    function escapeHtml(str) {
        return String(str).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
    }

    function pointsToGeoJSON(points) {
        return {
            type: 'FeatureCollection',
            features: points.map((p) => ({
                type: 'Feature',
                geometry: { type: 'Point', coordinates: [p.lon, p.lat] },
                properties: { name: p.name, count: p.count, geoSource: p.geoSource }
            }))
        };
    }

    // Data to apply once the map's style/tiles finish loading. generateDomicileStats()
    // runs more than once in quick succession while data is still loading (the CSV-load
    // and streets-load completion handlers can each trigger a render), and MapLibre's
    // 'load' event doesn't fire synchronously — so a second drawParisStreetMap() call
    // can land before the first map instance is ready. Stashing the latest points here
    // and reading them from the 'load' handler (rather than closing over a stale
    // snapshot) means whichever call happens last still wins, without tearing down and
    // recreating the map (which re-downloads every tile and can leave a dangling
    // instance whose 'load' event fires against a container that's been wiped).
    let parisMapPendingPoints = null;

    // Circle area (not radius) is proportional to the number of deaths.
    function circleRadiusExpr(maxCount) {
        return ['interpolate', ['linear'], ['sqrt', ['get', 'count']], 1, 3, Math.max(2, Math.sqrt(maxCount)), 20];
    }

    // Real OSM-tiled map (MapLibre GL), same approach as rues-paris.html in
    // the companion genealogy tool — a plain D3 scatter on a blank background
    // gave no sense of *where* in Paris these points actually are.
    function drawParisStreetMap(points) {
        const container = document.getElementById('domicile-map');

        if (parisMapInstance) {
            const src = parisMapInstance.getSource('domiciles');
            if (!src) {
                // Style/tiles still loading — the 'load' handler will pick this up.
                parisMapPendingPoints = points;
                return;
            }
            src.setData(pointsToGeoJSON(points));
            const maxCount = points.length ? Math.max(...points.map((p) => p.count)) : 1;
            parisMapInstance.setPaintProperty('domiciles-point', 'circle-radius', circleRadiusExpr(maxCount));
            return;
        }

        if (points.length === 0) {
            container.innerHTML = '<p>Aucune rue géolocalisée pour cette sélection.</p>';
            return;
        }

        container.innerHTML = '';
        parisMapPendingPoints = points;
        parisMapInstance = new maplibregl.Map({
            container: 'domicile-map',
            style: {
                version: 8,
                sources: {
                    osm: {
                        type: 'raster',
                        tiles: ['https://tile.openstreetmap.org/{z}/{x}/{y}.png'],
                        tileSize: 256,
                        attribution: '© <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap</a>'
                    }
                },
                // Desaturated, faded basemap: the data layer has to stand out, not the street map.
                layers: [
                    { id: 'bg', type: 'background', paint: { 'background-color': '#fafaf8' } },
                    { id: 'osm', type: 'raster', source: 'osm', paint: { 'raster-saturation': -1, 'raster-opacity': 0.5 } }
                ]
            },
            center: [2.3488, 48.8534],
            zoom: 11
        });
        parisMapInstance.addControl(new maplibregl.NavigationControl(), 'top-right');

        parisMapInstance.on('load', () => {
            const finalPoints = parisMapPendingPoints || [];
            parisMapPendingPoints = null;
            const maxCount = finalPoints.length ? Math.max(...finalPoints.map((p) => p.count)) : 1;

            parisMapInstance.addSource('domiciles', { type: 'geojson', data: pointsToGeoJSON(finalPoints) });
            parisMapInstance.addLayer({
                id: 'domiciles-point',
                type: 'circle',
                source: 'domiciles',
                paint: {
                    'circle-radius': circleRadiusExpr(maxCount),
                    'circle-color': ['match', ['get', 'geoSource'], 'quartier', PALETTE.s2, PALETTE.s1],
                    'circle-opacity': ['match', ['get', 'geoSource'], 'quartier', 0.55, 0.8],
                    'circle-stroke-color': '#fff',
                    'circle-stroke-width': 1
                }
            });

            let popup = null;
            parisMapInstance.on('mouseenter', 'domiciles-point', (e) => {
                parisMapInstance.getCanvas().style.cursor = 'pointer';
                const p = e.features[0].properties;
                const precisionNote = p.geoSource === 'quartier'
                    ? '<br><em>position approximative (centre du quartier)</em>'
                    : '';
                popup = new maplibregl.Popup({ closeButton: false, closeOnClick: false, maxWidth: '260px' })
                    .setLngLat(e.features[0].geometry.coordinates)
                    .setHTML(`<strong>${escapeHtml(p.name)}</strong><br>Domiciles: ${p.count}${precisionNote}`)
                    .addTo(parisMapInstance);
            });
            parisMapInstance.on('mouseleave', 'domiciles-point', () => {
                parisMapInstance.getCanvas().style.cursor = '';
                if (popup) { popup.remove(); popup = null; }
            });
        });
    }

    // Quartier choropleth <-> street dots, in one card
    function setParisView(view) {
        document.querySelectorAll('.pitie-app [data-paris-view]').forEach((b) => {
            const on = b.dataset.parisView === view;
            b.classList.toggle('is-active', on);
            b.setAttribute('aria-pressed', String(on));
        });
        document.querySelectorAll('.pitie-app [data-paris-pane]').forEach((p) => { p.hidden = p.dataset.parisPane !== view; });
        document.getElementById('quartier-map').classList.toggle('is-off', view !== 'quartier');
        document.getElementById('domicile-map').classList.toggle('is-off', view !== 'rues');
        document.getElementById('quartier-legend').hidden = view !== 'quartier';
        document.getElementById('rues-legend').hidden = view !== 'rues';
        const map = view === 'quartier' ? quartierMap : parisMapInstance;
        if (map) map.resize();
    }

    // ---- Search -------------------------------------------------------------
    function performSearch(event) {
        if (event) event.preventDefault();

        let result = [...dbData];

        SEARCH_CRITERIA.forEach((criterion) => {
            const searchTerm = document.getElementById(criterion.id).value.trim().toLowerCase();
            const searchTermNoAccent = stripAccents(searchTerm);
            const isFuzzy = document.getElementById(`fuzzy-${criterion.id}`).checked;

            if (!searchTerm) return;

            if (isFuzzy) {
                const matches = new Set(fuseIndexes[criterion.key].search(searchTermNoAccent).map((r) => r.item));
                result = result.filter((item) => matches.has(item));
            } else {
                result = result.filter((item) =>
                    item[criterion.key] && stripAccents(item[criterion.key].toLowerCase()).includes(searchTermNoAccent)
                );
            }
        });

        displayResults(result);
    }

    function check_listener(e) {
        const table = document.getElementById('results-table');
        const columnIndex = e.target.value;
        const cells = table.querySelectorAll(`th[data-column="${columnIndex}"], td:nth-child(${parseInt(columnIndex, 10) + 1})`);
        cells.forEach((cell) => {
            cell.style.display = e.target.checked ? '' : 'none';
        });
    }

    function displayResults(results) {
        const resultsContainer = document.getElementById('search-results');

        if (results.length === 0) {
            resultsContainer.innerHTML = '<p class="text-center">Aucun résultat trouvé.</p>';
            return;
        }

        let tableHTML = `
            <h3>${results.length} résultat(s) trouvé(s)</h3>

            <div class="table-container">
                <strong>Show/Hide Columns:</strong>
                <div id="column-controls" class="column-controls">
                </div>
                <table id="results-table">
                    <thead>
                        <tr>
                            <th data-column="0">Nom</th>
                            <th data-column="1">Prénoms</th>
                            <th data-column="2">Date de décès</th>
                            <th data-column="3">Âge</th>
                            <th data-column="4">Lieu de naissance</th>
                            <th data-column="5">Profession</th>
                            <th data-column="6">Cause du décès</th>
                            <th data-column="7">Nom conjoint</th>
                            <th data-column="8">Prénoms conjoint</th>
                            <th data-column="9">Permalien</th>
                        </tr>
                    </thead>
                    <tbody>
        `;

        results.slice(0, CONFIG.maxResultsShown).forEach((item) => {
            tableHTML += `
                <tr>
                    <td class="nth-child">${item['NOM'] || '-'}</td>
                    <td class="nth-child">${item['Prénoms'] || '-'}</td>
                    <td class="nth-child">${item['Date de décès'] || '-'}</td>
                    <td class="nth-child">${item['Âge'] || '-'}</td>
                    <td class="nth-child">${item['Lieu de naissance'] || '-'}</td>
                    <td class="nth-child">${item['Profession'] || '-'}</td>
                    <td class="nth-child">${item['Cause de mort: espèce'] || '-'}</td>
                    <td class="nth-child">${item['NOM CONJOINT'] || '-'}</td>
                    <td class="nth-child">${item['Prénoms Conjoint'] || '-'}</td>
                    <td class="nth-child"><a href='${item['Permalien'] || '-'}'>lien</a></td>
                </tr>
            `;
        });

        if (results.length > CONFIG.maxResultsShown) {
            tableHTML += `
                <tr>
                    <td colspan="10" class="text-center">
                        ... et ${results.length - CONFIG.maxResultsShown} autre(s) résultat(s). Affinez votre recherche pour voir plus de détails.
                    </td>
                </tr>
            `;
        }

        tableHTML += '</tbody></table></div>';
        resultsContainer.innerHTML = tableHTML;

        const table = document.getElementById('results-table');
        const headers = table.querySelectorAll('thead th');
        const controlsContainer = document.getElementById('column-controls');

        headers.forEach((header, index) => {
            if (index < 2) return; // first two columns are always visible
            const label = document.createElement('label');
            const checkbox = document.createElement('input');
            checkbox.type = 'checkbox';
            checkbox.value = index;
            checkbox.checked = true;

            label.appendChild(checkbox);
            label.appendChild(document.createTextNode(header.textContent));
            controlsContainer.appendChild(label);

            checkbox.addEventListener('change', check_listener);
        });
    }

    // ---- Navigation -----------------------------------------------------
    function showPage(pageId) {
        document.querySelectorAll('.pitie-app .page-section').forEach((section) => section.classList.remove('active'));
        document.querySelectorAll('.pitie-app #mobile-menu a').forEach((link) => link.classList.remove('active'));

        document.getElementById(pageId).classList.add('active');

        document.querySelectorAll('.pitie-app .nav-link').forEach((link) => link.classList.remove('active'));
        document.querySelectorAll(`.pitie-app nav a[href="#${pageId}"]`).forEach((link) => link.classList.add('active'));
        document.querySelectorAll(`.pitie-app #mobile-menu a[href="#${pageId}"]`).forEach((link) => link.classList.add('active'));

        document.getElementById('mobile-menu').classList.remove('show');

        window.location.hash = pageId;
    }

    function toggleMobileMenu() {
        document.getElementById('mobile-menu').classList.toggle('show');
    }

    function initializeNavigation() {
        const hash = window.location.hash.substring(1);
        if (hash && document.getElementById(hash) && document.querySelector(`.pitie-app .nav-link[href="#${hash}"]`)) {
            showPage(hash);
        }
    }

    // =====================================================================
    // STATISTIQUES AVANCÉES (chargées à la demande)
    // =====================================================================

    // Taxonomies pour classification - basée sur l'analyse des 2000+ entrées du CSV
    const jobTaxonomy = [
        { cat: 'Armée', keywords: [
            'soldat', 'militaire', 'fusilier', 'fusillier', 'garde impérial', 'garde imperial',
            'caporal', 'sergent', 'officier', 'dragon', 'hussard', 'canonnier', 'canonier',
            'infanterie', 'voltigeur', 'tirailleur', 'prussien', 'grenadier', 'cavalier',
            'artilleur', 'chasseur', 'cuirassier', 'lancier', 'tambour', 'trompette',
            'ex-militaire', 'vétéran', 'veteran', 'sapeur', 'maréchal des logis'
        ]},
        { cat: 'Bâtiment', keywords: [
            'maçon', 'macon', 'charpentier', 'menuisier', 'tailleur de pierre', 'couvreur',
            'peintre en bâtiment', 'peintre en batiment', 'vitrier', 'scieur de long',
            'terrassier', 'paveur', 'carrier', 'plâtrier', 'platrier', 'carreleur',
            'couverturier', 'plombier', 'serrurier', 'charron', 'marbrier', 'sculpteur'
        ]},
        { cat: 'Textile', keywords: [
            'couturi', 'lingère', 'lingere', 'tisserand', 'tailleur', 'brodeuse', 'brodeur',
            'chapelier', 'chapelière', 'dentellière', 'dentelliere', 'fille de mode', 'mode',
            'fileuse', 'fileur', 'bonnetier', 'bonnetière', 'culottière', 'culottiere',
            'gantière', 'gantiere', 'tricoteuse', 'tricoteur', 'dévideuse', 'devideuse',
            'cotonnière', 'cotonniere', 'ouvrier en coton', 'ouvrière en coton',
            'ouvrier en laine', 'ouvrière en laine', 'cardeur', 'cardeuse', 'frangière',
            'frangiere', 'passementier', 'rubanier', 'teinturier', 'blanchisseu'
        ]},
        { cat: 'Service', keywords: [
            'domestique', 'servante', 'femme de chambre', 'cocher', 'valet', 'cuisinier',
            'cuisinière', 'cuisiniere', 'portier', 'portière', 'portiere', 'concierge',
            'frotteur', 'palfrenier', 'palefrenier', 'balayeur', 'femme de ménage',
            'femme de menage', 'garçon de service', 'garcon de service', 'laquais'
        ]},
        { cat: 'Journalier', keywords: [
            'journalier', 'journalière', 'journaliere', 'gagne-denier', 'gagne denier',
            'manoeuvre', 'manouvrier', 'homme de peine', 'scieur de bois', 'portefaix',
            "porteur d'eau", "porteuse d'eau", 'porteur à la halle', 'porteuse à la halle',
            'commissionnaire', 'porteur', 'charretier', 'voiturier', 'débardeur'
        ]},
        { cat: 'Cuir', keywords: [
            'cordonnier', 'cordonnière', 'bottier', 'sellier', 'tanneur', 'corroyeur',
            'bourrelier', 'bourelier', 'maroquinier', 'gaiînier', 'gainier', 'savetier'
        ]},
        { cat: 'Métallurgie', keywords: [
            'serrurier', 'ferblantier', 'fondeur', 'chaudronnier', 'maréchal', 'marechal',
            'forgeron', 'cloutier', 'taillandier', 'mécanicien', 'mecanicien', 'armurier',
            "potier d'étain", "potier d'etain", 'rémouleur', 'remouleur', 'coutelier',
            'épinglier', 'ferronnier'
        ]},
        { cat: 'Artisanat luxe', keywords: [
            'bijoutier', 'horloger', 'orfèvre', 'orfevre', 'émailleur', 'emailleur',
            'émailleuse', 'emailleuse', 'joaillier', 'lapidaire', 'graveur', 'ciseleur',
            'doreur', 'argenteur', 'tabletier', 'tablettier', 'éventailliste', 'lunetier'
        ]},
        { cat: 'Bois', keywords: [
            'ébéniste', 'ebeniste', 'tourneur', 'tonnelier', 'vannier', 'layetier',
            'charron', 'sabotier', 'brossier', 'boisselier'
        ]},
        { cat: 'Imprimerie', keywords: [
            'imprimeur', 'relieur', 'écrivain', 'ecrivain', 'papetier', 'cartonnière',
            'cartonniere', 'cartonnier', 'lithographe', 'typographe', 'graveur'
        ]},
        { cat: 'Alimentation', keywords: [
            'boucher', 'boulanger', 'boulangère', 'pâtissier', 'patissier', 'limonadier',
            'traiteur', 'marchand de vin', 'charcutier', 'fruitière', 'fruitiere',
            'épicier', 'epicier', 'confiseur', 'vinaigrier', 'brasseur', 'meunier',
            'garçon de café', 'garcon de cafe'
        ]},
        { cat: 'Commerce', keywords: [
            'marchand', 'marchande', 'revendeu', 'brocanteur', 'brocanteuse', 'colporteur',
            'camelot', 'chiffonnier', 'chiffonnière', 'chiffoniere', 'fripier', 'fripière',
            'mercier', 'mercière', 'épicier', 'quincaillier'
        ]},
        { cat: 'Agriculture', keywords: [
            'cultivateur', 'vigneron', 'jardinier', 'jardinière', 'jardini', 'laboureur',
            'berger', 'bergère', 'bergere', 'charretier', 'moissonneur', 'vendangeur',
            'maraîcher', 'maraicher', 'batteur en grange'
        ]},
        { cat: 'Transport', keywords: [
            'marinier', 'batelier', 'voiturier', 'cocher', 'postillon', 'charretier',
            'ouvrier au canal', 'éclusier', 'débardeur', 'roulier'
        ]},
        { cat: 'Arts', keywords: [
            'musicien', 'peintre', 'sculpteur', 'acteur', 'actrice', 'comédien', 'comedien',
            'danseur', 'danseuse', 'chanteur', 'chanteuse', 'artiste', 'décrotteur',
            'graveur'
        ]},
        { cat: 'Intellectuel', keywords: [
            'instituteur', 'institutrice', 'professeur', 'précepteur', 'clerc', 'notaire',
            'avocat', 'médecin', 'chirurgien', 'pharmacien', 'apothicaire', 'employé',
            'commis', 'comptable'
        ]},
        { cat: 'Industrie', keywords: [
            'ouvrier au tabac', 'ouvrière au tabac', 'gazier', 'gazière', 'gaziere',
            'matelassier', 'ouvrier', 'ouvrière en linge'
        ]},
        { cat: 'Fleuriste', keywords: ['fleuriste', 'bouquetière', 'bouquetiere'] },
        { cat: 'Sans état', keywords: [
            'sans état', 'sans etat', 'néant', 'neant', 'indigent', 'n/c', 'aucune',
            'enfant', 'élève', 'eleve', 'mendiant', 'mendiante', 'rentier', 'rentière',
            'propriétaire', 'proprietaire'
        ]}
    ];

    // Taxonomie des causes de décès - basée sur l'analyse des 2000+ entrées du CSV
    const causeTaxonomy = [
        { cat: 'Phtisie/Tuberculose', keywords: [
            'phtisie', 'phitisie', 'phtisique', 'poitrinaire', 'tuberculose', 'tubercule',
            'chronique de poitrine', 'affection de poitrine'
        ]},
        { cat: 'Fièvres', keywords: [
            'fièvre', 'fievre', 'typhus', 'typhoïde', 'typhoide', 'adynamique', 'ataxique',
            'putride', 'bilieuse', 'gastrique', 'catarrhale', 'muqueuse', 'hectique',
            'intermittente', 'continue', 'lente', 'inflammatoire', 'dynamique',
            'ataxico-adynamique', 'lente nerveuse'
        ]},
        { cat: 'Respiratoire', keywords: [
            'pneumonie', 'péripneumonie', 'peripneumonie', 'catarrhe', 'catharre',
            'pleurésie', 'pleuresie', 'fluxion de poitrine', 'flux de poitrine',
            'hydrothorax', 'hydro-thorax', 'asthme', 'suffocant', 'bronchite',
            'laryngée', 'laryngite', 'angine', 'croup', 'coqueluche'
        ]},
        { cat: 'Cardiovasculaire', keywords: [
            'anévrisme', 'anevrisme', 'coeur', 'cœur', 'hypertrophie du coeur',
            'affection organique du coeur', 'maladie du coeur', 'maladie organique du coeur',
            'cardite', 'péricardite', 'endocardite', 'angine de poitrine'
        ]},
        { cat: 'Digestif', keywords: [
            'diarrhée', 'diarrhee', 'dévoiement', 'devoiement', 'dysenterie', 'dyssenterie',
            'dissenterie', 'dissentrie', 'gastrite', 'gastro-entérite', 'gastro-enterite',
            'entérite', 'enterite', 'péritonite', 'peritonite', 'colique', 'colite',
            'ulcérations intestinales', 'embarras gastrique', 'estomac', 'abdomen',
            'engorgement au foie', 'foie', 'hépatite', 'ictère', 'jaunisse'
        ]},
        { cat: 'Hydropisie', keywords: [
            'hydropisie', 'hydropysie', 'hydropique', 'anasarque', 'ascite',
            'leucophlegmatie', 'leucophlegmasie', 'œdème', 'oedeme'
        ]},
        { cat: 'Neurologique', keywords: [
            'apoplexie', 'paralysie', 'hémiplégie', 'hemiplegie', 'ramollissement du cerveau',
            'cerveau', 'méningite', 'meningite', 'convulsion', 'épilepsie', 'epilepsie',
            'tétanos', 'tetanos', 'encéphalite', 'encephalite'
        ]},
        { cat: 'Cachexie/Marasme', keywords: [
            'cachexie', 'cach', 'marasme', 'adynamie', 'asthénie', 'asthenie',
            'affaiblissement', 'épuisement', 'epuisement', 'consomption', 'atrophie'
        ]},
        { cat: 'Vieillesse', keywords: [
            'sénile', 'senile', 'sénilité', 'senilite', 'vieillesse', 'décrépitude',
            'decrepitude', 'débilité', 'debilite', 'caducité'
        ]},
        { cat: 'Cancer', keywords: [
            'cancer', 'tumeur', 'squirre', 'ulcère à la matrice', 'ulcere a la matrice',
            "ulcère à l'uterus", "cancer de l'estomac", "cancer de l'utérus",
            'cancer uterine', 'carcinome'
        ]},
        { cat: 'Infectieux', keywords: [
            'choléra', 'cholera', 'variole', 'petite vérole', 'rougeole', 'scarlatine',
            'syphilis', 'vénérien', 'venerien', 'érysipèle', 'erysipele', 'gangrène',
            'gangrene', 'scorbut', 'fièvre jaune', 'peste', 'diphtérie', 'diphterie'
        ]},
        { cat: 'Génito-urinaire', keywords: [
            'aménorrhée', 'amenorrhee', 'matrice', 'utérus', 'uterus', 'métrite', 'metrite',
            'néphrite', 'nephrite', 'calcul', "rétention d'urine", 'hydropisie de poitrine',
            'couches', 'accouchement', 'fièvre puerpérale'
        ]},
        { cat: 'Rhumatismal', keywords: ['rhumatisme', 'rhumatismale', 'goutte', 'arthrite', 'articulation'] },
        { cat: 'Mort subite/Arrivée', keywords: [
            'arrivé mourant', 'arrive mourant', 'arriv', 'mort en entrant', 'mort en arrivant',
            'morte en arrivant', 'agonisant', 'agonisante', 'mort subite', 'foudroyant'
        ]},
        { cat: 'Accidents', keywords: [
            'chute', 'brûlure', 'brulure', 'fracture', 'plaie', 'blessure', 'contusion',
            'noyade', 'asphyxie', 'strangulation', 'suicide', 'empoisonnement', 'écrasement'
        ]},
        { cat: 'Non précisé', keywords: ['n/c', 'non précisé', 'non precise', '???', 'inconnu', 'indéterminé'] }
    ];

    function categorizeAdvanced(str, taxonomy, defaultVal = 'Autres') {
        if (!str || str.length < 3) return defaultVal;
        let s = str.toLowerCase();
        for (let t of taxonomy) {
            if (t.keywords.some((k) => s.includes(k))) return t.cat;
        }
        return defaultVal;
    }

    function cleanPrenoms(str) {
        if (!str || typeof str !== 'string') return [null, null, null];
        let parts = str.trim().split(/[\s-]+/);
        let cleanParts = parts.filter((p) => p.length > 2 && !['veuve', 'épouse', 'fils', 'fille', 'femme', 'epoux', 'sieur'].includes(p.toLowerCase()));
        return [cleanParts[0] || null, cleanParts[1] || null, cleanParts[2] || null];
    }

    function extractDepartmentAdvanced(val) {
        const raw = extractHistoricalDeptRaw(val);
        return raw ? canonicalDeptName(raw) : 'Inconnu';
    }

    function calculateSmartMax(matrix) {
        let values = _.flattenDeep(matrix).filter((v) => v > 0).sort((a, b) => a - b);
        if (values.length === 0) return 10;
        return values[Math.floor(values.length * 0.95)];
    }

    function getValueAdvanced(row, keys) {
        for (let k of keys) { if (row[k] !== undefined) return row[k]; }
        return null;
    }

    function loadAdvancedStats() {
        if (advancedStatsLoaded) {
            document.getElementById('advanced-stats').scrollIntoView({ behavior: 'smooth' });
            return;
        }

        document.getElementById('advanced-stats').style.display = 'block';
        document.getElementById('btn-more-stats').textContent = '⏳ Chargement en cours...';
        document.getElementById('btn-more-stats').disabled = true;

        if (dbData.length > 0) {
            advancedStatsRetryCount = 0;
            processAdvancedData(dbData);
            return;
        }

        const statusEl = document.getElementById('advanced-stats-status');
        if (advancedStatsRetryCount < CONFIG.advancedStatsRetry.maxAttempts) {
            advancedStatsRetryCount++;
            statusEl.textContent = `⏳ Attente du chargement des données... (${advancedStatsRetryCount}/${CONFIG.advancedStatsRetry.maxAttempts})`;
            setTimeout(loadAdvancedStats, CONFIG.advancedStatsRetry.delayMs);
        } else {
            statusEl.textContent = '❌ Impossible de charger les données. Veuillez recharger la page.';
            statusEl.classList.remove('status-ok');
            statusEl.classList.add('status-error');
            document.getElementById('btn-more-stats').textContent = '📊 Plus de statistiques avancées';
            document.getElementById('btn-more-stats').disabled = false;
        }
    }

    function processAdvancedData(rawData) {
        ADVANCED_DATA = rawData.map((d) => {
            let dateStr = getValueAdvanced(d, ['Date de décès', 'Date']);
            let parts = dateStr ? dateStr.match(/(\d{1,2})[\/\-\.](\d{1,2})[\/\-\.](\d{4})/) : null;
            let date = parts ? new Date(parts[3], parts[2] - 1, parts[1]) : null;

            let age = parseAge(getValueAdvanced(d, ['Âge', 'Age', 'age']));

            // Missing / unreadable sex stays null: it must not be counted as a man.
            let sexeStr = (getValueAdvanced(d, ['Sexe']) || '').trim().toLowerCase();
            let sexe = sexeStr.startsWith('f') ? 'F' : (sexeStr.startsWith('m') ? 'M' : null);

            let causeStr = getValueAdvanced(d, ['Cause de mort: espèce', 'Cause', 'Maladie', 'Observations', 'Genre de mort']);

            return {
                date: date,
                year: date ? date.getFullYear() : null,
                month: date ? date.getMonth() : null,
                age: age,
                sexe: sexe,
                job_cat: categorizeAdvanced(getValueAdvanced(d, ['Profession', 'Metier']), jobTaxonomy, 'Autres'),
                cause_cat: (causeStr && causeStr.trim().length >= 3) ? categorizeAdvanced(causeStr, causeTaxonomy, 'Autres') : 'Non précisé',
                cause_raw: causeStr,
                departement: extractDepartmentAdvanced(getValueAdvanced(d, ['Lieu de naissance', 'Commune de naissance'])),
                p_defunt: cleanPrenoms(getValueAdvanced(d, ['Prénoms', 'Prenoms', 'Prénom'])),
                p_conjoint: cleanPrenoms(getValueAdvanced(d, ['Prénoms Conjoint', 'Prenoms Conjoint']))
            };
        }).filter((d) => d.date != null && d.year >= CONFIG.dataYearRange[0] && d.year <= CONFIG.dataYearRange[1]);

        const statusEl = document.getElementById('advanced-stats-status');
        statusEl.textContent = `✅ Statistiques avancées chargées (${ADVANCED_DATA.length} entrées analysées${filteredData.length < dbData.length ? ', filtres appliqués' : ''})`;
        statusEl.classList.remove('status-error');
        statusEl.classList.add('status-ok');

        document.getElementById('btn-more-stats').textContent = '📊 Statistiques avancées affichées';
        document.getElementById('btn-more-stats').disabled = false;

        populateCauseDropdown();
        updateHeatmap();
        renderSeasonality();
        renderRegionJobs();
        renderLifeExpectancy();
        renderCauseViolinPlot();
        renderNamesPercent();

        const firstLoad = !advancedStatsLoaded;
        advancedStatsLoaded = true;

        if (firstLoad) document.getElementById('advanced-stats').scrollIntoView({ behavior: 'smooth' });
    }

    // The filters above scope the advanced charts too (one filter row for every chart on the page).
    function refreshAdvancedStats() {
        if (advancedStatsLoaded) processAdvancedData(filteredData);
    }

    function populateCauseDropdown() {
        let counts = _.countBy(ADVANCED_DATA, 'cause_cat');
        let sel = document.getElementById('causeSelect');
        const previous = sel.value;
        sel.innerHTML = '<option value="All">Toutes les causes</option>';
        Object.entries(counts).sort((a, b) => b[1] - a[1]).forEach(([cause, count]) => {
            let opt = document.createElement('option');
            opt.value = cause;
            opt.text = `${cause} (${count})`;
            sel.add(opt);
        });
        if (previous && Array.from(sel.options).some((o) => o.value === previous)) sel.value = previous;
    }

    // Years complete enough to be compared (see MIN_YEAR_ENTRIES), plus the ones left out.
    function yearCoverage() {
        const totals = _.countBy(ADVANCED_DATA, 'year');
        const all = Object.keys(totals).map(Number).sort((a, b) => a - b);
        return {
            totals,
            years: all.filter((y) => totals[y] >= MIN_YEAR_ENTRIES),
            thin: all.filter((y) => totals[y] < MIN_YEAR_ENTRIES)
        };
    }

    function updateHeatmap() {
        if (ADVANCED_DATA.length === 0) return;

        const selectedCause = document.getElementById('causeSelect').value;
        const rows = (selectedCause === 'All') ? ADVANCED_DATA : ADVANCED_DATA.filter((d) => d.cause_cat === selectedCause);
        const { years, thin, totals } = yearCoverage();

        const z = MONTH_NAMES.map(() => Array(years.length).fill(0));
        rows.forEach((d) => {
            const x = years.indexOf(d.year);
            if (x > -1 && d.month !== null) z[d.month][x]++;
        });
        const text = z.map((r) => r.map((v) => (v ? String(v) : '')));
        const zmax = Math.max(1, ...z.flat());

        setNote('heatmap-note',
            `${selectedCause === 'All' ? 'Toutes causes' : selectedCause} : ${fmtInt(rows.length)} décès sur ${years.length} années. ` +
            (thin.length ? `Années écartées car trop peu de relevés indexés (moins de ${MIN_YEAR_ENTRIES}) : ${thin.map((y) => `${y} (${totals[y]})`).join(', ')}. ` : '') +
            'Une case très claire peut venir d\'un registre pas encore indexé plutôt que d\'une absence de décès.');

        Plotly.react('chart-heatmap-deaths', [{
            x: years.map(String), y: MONTH_NAMES, z, text, type: 'heatmap',
            colorscale: sequentialColorscale(), zmin: 0, zmax,
            xgap: 2, ygap: 2,
            texttemplate: '%{text}', textfont: { size: 10 },
            hovertemplate: '%{y} %{x} : %{z} décès<extra></extra>',
            colorbar: { title: { text: 'Décès / mois' }, thickness: 12, outlinewidth: 0 }
        }], plotlyLayout({
            height: 460,
            margin: { t: 8, l: 48 },
            xaxis: { type: 'category', showgrid: false },
            yaxis: { autorange: 'reversed', showgrid: false, fixedrange: true }
        }), PLOTLY_CONFIG);
    }

    function renderSeasonality() {
        const { years, totals } = yearCoverage();
        if (years.length < 2) return;

        const peakYear = years.reduce((best, y) => (totals[y] > totals[best] ? y : best), years[0]);
        const byMonth = (y) => MONTH_NAMES.map((_, m) => ADVANCED_DATA.filter((d) => d.year === y && d.month === m).length);
        const baseline = years.filter((y) => y !== peakYear).map(byMonth);
        const peak = byMonth(peakYear);
        const stats = MONTH_NAMES.map((month, m) => {
            const counts = baseline.map((r) => r[m]);
            return { month, mean: math.mean(counts), std: math.std(counts), peak: peak[m] };
        });

        document.getElementById('saison-title').textContent = `Saisonnalité : ${peakYear} contre les autres années`;
        setNote('saison-note',
            `${peakYear} est l'année la plus chargée (${fmtInt(totals[peakYear])} décès). Moyenne et écart-type calculés sur les ${baseline.length} autres années ` +
            `comptant au moins ${MIN_YEAR_ENTRIES} relevés. Un mois sans aucun relevé en ${peakYear} n'est pas tracé : c'est probablement un registre manquant.`);

        const x = stats.map((s) => s.month);
        const peakIdx = stats.reduce((best, s, i) => (s.peak > stats[best].peak ? i : best), 0);
        Plotly.newPlot('chart-saison', [
            { x, y: stats.map((s) => s.mean + s.std), type: 'scatter', mode: 'lines', showlegend: false, hoverinfo: 'skip', line: { width: 0 } },
            { x, y: stats.map((s) => Math.max(0, s.mean - s.std)), type: 'scatter', mode: 'lines', name: 'Moyenne ± 1 écart-type', fill: 'tonexty', fillcolor: PALETTE.bandFill, hoverinfo: 'skip', line: { width: 0 } },
            { x, y: stats.map((s) => s.mean), type: 'scatter', mode: 'lines', name: `Moyenne hors ${peakYear}`, line: { color: PALETTE.s1, width: 3 }, hovertemplate: '%{x} : %{y:.0f} décès en moyenne<extra></extra>' },
            { x, y: stats.map((s) => (s.peak > 0 ? s.peak : null)), type: 'scatter', mode: 'lines+markers', name: String(peakYear), connectgaps: false, line: { color: PALETTE.s2, width: 3 }, marker: { size: 8, color: PALETTE.s2, line: { color: '#fff', width: 2 } }, hovertemplate: '%{x} ' + peakYear + ' : %{y} décès<extra></extra>' }
        ], plotlyLayout({
            height: 460,
            margin: { t: 24 },
            yaxis: { title: { text: 'Décès par mois' }, rangemode: 'tozero' },
            xaxis: { fixedrange: true },
            legend: { orientation: 'h', y: -0.14, x: 0.5, xanchor: 'center' },
            annotations: [{
                x: MONTH_NAMES[peakIdx], y: stats[peakIdx].peak, xref: 'x', yref: 'y',
                text: `${MONTH_NAMES[peakIdx]} ${peakYear} : ${stats[peakIdx].peak}`,
                showarrow: true, arrowcolor: PALETTE.ink2, ax: 56, ay: 4,
                font: { size: 12, color: PALETTE.ink }
            }]
        }), PLOTLY_CONFIG);
    }

    function renderRegionJobs() {
        const known = ADVANCED_DATA.filter((d) => d.job_cat && d.job_cat !== 'Sans état' && d.departement !== 'Inconnu');
        const topDepts = Object.entries(_.countBy(known.filter((d) => d.departement !== 'Seine'), 'departement'))
            .sort((a, b) => b[1] - a[1]).slice(0, 15).map((x) => x[0]);
        if (topDepts.length === 0) return;

        const jobCounts = _.countBy(known, 'job_cat');
        const jobs = Object.keys(jobCounts)
            .filter((j) => j !== 'Autres')
            .sort((a, b) => jobCounts[b] - jobCounts[a])
            .concat(jobCounts['Autres'] ? ['Autres'] : []);

        const n = topDepts.map((dept) => known.filter((d) => d.departement === dept).length);
        const counts = jobs.map(() => Array(topDepts.length).fill(0));
        known.forEach((d) => {
            const x = topDepts.indexOf(d.departement);
            const y = jobs.indexOf(d.job_cat);
            if (x > -1 && y > -1) counts[y][x]++;
        });
        const z = counts.map((row) => row.map((v, x) => (n[x] ? (v / n[x]) * 100 : 0)));
        const text = z.map((row) => row.map((v) => (v >= 5 ? String(Math.round(v)) : '')));

        setNote('jobs-note',
            'Pour 100 défunts nés dans un département, part de chaque catégorie de métier (les colonnes totalisent 100 %). ' +
            'Seine exclue ; 15 départements les plus représentés ; « sans état » exclu. Les nombres affichés sont des pourcentages ≥ 5 %.');

        Plotly.react('chart-heatmap-jobs', [{
            x: topDepts.map((dept, i) => `${dept} (n = ${n[i]})`), y: jobs, z, text, customdata: counts, type: 'heatmap',
            colorscale: sequentialColorscale(), zmin: 0, zmax: Math.max(...z.flat()),
            xgap: 2, ygap: 2, texttemplate: '%{text}', textfont: { size: 10 },
            hovertemplate: '%{y} parmi les nés en %{x}<br>%{z:.1f} % (%{customdata} défunts)<extra></extra>',
            colorbar: { title: { text: '% du département' }, thickness: 12, outlinewidth: 0, ticksuffix: ' %' }
        }], plotlyLayout({
            height: 640,
            margin: { t: 8, l: 100, b: 130 },
            xaxis: { tickangle: -40, showgrid: false },
            yaxis: { autorange: 'reversed', showgrid: false }
        }), PLOTLY_CONFIG);
    }

    // One violin per group, a single hue (the group is already named on the axis), ordered by median age.
    function buildViolinTraces(groups) {
        return groups.map(([label, ages]) => {
            const name = `${label} (n = ${ages.length})`;
            const mean = ages.reduce((a, b) => a + b, 0) / ages.length;
            return {
                type: 'violin',
                x: ages,
                y: Array(ages.length).fill(name),
                name,
                orientation: 'h',
                side: 'positive',
                width: 0.9,
                spanmode: 'hard',
                points: false,
                box: { visible: true, width: 0.18, fillcolor: '#fff', line: { color: PALETTE.ink, width: 1.5 } },
                meanline: { visible: false },
                line: { color: PALETTE.s1, width: 1 },
                fillcolor: 'rgba(42, 120, 214, 0.55)',
                hovertemplate: `<b>${label}</b><br>Effectif : ${ages.length}<br>Âge médian : ${median(ages).toFixed(0)} ans<br>Âge moyen : ${mean.toFixed(1)} ans<extra></extra>`
            };
        });
    }

    function renderViolins(divId, noteId, byGroup, minCount, maxGroups, xRange, noteText) {
        const groups = Object.entries(byGroup)
            .filter(([, ages]) => ages.length >= minCount)
            .sort((a, b) => b[1].length - a[1].length)
            .slice(0, maxGroups)
            .sort((a, b) => median(a[1]) - median(b[1])); // youngest at the bottom, oldest on top
        if (groups.length === 0) return;

        setNote(noteId, noteText.replace('{n}', groups.length));
        const traces = buildViolinTraces(groups);
        Plotly.react(divId, traces, plotlyLayout({
            height: 90 + groups.length * 46,
            margin: { t: 8, l: 190, r: 16, b: 56 },
            xaxis: { title: { text: 'Âge au décès (années)' }, zeroline: false, range: xRange, dtick: 10 },
            yaxis: { title: '', categoryorder: 'array', categoryarray: traces.map((t) => t.name), showgrid: false },
            showlegend: false,
            violinmode: 'overlay'
        }), PLOTLY_CONFIG);
    }

    function renderLifeExpectancy() {
        const byJob = {};
        ADVANCED_DATA.forEach((d) => {
            if (d.age !== null && d.age > 10 && d.job_cat && d.job_cat !== 'Sans état') {
                (byJob[d.job_cat] = byJob[d.job_cat] || []).push(d.age);
            }
        });
        renderViolins('chart-life-expectancy', 'life-note', byJob, 5, 15, [10, 100],
            'Âge au décès des plus de 10 ans, pour les {n} catégories de métier les plus fréquentes, de la plus jeune (bas) à la plus âgée (haut). ' +
            'La largeur indique où se concentrent les décès ; le trait noir marque la médiane et l\'étendue interquartile.');
    }

    function renderCauseViolinPlot() {
        const byCause = {};
        ADVANCED_DATA.forEach((d) => {
            if (d.age !== null && d.cause_cat && d.cause_cat !== 'Non précisé') {
                (byCause[d.cause_cat] = byCause[d.cause_cat] || []).push(d.age);
            }
        });
        renderViolins('chart-cause-violin', 'cause-violin-note', byCause, 10, 12, [0, 100],
            'Âge au décès pour les {n} grandes familles de causes (regroupement par mots-clés), de la plus jeune (bas) à la plus âgée (haut). ' +
            'Boîte : médiane et quartiles ; forme : répartition des âges.');
    }

    // Share of the people of each sex that carry each first name (deceased + spouses).
    function renderNamesPercent() {
        const names = { M: [[], [], []], F: [[], [], []] };
        const base = { M: 0, F: 0 };
        const add = (sex, list) => {
            if (!list.some(Boolean)) return;
            base[sex]++;
            list.forEach((n, i) => { if (n) names[sex][i].push(n); });
        };
        ADVANCED_DATA.forEach((d) => {
            if (d.sexe !== 'M' && d.sexe !== 'F') return;
            add(d.sexe, d.p_defunt);
            add(d.sexe === 'M' ? 'F' : 'M', d.p_conjoint); // the spouse is of the other sex
        });

        function buildNameChart(divId, noteId, sex, title, shades) {
            const total = base[sex];
            if (!total) return;
            const perRank = names[sex].map((list) => _.countBy(list));
            const sumAll = (n) => perRank.reduce((s, c) => s + (c[n] || 0), 0);
            const topNames = Object.keys(perRank[0]).sort((a, b) => sumAll(b) - sumAll(a)).slice(0, 10);
            if (topNames.length === 0) return;
            const ordered = [...topNames].reverse(); // biggest on top in a horizontal bar chart

            setNote(noteId, `Base : ${fmtInt(total)} ${sex === 'M' ? 'hommes' : 'femmes'} (défunts et conjoints). ` +
                'Chaque barre empile la part des personnes qui portent ce prénom en 1re, 2e ou 3e position.');

            const traces = [0, 1, 2].map((rank) => ({
                y: ordered,
                x: ordered.map((n) => ((perRank[rank][n] || 0) / total) * 100),
                customdata: ordered.map((n) => perRank[rank][n] || 0),
                type: 'bar', orientation: 'h',
                name: rank === 0 ? '1er prénom' : `${rank + 1}e prénom`,
                marker: { color: shades[rank], line: { color: '#fff', width: 1.5 } },
                hovertemplate: `%{y}, ${rank === 0 ? '1er' : `${rank + 1}e`} prénom : %{x:.1f} % (%{customdata})<extra></extra>`
            }));
            Plotly.react(divId, traces, plotlyLayout({
                height: 440,
                barmode: 'stack',
                margin: { t: 8, l: 90, b: 70 },
                xaxis: { title: { text: '% des ' + (sex === 'M' ? 'hommes' : 'femmes') }, ticksuffix: ' %', rangemode: 'tozero' },
                yaxis: { showgrid: false },
                legend: { orientation: 'h', y: -0.28, x: 0.5, xanchor: 'center', traceorder: 'normal' }
            }), PLOTLY_CONFIG);
        }

        buildNameChart('chart-names-men', 'names-men-note', 'M', 'Prénoms masculins', PALETTE.maleShades);
        buildNameChart('chart-names-women', 'names-women-note', 'F', 'Prénoms féminins', PALETTE.femaleShades);
    }

    // ---- Wiring & init ----------------------------------------------------
    function bindEvents() {
        document.querySelectorAll('.pitie-app [data-page]').forEach((link) => {
            link.addEventListener('click', function (e) {
                e.preventDefault();
                showPage(this.dataset.page);
            });
        });

        const menuBtn = document.querySelector('.pitie-app .mobile-menu-button');
        if (menuBtn) menuBtn.addEventListener('click', toggleMobileMenu);

        const searchForm = document.querySelector('.pitie-app .search-form');
        if (searchForm) searchForm.addEventListener('submit', performSearch);

        const applyBtn = document.getElementById('apply-filters-btn');
        if (applyBtn) applyBtn.addEventListener('click', applyFilters);

        const resetBtn = document.getElementById('reset-filters-btn');
        if (resetBtn) resetBtn.addEventListener('click', resetFilters);

        document.querySelectorAll('.pitie-app [data-paris-view]').forEach((btn) => {
            btn.addEventListener('click', () => setParisView(btn.dataset.parisView));
        });

        const moreStatsBtn = document.getElementById('btn-more-stats');
        if (moreStatsBtn) moreStatsBtn.addEventListener('click', loadAdvancedStats);

        const causeSelect = document.getElementById('causeSelect');
        if (causeSelect) causeSelect.addEventListener('change', updateHeatmap);
    }

    function init() {
        PALETTE = readPalette();
        applyChartDefaults();
        bindEvents();
        loadCSVData();
        loadParisStreetsData();
        initializeNavigation();
    }

    document.addEventListener('DOMContentLoaded', init);

    window.PitieApp = {
        init: init,
        showPage: showPage,
        // Used by pitie-gedcom-match.js (GEDCOM search)
        getData: function () { return dbData; },
        extractHistoricalDeptRaw: extractHistoricalDeptRaw,
        resolveModernDeptCode: resolveModernDeptCode
    };
})();
