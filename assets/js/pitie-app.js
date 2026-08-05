/*
 * Pitié app logic.
 * Single IIFE namespace — nothing here touches `window` except the final
 * `window.PitieApp` export, so this script can share a page with other
 * scripts (its own copies of chart instances, taxonomies, etc. never
 * collide with a host page's globals).
 *
 * Requires (loaded before this file, in this order): Fuse.js, PapaParse,
 * D3 v7 (+ d3-cloud), Chart.js, Plotly, lodash, mathjs, and
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
        geoJsonUrl: 'https://raw.githubusercontent.com/Sidam31/ICA-APHP/refs/heads/main/Data/data_carte.geojson',
        streetsJsonUrl: 'https://raw.githubusercontent.com/Sidam31/ICA-APHP/refs/heads/main/Data/rues-paris-lazare-1844.json',
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
    let causeChartInstance = null;
    let ageHistogramInstance = null;
    let profChartInstance = null;
    let ADVANCED_DATA = [];
    let advancedStatsLoaded = false;
    let advancedStatsRetryCount = 0;
    let mapTooltip = null;
    let PALETTE = null;
    let parisStreets = [];
    let exactStreetLookup = null; // Map<normalized name/variant, street>
    let quartierInfo = new Map(); // Map<quart number, { nom, arr }> — the 48 quartiers of 1811-1849
    let domicileMatchByRow = null; // WeakMap<row, matchResult> — built once, reused across filter changes
    let domicileChartInstance = null;
    let parisMapInstance = null; // MapLibre GL instance, created once and reused across filter changes

    // ---- DA / theme -------------------------------------------------------
    // Reads the design tokens declared in assets/css/theme.css so chart
    // colors stay derived from the DA instead of being separate hardcoded
    // hex arrays scattered through this file.
    function readPalette() {
        const cs = getComputedStyle(document.documentElement);
        const v = (name) => cs.getPropertyValue(name).trim();
        return {
            sequential: Array.from({ length: 12 }, (_, i) => v(`--pitie-chart-seq-${i + 1}`)),
            categorical: Array.from({ length: 18 }, (_, i) => v(`--pitie-chart-cat-${i + 1}`)),
            male: v('--pitie-chart-male'),
            female: v('--pitie-chart-female'),
            maleShades: [1, 2, 3].map((i) => v(`--pitie-chart-male-${i}`)),
            femaleShades: [1, 2, 3].map((i) => v(`--pitie-chart-female-${i}`)),
            meanLine: v('--pitie-chart-mean-line'),
            peakLine: v('--pitie-chart-peak-line'),
            bandFill: v('--pitie-chart-band-fill'),
            mapEmpty: v('--pitie-map-empty'),
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
                const ageStr = row['Âge'].trim();
                if (!ageStr) return false;
                const ageMatch = ageStr.match(/^([0-9]*[.|,]?[0-9]*)$/);
                if (!ageMatch) return false;
                const age = parseFloat(ageMatch[1].replace(',', '.'));
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

            generateCausesChart(filteredData);
            generateWordCloud(filteredData);
            generateAgeHistogram(filteredData);
            generateProfChart(filteredData);
            generateDepartChart(filteredData);
            generateDomicileStats(filteredData);
        }
    }

    function generateWordCloud(data) {
        const nameCounts = data.reduce((acc, row) => {
            var name = row['NOM'] ? row['NOM'].trim().toUpperCase() : '';
            if (name) acc[name] = (acc[name] || 0) + 1;
            name = row['NOM CONJOINT'] ? row['NOM CONJOINT'].trim().toUpperCase() : '';
            if (name) acc[name] = (acc[name] || 0) + 1;
            return acc;
        }, {});

        const maxWords = 100;
        const words = Object.entries(nameCounts)
            .map(([text, size]) => ({ text, size }))
            .sort((a, b) => b.size - a.size)
            .slice(0, maxWords);

        const actualCount = words.length;
        document.getElementById('word-cloud-title').textContent =
            `Les ${actualCount} Noms de famille les plus fréquents`;

        var [width] = [document.getElementById('word-cloud').offsetWidth];
        const height = 300;
        if (width === 0) width = document.getElementById('project-card').offsetWidth * 0.8;
        if (width === 0) width = document.getElementById('search-card').offsetWidth * 0.8;
        if (width === 0) width = document.getElementById('join-card').offsetWidth * 0.8;
        if (width === 0) width = 300;

        const layout = d3.layout.cloud()
            .size([width, height])
            .words(words)
            .padding(5)
            .rotate(() => (~~(Math.random() * 6) - 3) * 30)
            .font('Inter')
            .fontSize((d) => Math.sqrt(d.size) * 10)
            .on('end', draw)
            .timeInterval(20);

        layout.start();

        function draw(words) {
            d3.select('#word-cloud').html('');
            d3.select('#word-cloud').append('svg')
                .attr('width', layout.size()[0])
                .attr('height', layout.size()[1])
                .append('g')
                .attr('transform', 'translate(' + layout.size()[0] / 2 + ',' + layout.size()[1] / 2 + ')')
                .selectAll('text')
                .data(words)
                .enter().append('text')
                .style('font-size', (d) => d.size + 'px')
                .style('font-family', 'Inter')
                .style('fill', PALETTE.brand)
                .attr('text-anchor', 'middle')
                .attr('transform', (d) => `translate(${[d.x, d.y]})rotate(${d.rotate})`)
                .text((d) => d.text);
        }
    }

    function generateCausesChart(data) {
        const causeCounts = data.reduce((acc, row) => {
            const cause = row['Cause de mort: espèce'] ? row['Cause de mort: espèce'].trim() : 'N/C';
            if (cause && cause !== 'N/C') acc[cause] = (acc[cause] || 0) + 1;
            return acc;
        }, {});

        var sortedCauses = Object.entries(causeCounts)
            .sort(([, a], [, b]) => b - a)
            .slice(0, 14);
        sortedCauses.push(['Autres', Object.values(causeCounts).reduce((a, b) => a + b, 0) - sortedCauses.reduce((a, [, b]) => a + b, 0)]);
        const labels = sortedCauses.map((entry) => entry[0]);
        const values = sortedCauses.map((entry) => entry[1]);

        const ctx = document.getElementById('causes-chart').getContext('2d');

        if (causeChartInstance) causeChartInstance.destroy();

        causeChartInstance = new Chart(ctx, {
            type: 'pie',
            data: {
                labels: labels,
                datasets: [{
                    label: 'Top 14 des causes de décès les plus fréquentes',
                    data: values,
                    backgroundColor: PALETTE.sequential,
                    borderColor: '#FFFFFF',
                    borderWidth: 1
                }]
            },
            options: {
                responsive: false,
                plugins: {
                    legend: { position: 'top' },
                    title: { display: false }
                }
            }
        });
    }

    function generateAgeHistogram(data) {
        const bins = {};
        const labels = [];
        for (let i = 0; i <= 100; i += 5) {
            const label = `${i}-${i + 4}`;
            labels.push(label);
            bins[label] = { M: 0, F: 0 };
        }

        data.forEach((row) => {
            const ageStr = row['Âge'];
            const sex = row['Sexe'];
            if (!ageStr || (sex !== 'M' && sex !== 'F')) return;

            const ageMatch = ageStr.match(/^([0-9]*[.|,]?[0-9]*)$/);
            if (!ageMatch) return;

            const age = parseFloat(ageMatch[1].replace(',', '.'));
            const binIndex = Math.floor(age / 5);
            const label = `${binIndex * 5}-${binIndex * 5 + 4}`;

            if (bins[label]) bins[label][sex]++;
        });

        const maleData = labels.map((label) => -bins[label].M);
        const femaleData = labels.map((label) => bins[label].F);

        const ctx = document.getElementById('age-histogram-chart').getContext('2d');
        if (ageHistogramInstance) ageHistogramInstance.destroy();

        ageHistogramInstance = new Chart(ctx, {
            type: 'bar',
            data: {
                labels: labels,
                datasets: [
                    { label: 'Hommes', data: maleData, backgroundColor: PALETTE.male, stack: 'stack' },
                    { label: 'Femmes', data: femaleData, backgroundColor: PALETTE.female, stack: 'stack' }
                ]
            },
            options: {
                indexAxis: 'y',
                responsive: true,
                scales: {
                    x: { stacked: false, ticks: { callback: (value) => Math.abs(value) } },
                    y: { stacked: true, beginAtZero: true, reverse: true }
                },
                plugins: {
                    tooltip: {
                        callbacks: {
                            label: (context) => `${context.dataset.label}: ${Math.abs(context.raw)}`
                        }
                    }
                }
            }
        });
    }

    function generateProfChart(data) {
        const profCounts = data.reduce((acc, row) => {
            var profession = row['Profession'] ? row['Profession'].trim() : 'N/C';
            if (profession && profession !== 'N/C' && profession !== 'Sans état') {
                if (profession.startsWith('Journalière') || profession.startsWith('Journalier')) profession = 'Journalier.e';
                if (profession.startsWith('Ouvrière') || profession.startsWith('Ouvrier')) profession = 'Ouvrier.e';
                if (profession.startsWith('Couturière') || profession.startsWith('Couturier')) profession = 'Couturier.e';
                if (profession === 'Tailleuse' || profession === 'Tailleur') profession = 'Tailleur.se';
                if (profession.startsWith("Porteur d'eau") || profession.startsWith("Porteuse d'eau")) profession = "Porteur.se d'eau";
                if (profession.startsWith('Soldat') || profession.startsWith('Militaire') || profession.startsWith('Infanterie') || profession.startsWith('Fusilier') || profession.startsWith('Caporal') || profession.startsWith('Garde') || profession.startsWith('Dragon') || profession.startsWith('Cavalier') || profession.startsWith('Chasseur') || profession.startsWith('Artilleur') || profession.startsWith('Voltigeur')) profession = 'Militaire';
                if (profession.startsWith('Marchande') || profession.startsWith('Marchand')) profession = 'Marchand.e';
                if (profession.startsWith('Agricultrice') || profession.startsWith('Agriculteur')) profession = 'Agriculteur.rice';
                if (profession.startsWith('Revendeur') || profession.startsWith('Revendeuse')) profession = 'Revendeur.se';

                acc[profession] = (acc[profession] || 0) + 1;
            }
            return acc;
        }, {});

        var sortedProfessions = Object.entries(profCounts)
            .sort(([, a], [, b]) => b - a)
            .slice(0, 14);
        sortedProfessions.push(['Autres', Object.values(profCounts).reduce((a, b) => a + b, 0) - sortedProfessions.reduce((a, b) => a + b[1], 0)]);
        const labels = sortedProfessions.map((entry) => entry[0]);
        const values = sortedProfessions.map((entry) => entry[1]);

        const ctx = document.getElementById('prof-chart').getContext('2d');

        if (profChartInstance) profChartInstance.destroy();

        profChartInstance = new Chart(ctx, {
            type: 'pie',
            data: {
                labels: labels,
                datasets: [{
                    label: 'Top 14 des professions les plus fréquentes',
                    data: values,
                    backgroundColor: PALETTE.sequential,
                    borderColor: '#FFFFFF',
                    borderWidth: 1
                }]
            },
            options: {
                responsive: false,
                plugins: {
                    legend: { position: 'top' },
                    title: { display: false }
                }
            }
        });
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

    function generateDepartChart(data) {
        var deptCounts = {};
        var nonRecognizedDepartments = new Set();
        data.forEach((row) => {
            const birthplace = row['Lieu de naissance'];
            if (!birthplace) return;

            const historicalDept = extractHistoricalDeptRaw(birthplace);
            if (historicalDept) {
                const modernCode = resolveModernDeptCode(historicalDept);

                if (modernCode) {
                    deptCounts[modernCode] = (deptCounts[modernCode] || 0) + 1;
                    if (modernCode === '75') { // Seine -> split into 92/93/94
                        deptCounts['92'] = (deptCounts['92'] || 0) + 1;
                        deptCounts['93'] = (deptCounts['93'] || 0) + 1;
                        deptCounts['94'] = (deptCounts['94'] || 0) + 1;
                    }
                    if (modernCode === '78') { // Seine-et-Oise -> split into 91/92/95
                        deptCounts['91'] = (deptCounts['91'] || 0) + 1;
                        deptCounts['92'] = (deptCounts['92'] || 0) + 1;
                        deptCounts['95'] = (deptCounts['95'] || 0) + 1;
                    }
                    if (modernCode === 'B11') { // Brabant -> also counts toward Brabant Flamand
                        deptCounts['B02'] = (deptCounts['B02'] || 0) + 1;
                    }
                    if (modernCode === '73') { // Mont-Blanc -> merged into Haute-Savoie
                        deptCounts['74'] = (deptCounts['74'] || 0) + 1;
                    }
                    if (modernCode === '2A') { // Corse -> split into Corse-du-Sud / Haute-Corse
                        deptCounts['2B'] = (deptCounts['2B'] || 0) + 1;
                    }
                } else {
                    nonRecognizedDepartments.add(historicalDept);
                }
            }
        });
        if (nonRecognizedDepartments.size > 0) {
            console.warn('Départements non reconnus:', Array.from(nonRecognizedDepartments).join(', '));
        }

        fetch(CONFIG.geoJsonUrl)
            .then((response) => response.json())
            .then((geojson) => drawFranceMap(geojson, deptCounts))
            .catch((error) => {
                console.error('Erreur lors du chargement de la carte:', error);
                document.getElementById('france-map').innerHTML =
                    '<p style="color: var(--pitie-danger);">Erreur lors du chargement de la carte.</p>';
            });
    }

    function drawFranceMap(geojson, deptCounts) {
        const container = document.getElementById('france-map');
        container.innerHTML = '';
        mapTooltip = null; // container was cleared, any previously appended tooltip node is gone with it

        const width = Math.min(container.offsetWidth || 600, 600);
        const height = 600;

        const svg = d3.select('#france-map')
            .append('svg')
            .attr('width', width)
            .attr('height', height);

        const projection = d3.geoConicConformal()
            .center([2.454071, 46.279229])
            .scale(2800)
            .translate([width / 2, height / 2]);

        const path = d3.geoPath().projection(projection);

        const maxCount = Math.max(...Object.values(deptCounts));
        // One scale, reused for both the fill and the legend gradient below,
        // so they can never drift out of sync with each other.
        const colorScale = d3.scaleSequentialSqrt(d3.interpolateBlues).domain([0, maxCount]);

        if (!mapTooltip) {
            mapTooltip = document.querySelector('.pitie-app').appendChild(document.createElement('div'));
        }
        const tooltip = d3.select(mapTooltip)
            .style('position', 'absolute')
            .style('background', 'white')
            .style('padding', '8px')
            .style('border', '1px solid #ccc')
            .style('border-radius', '4px')
            .style('pointer-events', 'none')
            .style('opacity', 0)
            .style('font-size', '12px')
            .style('box-shadow', '0 2px 4px rgba(0,0,0,0.2)');

        svg.selectAll('path')
            .data(geojson.features)
            .enter()
            .append('path')
            .attr('d', path)
            .attr('fill', (d) => {
                const code = d.properties.code;
                const count = deptCounts[code] || 0;
                return count > 0 ? colorScale(count) : PALETTE.mapEmpty;
            })
            .attr('stroke', PALETTE.mapStroke)
            .attr('stroke-width', 0.5)
            .on('mouseover', function (event, d) {
                const code = d.properties.code;
                const count = deptCounts[code] || 0;
                const name = d.properties.nom;

                d3.select(this).attr('stroke-width', 2).attr('stroke', PALETTE.brand);

                tooltip.transition().duration(200).style('opacity', 1);
                const label = code.startsWith('B') ? `<strong>${name}</strong>` : `<strong>${name} (${code})</strong>`;
                tooltip.html(`${label}<br/>Naissances: ${count}`)
                    .style('left', (event.pageX + 10) + 'px')
                    .style('top', (event.pageY - 28) + 'px');
            })
            .on('mouseout', function () {
                d3.select(this).attr('stroke-width', 0.5).attr('stroke', PALETTE.mapStroke);
                tooltip.transition().duration(200).style('opacity', 0);
            });

        const legendWidth = 200;
        const legendHeight = 20;
        const legend = svg.append('g')
            .attr('transform', `translate(${width - legendWidth - 20}, ${height - 60})`);

        const legendScale = d3.scaleLinear()
            .domain([0, maxCount])
            .range([0, legendWidth]);

        const legendAxis = d3.axisBottom(legendScale)
            .ticks(5)
            .tickFormat((d) => Math.round(d));

        const defs = svg.append('defs');
        const linearGradient = defs.append('linearGradient').attr('id', 'legend-gradient');

        linearGradient.selectAll('stop')
            .data(d3.range(0, 1.1, 0.1))
            .enter()
            .append('stop')
            .attr('offset', (d) => `${d * 100}%`)
            .attr('stop-color', (d) => colorScale(d * maxCount));

        legend.append('rect')
            .attr('width', legendWidth)
            .attr('height', legendHeight)
            .style('fill', 'url(#legend-gradient)');

        legend.append('g')
            .attr('transform', `translate(0, ${legendHeight})`)
            .call(legendAxis);
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
            summaryEl.textContent =
                `${matchedCount.toLocaleString('fr-FR')} domiciles localisés · ` +
                `${outsideParisCount.toLocaleString('fr-FR')} hors Paris · ` +
                `${unmatchedCount.toLocaleString('fr-FR')} non reconnus`;
        }

        if (matchedCount > 0) {
            drawQuartierChart(quartierCounts);
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

        const ctx = document.getElementById('domicile-arr-chart').getContext('2d');
        if (domicileChartInstance) domicileChartInstance.destroy();

        domicileChartInstance = new Chart(ctx, {
            type: 'bar',
            data: {
                labels: labels,
                datasets: [{
                    label: 'Domiciles par quartier (1811-1849)',
                    data: values,
                    backgroundColor: PALETTE.brand
                }]
            },
            options: {
                indexAxis: 'y',
                responsive: false,
                plugins: { legend: { display: false } },
                scales: { x: { beginAtZero: true } }
            }
        });
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
            parisMapInstance.setPaintProperty('domiciles-point', 'circle-radius', [
                'interpolate', ['linear'], ['get', 'count'], 1, 3, maxCount, 18
            ]);
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
                layers: [{ id: 'osm', type: 'raster', source: 'osm' }]
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
                    'circle-radius': ['interpolate', ['linear'], ['get', 'count'], 1, 3, maxCount, 18],
                    'circle-color': ['match', ['get', 'geoSource'], 'quartier', '#e67e22', PALETTE.brand],
                    'circle-opacity': ['match', ['get', 'geoSource'], 'quartier', 0.5, 0.75],
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
        return extractHistoricalDeptRaw(val) || 'Inconnu';
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

            let ageStr = getValueAdvanced(d, ['Âge', 'Age', 'age']);
            let age = null;
            if (ageStr) {
                let s = ageStr.toString().toLowerCase().replace(',', '.');
                let val = parseFloat(s.match(/[\d\.]+/));
                if (!isNaN(val)) {
                    if (s.includes('mois')) age = val / 12;
                    else if (s.includes('jour')) age = 0;
                    else age = val;
                }
            }

            let sexeStr = getValueAdvanced(d, ['Sexe']);
            let sexe = (sexeStr && sexeStr.toLowerCase().startsWith('f')) ? 'F' : 'M';

            let causeStr = getValueAdvanced(d, ['Cause de mort: espèce', 'Cause', 'Maladie', 'Observations', 'Genre de mort']);

            return {
                date: date,
                year: date ? date.getFullYear() : null,
                month: date ? date.getMonth() : null,
                age: age,
                sexe: sexe,
                job_cat: categorizeAdvanced(getValueAdvanced(d, ['Profession', 'Metier']), jobTaxonomy, 'Autres'),
                cause_cat: categorizeAdvanced(causeStr, causeTaxonomy, 'Autres'),
                cause_raw: causeStr,
                departement: extractDepartmentAdvanced(getValueAdvanced(d, ['Lieu de naissance', 'Commune de naissance'])),
                p_defunt: cleanPrenoms(getValueAdvanced(d, ['Prénoms', 'Prenoms', 'Prénom'])),
                p_conjoint: cleanPrenoms(getValueAdvanced(d, ['Prénoms Conjoint', 'Prenoms Conjoint']))
            };
        }).filter((d) => d.date != null && d.year >= CONFIG.dataYearRange[0] && d.year <= CONFIG.dataYearRange[1]);

        const statusEl = document.getElementById('advanced-stats-status');
        statusEl.textContent = `✅ Statistiques avancées chargées (${ADVANCED_DATA.length} entrées analysées)`;
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

        advancedStatsLoaded = true;

        document.getElementById('advanced-stats').scrollIntoView({ behavior: 'smooth' });
    }

    function populateCauseDropdown() {
        let counts = _.countBy(ADVANCED_DATA, 'cause_cat');
        let sel = document.getElementById('causeSelect');
        sel.innerHTML = '<option value="All">Toutes les causes</option>';
        Object.entries(counts).sort((a, b) => b[1] - a[1]).forEach(([cause, count]) => {
            let opt = document.createElement('option');
            opt.value = cause;
            opt.text = `${cause} (${count})`;
            sel.add(opt);
        });
    }

    function updateHeatmap() {
        if (ADVANCED_DATA.length === 0) return;

        let selectedCause = document.getElementById('causeSelect').value;
        let filteredAdvData = (selectedCause === 'All')
            ? ADVANCED_DATA
            : ADVANCED_DATA.filter((d) => d.cause_cat === selectedCause);

        let years = _.uniq(ADVANCED_DATA.map((d) => d.year)).sort();
        let monthNames = ['Jan', 'Fév', 'Mar', 'Avr', 'Mai', 'Juin', 'Juil', 'Aoû', 'Sep', 'Oct', 'Nov', 'Déc'];
        let z = Array(12).fill(0).map(() => Array(years.length).fill(0));

        filteredAdvData.forEach((d) => {
            let yIdx = years.indexOf(d.year);
            if (yIdx > -1 && d.month !== null) z[d.month][yIdx]++;
        });

        let smartMax = calculateSmartMax(z);

        Plotly.react('chart-heatmap-deaths', [{
            x: years, y: monthNames, z: z, type: 'heatmap',
            colorscale: 'Reds', zmin: 0, zmax: smartMax,
            colorbar: { title: 'Décès' }
        }], {
            title: `Intensité des Décès : ${selectedCause}`,
            margin: { t: 50, l: 60 },
            xaxis: { type: 'category', tickmode: 'array', tickvals: years, ticktext: years.map(String) }
        });
    }

    function renderSeasonality() {
        let years = _.uniq(ADVANCED_DATA.map((d) => d.year)).sort();
        let monthNames = ['Jan', 'Fév', 'Mar', 'Avr', 'Mai', 'Juin', 'Juil', 'Aoû', 'Sep', 'Oct', 'Nov', 'Déc'];
        let stats = [];

        let yearCounts = _.countBy(ADVANCED_DATA, 'year');
        let peakYear = Object.entries(yearCounts).sort((a, b) => b[1] - a[1])[0];
        let peakYearNum = peakYear ? parseInt(peakYear[0], 10) : years[0];

        for (let m = 0; m < 12; m++) {
            let counts = years.filter((y) => y !== peakYearNum).map((y) => ADVANCED_DATA.filter((d) => d.year === y && d.month === m).length);
            let countPeak = ADVANCED_DATA.filter((d) => d.year === peakYearNum && d.month === m).length;
            if (counts.length > 0) {
                stats.push({ month: monthNames[m], mean: math.mean(counts), std: math.std(counts), valPeak: countPeak });
            }
        }

        if (stats.length === 0) return;

        Plotly.newPlot('chart-saison', [
            { x: stats.map((s) => s.month), y: stats.map((s) => s.mean), type: 'scatter', mode: 'lines', name: `Moyenne (Hors ${peakYearNum})`, line: { color: PALETTE.meanLine, width: 4 } },
            { x: stats.map((s) => s.month), y: stats.map((s) => s.mean + s.std), type: 'scatter', mode: 'lines', showlegend: false, line: { width: 0 } },
            { x: stats.map((s) => s.month), y: stats.map((s) => s.mean - s.std), type: 'scatter', mode: 'lines', name: 'Zone Normale (±1σ)', fill: 'tonexty', fillcolor: PALETTE.bandFill, line: { width: 0 } },
            { x: stats.map((s) => s.month), y: stats.map((s) => s.valPeak), type: 'scatter', mode: 'markers+lines', name: `Année ${peakYearNum}`, line: { color: PALETTE.peakLine, dash: 'dot' } }
        ], { title: `Saisonnalité & Comparaison avec ${peakYearNum}`, margin: { t: 50 } });
    }

    function renderRegionJobs() {
        let topDepts = Object.entries(_.countBy(ADVANCED_DATA, 'departement'))
            .filter((x) => x[0] !== 'Inconnu' && x[0] !== '75' && x[0] !== 'Seine')
            .sort((a, b) => b[1] - a[1]).slice(0, 15).map((x) => x[0]);

        let jobCounts = _.countBy(ADVANCED_DATA.filter((d) => d.job_cat && d.job_cat !== 'Sans état'), 'job_cat');
        let taxos = Object.entries(jobCounts).sort((a, b) => b[1] - a[1]).map((x) => x[0]);

        let z = taxos.map(() => Array(topDepts.length).fill(0));

        ADVANCED_DATA.forEach((d) => {
            let xIdx = topDepts.indexOf(d.departement);
            let yIdx = taxos.indexOf(d.job_cat);
            if (xIdx > -1 && yIdx > -1) z[yIdx][xIdx]++;
        });

        let taxosReversed = [...taxos].reverse();
        let zReversed = [...z].reverse();

        Plotly.newPlot('chart-heatmap-jobs', [{
            x: topDepts, y: taxosReversed, z: zReversed, type: 'heatmap',
            colorscale: 'Viridis', zmin: 0, zmax: calculateSmartMax(z)
        }], { title: 'Origine Provinciale des Métiers', margin: { l: 120, t: 50 } });
    }

    function buildViolinTraces(groups, colors) {
        return groups.map(([label, ages], index) => ({
            type: 'violin',
            x: ages,
            y: Array(ages.length).fill(label),
            name: `${label} (n=${ages.length})`,
            orientation: 'h',
            side: 'positive',
            box: { visible: true },
            meanline: { visible: true },
            line: { color: colors[index % colors.length] },
            fillcolor: colors[index % colors.length],
            opacity: 0.7,
            points: false,
            scalemode: 'width',
            width: 0.8,
            hovertemplate: `<b>${label}</b><br>` +
                `Effectif: ${ages.length} personnes<br>` +
                `Âge moyen: ${(ages.reduce((a, b) => a + b, 0) / ages.length).toFixed(1)} ans<br>` +
                '<extra></extra>'
        }));
    }

    function renderLifeExpectancy() {
        let jobsData = {};
        ADVANCED_DATA.forEach((d) => {
            if (d.age !== null && d.age > 10 && d.job_cat && d.job_cat !== 'Sans état') {
                (jobsData[d.job_cat] = jobsData[d.job_cat] || []).push(d.age);
            }
        });

        let sortedJobs = Object.entries(jobsData)
            .filter(([, ages]) => ages.length >= 5)
            .sort((a, b) => b[1].length - a[1].length)
            .slice(0, 15);

        if (sortedJobs.length === 0) return;

        let categoryOrder = sortedJobs.map(([job]) => job).reverse();
        let traces = buildViolinTraces(sortedJobs, PALETTE.categorical);

        Plotly.newPlot('chart-life-expectancy', traces, {
            title: "Distribution de l'âge au décès par métier (>10 ans)",
            xaxis: { title: 'Âge (années)', zeroline: false, range: [10, 100] },
            yaxis: { title: '', categoryorder: 'array', categoryarray: categoryOrder },
            showlegend: false,
            margin: { l: 120, t: 50, r: 20, b: 50 }
        });
    }

    function renderCauseViolinPlot() {
        let causesData = {};
        ADVANCED_DATA.forEach((d) => {
            if (d.age !== null && d.age >= 0 && d.cause_cat && d.cause_cat !== 'Non précisé') {
                (causesData[d.cause_cat] = causesData[d.cause_cat] || []).push(d.age);
            }
        });

        let sortedCauses = Object.entries(causesData)
            .filter(([, ages]) => ages.length >= 10)
            .sort((a, b) => b[1].length - a[1].length)
            .slice(0, 12);

        if (sortedCauses.length === 0) return;

        let categoryOrder = sortedCauses.map(([cause]) => cause).reverse();
        let traces = buildViolinTraces(sortedCauses, PALETTE.categorical);

        Plotly.newPlot('chart-cause-violin', traces, {
            title: "Distribution de l'âge au décès selon la cause",
            xaxis: { title: 'Âge au décès (années)', zeroline: false, range: [0, 100] },
            yaxis: { title: '', categoryorder: 'array', categoryarray: categoryOrder },
            showlegend: false,
            margin: { t: 50, b: 50, l: 150, r: 20 }
        });
    }

    function renderNamesPercent() {
        let namesM = [[], [], []];
        let namesF = [[], [], []];
        let totalMen = 0;
        let totalWomen = 0;

        ADVANCED_DATA.forEach((d) => {
            if (d.sexe === 'M') {
                totalMen++;
                [0, 1, 2].forEach((i) => { if (d.p_defunt[i]) namesM[i].push(d.p_defunt[i]); });
                [0, 1, 2].forEach((i) => { if (d.p_conjoint[i]) namesF[i].push(d.p_conjoint[i]); });
            } else {
                totalWomen++;
                [0, 1, 2].forEach((i) => { if (d.p_defunt[i]) namesF[i].push(d.p_defunt[i]); });
                [0, 1, 2].forEach((i) => { if (d.p_conjoint[i]) namesM[i].push(d.p_conjoint[i]); });
            }
        });

        if (totalMen === 0) totalMen = 1;
        if (totalWomen === 0) totalWomen = 1;

        function buildNameChart(divId, nameArray, title, totalPop, colorShades) {
            let counts1 = _.countBy(nameArray[0]);
            let topNames = Object.entries(counts1).sort((a, b) => b[1] - a[1]).slice(0, 10).map((x) => x[0]);

            if (topNames.length === 0) return;

            let traces = [];
            [0, 1, 2].forEach((rank, i) => {
                let counts = _.countBy(nameArray[rank]);
                let percentages = topNames.map((n) => ((counts[n] || 0) / totalPop) * 100);
                traces.push({
                    x: topNames,
                    y: percentages,
                    type: 'bar',
                    name: `${i + 1}${i === 0 ? 'er' : 'ème'} Prénom`,
                    marker: { color: colorShades[i] }
                });
            });

            Plotly.newPlot(divId, traces, {
                title: title + ` (Base: ${totalPop})`,
                barmode: 'group',
                yaxis: { title: '% de la population', ticksuffix: '%' },
                legend: { orientation: 'h', y: 1.15 },
                margin: { t: 80 }
            });
        }

        buildNameChart('chart-names-men', namesM, 'Prénoms Masculins', totalMen, PALETTE.maleShades);
        buildNameChart('chart-names-women', namesF, 'Prénoms Féminins', totalWomen, PALETTE.femaleShades);
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

        const moreStatsBtn = document.getElementById('btn-more-stats');
        if (moreStatsBtn) moreStatsBtn.addEventListener('click', loadAdvancedStats);

        const causeSelect = document.getElementById('causeSelect');
        if (causeSelect) causeSelect.addEventListener('change', updateHeatmap);
    }

    function init() {
        PALETTE = readPalette();
        bindEvents();
        loadCSVData();
        loadParisStreetsData();
        initializeNavigation();
    }

    document.addEventListener('DOMContentLoaded', init);

    window.PitieApp = { init: init, showPage: showPage };
})();
