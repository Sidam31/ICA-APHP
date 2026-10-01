/*
 * Recherche par fichier GEDCOM : l'utilisateur dépose un GEDCOM, chaque individu est comparé
 * aux relevés de décès de la Pitié (dbData) avec un score de vraisemblance combinant
 *   - nom de famille et prénoms (similarité floue + phonétique française),
 *   - dates (année de naissance estimée = année de décès - âge, avec marge ; année de décès),
 *   - lieu de naissance (département historique -> départements actuels, commune, distance GPS),
 *   - bonus si le nom du conjoint du relevé correspond à un conjoint de l'individu.
 *
 * Le parseur GEDCOM et les communes géolocalisées viennent du projet Outils-genealogiques
 * (chargés à la demande, uniquement quand un fichier est déposé).
 */
(function () {
    'use strict';

    const TOOLS_BASE = 'https://sidam31.github.io/Outils-genealogiques/assets/';
    const GEDCOM_MODULE_URL = TOOLS_BASE + 'js/gedcom.js';
    const COMMUNES_GEO_URL = TOOLS_BASE + 'data/communes_geo/';
    const COMMUNE_DEPTS = [].concat(
        Array.from({ length: 19 }, (_, i) => String(i + 1).padStart(2, '0')),
        ['2A', '2B'],
        Array.from({ length: 75 }, (_, i) => String(i + 21)),
        ['971', '972', '973', '974', '976']
    );
    const MAX_MATCHES_PER_PERSON = 5;
    const MAX_GROUPS_SHOWN = 300;
    const WEIGHTS = { surname: 0.30, given: 0.15, date: 0.30, place: 0.25 };
    const SPOUSE_BONUS = 0.08;

    // Départements de l'Empire (1809-1860) qui couvraient plusieurs départements actuels.
    const DEPT_EXPANSION = {
        '75': ['75', '92', '93', '94'],
        '78': ['78', '91', '95'],
        '73': ['73', '74'],
        '74': ['74', '73'],
        '2A': ['2A', '2B'],
        '2B': ['2A', '2B']
    };

    let gedcomModulePromise = null;
    let communeIndex = null; // Promise<Map<nom normalisé, [{dept, lat, lon}]>>
    let recordIndex = null;  // construit une seule fois à partir de dbData
    let lastExport = [];

    // ---- Texte ------------------------------------------------------------
    const DIACRITICS_RE = new RegExp('[' + String.fromCharCode(0x0300) + '-' + String.fromCharCode(0x036f) + ']', 'g');

    function norm(s) {
        return String(s || '')
            .normalize('NFD').replace(DIACRITICS_RE, '')
            .toLowerCase()
            .replace(/œ/g, 'oe').replace(/æ/g, 'ae')
            .replace(/[^a-z0-9]+/g, ' ')
            .trim();
    }

    function normCity(s) {
        return norm(String(s || '').replace(/\{[^}]*\}|\([^)]*\)/g, ' '))
            .replace(/\bst\b/g, 'saint').replace(/\bste\b/g, 'sainte')
            .replace(/\bsur\b|\bsous\b|\ble\b|\bla\b|\bles\b|\bde\b|\bdu\b|\bdes\b|\bd\b|\bl\b|\ben\b/g, ' ')
            .replace(/\s+/g, ' ').trim();
    }

    // Clé phonétique française simplifiée : deux orthographes proches donnent la même clé.
    function phonetic(s) {
        let t = norm(s).replace(/[^a-z]/g, '');
        if (!t) return '';
        t = t.replace(/ph/g, 'f').replace(/ck/g, 'k').replace(/qu/g, 'k').replace(/gu(?=[eiy])/g, 'g')
            .replace(/c(?=[eiy])/g, 's').replace(/ç/g, 's').replace(/[cq]/g, 'k')
            .replace(/y/g, 'i').replace(/w/g, 'v').replace(/h/g, '')
            .replace(/eau|au/g, 'o').replace(/ou/g, 'u').replace(/ai|ei|et(?=$)/g, 'e')
            .replace(/[ae]n|[ae]m/g, 'a').replace(/on|om/g, 'o').replace(/ain|ein|in|im/g, 'i')
            .replace(/(.)\1+/g, '$1')
            .replace(/[sxtdzeo]+$/g, '');
        return t;
    }

    function jaroWinkler(a, b) {
        if (a === b) return 1;
        const la = a.length, lb = b.length;
        if (!la || !lb) return 0;
        const range = Math.max(0, Math.floor(Math.max(la, lb) / 2) - 1);
        const ma = new Array(la).fill(false), mb = new Array(lb).fill(false);
        let matches = 0;
        for (let i = 0; i < la; i++) {
            const lo = Math.max(0, i - range), hi = Math.min(lb - 1, i + range);
            for (let j = lo; j <= hi; j++) {
                if (!mb[j] && a[i] === b[j]) { ma[i] = mb[j] = true; matches++; break; }
            }
        }
        if (!matches) return 0;
        let t = 0, k = 0;
        for (let i = 0; i < la; i++) {
            if (!ma[i]) continue;
            while (!mb[k]) k++;
            if (a[i] !== b[k]) t++;
            k++;
        }
        const jaro = (matches / la + matches / lb + (matches - t / 2) / matches) / 3;
        let p = 0;
        while (p < Math.min(4, la, lb) && a[p] === b[p]) p++;
        return jaro + p * 0.1 * (1 - jaro);
    }

    // Similarité de deux noms : Jaro-Winkler, relevée si la prononciation est identique.
    function nameSim(a, b) {
        if (!a || !b) return 0;
        const s = jaroWinkler(a, b);
        const pa = phonetic(a), pb = phonetic(b);
        return pa && pa === pb ? Math.max(s, 0.92) : s;
    }

    function haversineKm(lat1, lon1, lat2, lon2) {
        const r = Math.PI / 180;
        const dLat = (lat2 - lat1) * r, dLon = (lon2 - lon1) * r;
        const a = Math.sin(dLat / 2) ** 2 + Math.cos(lat1 * r) * Math.cos(lat2 * r) * Math.sin(dLon / 2) ** 2;
        return 6371 * 2 * Math.asin(Math.sqrt(a));
    }

    function escapeHtml(str) {
        return String(str == null ? '' : str).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
    }

    // ---- Chargements à la demande -------------------------------------------
    function loadGedcomModule() {
        if (!gedcomModulePromise) gedcomModulePromise = import(GEDCOM_MODULE_URL);
        return gedcomModulePromise;
    }

    function loadCommuneIndex() {
        if (!communeIndex) {
            communeIndex = Promise.all(COMMUNE_DEPTS.map((dept) =>
                fetch(COMMUNES_GEO_URL + dept + '.json')
                    .then((r) => (r.ok ? r.json() : []))
                    .then((entries) => ({ dept, entries }))
                    .catch(() => ({ dept, entries: [] }))
            )).then((files) => {
                const map = new Map();
                files.forEach(({ dept, entries }) => entries.forEach(([names, lat, lon]) => {
                    names.forEach((n) => {
                        const key = normCity(n);
                        if (!key) return;
                        if (!map.has(key)) map.set(key, []);
                        map.get(key).push({ dept, lat, lon });
                    });
                }));
                return map;
            });
        }
        return communeIndex;
    }

    // ---- Relevés de la base --------------------------------------------------
    function parseDeathDate(s) {
        const m = String(s || '').match(/(\d{1,2})\/(\d{1,2})\/(\d{4})/);
        if (m) return { day: +m[1], month: +m[2], year: +m[3] };
        const y = String(s || '').match(/\d{4}/);
        return y ? { day: null, month: null, year: +y[0] } : null;
    }

    function parseAge(s) {
        const str = String(s || '').toLowerCase();
        const m = str.match(/\d+/);
        if (!m) return null;
        if (/mois|jour|sem/.test(str)) return 0;
        const n = parseInt(m[0], 10);
        return n >= 0 && n < 120 ? n : null;
    }

    function recordDepts(rawDept, resolve) {
        if (!rawDept) return { codes: null, belgian: false };
        const code = resolve(rawDept);
        if (!code) return { codes: null, belgian: false };
        if (code.charAt(0) === 'B') return { codes: null, belgian: true };
        return { codes: DEPT_EXPANSION[code] || [code], belgian: false };
    }

    function buildRecordIndex(app) {
        const rows = app.getData();
        const records = [];
        const byPhon = new Map(), byPrefix = new Map();
        const add = (map, key, idx) => {
            if (!key) return;
            let arr = map.get(key);
            if (!arr) map.set(key, (arr = []));
            arr.push(idx);
        };
        rows.forEach((row) => {
            const surname = norm(row['NOM']);
            if (!surname) return;
            const death = parseDeathDate(row['Date de décès']);
            if (!death) return;
            const age = parseAge(row['Âge']);
            const place = String(row['Lieu de naissance'] || '');
            const dept = recordDepts(app.extractHistoricalDeptRaw(place), app.resolveModernDeptCode);
            const rec = {
                row,
                surname,
                givens: norm(row['Prénoms']).split(' ').filter(Boolean),
                sex: row['Sexe'] === 'M' || row['Sexe'] === 'F' ? row['Sexe'] : null,
                spouseSurname: norm(row['NOM CONJOINT']),
                spouseGivens: norm(row['Prénoms Conjoint']).split(' ').filter(Boolean),
                death,
                birthEst: age == null ? null : death.year - age,
                city: normCity(place.replace(/\{[^}]*\}/g, '').split('(')[0]),
                depts: dept.codes,
                belgian: dept.belgian
            };
            const idx = records.push(rec) - 1;
            add(byPhon, phonetic(surname).slice(0, 4), idx);
            add(byPrefix, surname.slice(0, 3), idx);
        });
        return { records, byPhon, byPrefix };
    }

    // ---- Individus du GEDCOM -------------------------------------------------
    function personSummary(i, parser, deptCode) {
        const geo = i.birth.geo || (i.events.BAPM && i.events.BAPM.geo) || null;
        const spouses = [];
        (i.fams || []).forEach((fid) => {
            const f = parser.fams.get(fid);
            if (!f) return;
            const sid = f.husb === i.id ? f.wife : f.husb;
            const s = sid && parser.indis.get(sid);
            if (s && (s.surname || (s.givens && s.givens.length))) spouses.push({ display: `${s.given || ''} ${s.surname || ''}`.trim(), surname: norm(s.surname), givens: (s.givens || []).flatMap((g) => norm(g).split(' ')).filter(Boolean) });
        });
        return {
            indi: i,
            surname: norm(i.surname),
            sex: i.sex === 'M' || i.sex === 'F' ? i.sex : null,
            givens: (i.givens || []).flatMap((g) => norm(g).split(' ')).filter(Boolean),
            birthYear: i.birth.year || null,
            deathYear: i.death.year || null,
            deathDay: i.death.day || null,
            deathMonth: i.death.month || null,
            spouses,
            place: geo && (geo.city || geo.dept || geo.country) ? {
                raw: geo.raw,
                dept: geo.dept ? deptCode(geo.dept) : null,
                country: geo.country && geo.country !== 'Inconnu' ? geo.country : null,
                cities: (geo.cityChain && geo.cityChain.length ? geo.cityChain : [geo.city]).map(normCity).filter(Boolean),
                lat: geo.lat, lon: geo.lon
            } : null
        };
    }

    // ---- Scoring ------------------------------------------------------------
    function scoreGiven(p, rec) {
        if (!p.givens.length || !rec.givens.length) return { v: 0.5, known: false };
        let sum = 0, wsum = 0;
        p.givens.forEach((g, k) => {
            const w = k === 0 ? 2 : 1;
            let best = 0;
            rec.givens.forEach((r) => { best = Math.max(best, nameSim(g, r)); });
            sum += w * (best >= 0.85 ? best : best * 0.5);
            wsum += w;
        });
        return { v: sum / wsum, known: true };
    }

    // Retourne { v, reasons } ou null si les dates sont incompatibles (candidat écarté).
    function scoreDate(p, rec, slack) {
        const parts = [];
        let label = [];
        if (p.birthYear != null && rec.birthEst != null) {
            const d = Math.abs(rec.birthEst - p.birthYear);
            if (d > 1 + slack) return null;
            parts.push(d <= 1 ? 1 : 1 - (d - 1) / (1 + slack));
            label.push(`naissance ≈ ${rec.birthEst} (écart ${d} an${d > 1 ? 's' : ''})`);
        }
        if (p.birthYear != null && p.birthYear > rec.death.year) return null;
        if (p.deathYear != null) {
            const dd = Math.abs(rec.death.year - p.deathYear);
            if (dd > slack) return null;
            let s = 1 - dd / (slack + 1);
            if (dd === 0 && p.deathDay && rec.death.day && p.deathMonth != null) {
                const sameDay = p.deathDay === rec.death.day && p.deathMonth + 1 === rec.death.month;
                s = sameDay ? 1 : 0.8;
                label.push(sameDay ? 'décès : même jour' : 'décès : même année');
            } else {
                label.push(dd === 0 ? 'décès : même année' : `décès : écart ${dd} an${dd > 1 ? 's' : ''}`);
            }
            parts.push(s);
        }
        if (!parts.length) return { v: 0.4, reasons: ['âge du relevé inconnu'] };
        return { v: parts.reduce((a, b) => a + b, 0) / parts.length, reasons: label };
    }

    function scorePlace(p, rec, communes) {
        const g = p.place;
        if (!g) return { v: 0.5, reason: null };

        let deptMatch = null;
        if (rec.belgian) {
            if (g.country) deptMatch = g.country === 'Belgique';
        } else if (rec.depts) {
            if (g.dept) deptMatch = rec.depts.includes(g.dept);
            else if (g.country && g.country !== 'France') deptMatch = false;
        }

        let citySim = 0;
        if (rec.city) g.cities.forEach((c) => { citySim = Math.max(citySim, jaroWinkler(c, rec.city)); });

        // Coordonnées : celles du GEDCOM, sinon la commune retrouvée dans la base (dans le même département si connu).
        const lookup = (name, depts) => {
            const hits = communes.get(name);
            if (!hits) return null;
            const pick = depts ? hits.find((h) => depts.includes(h.dept)) : (hits.length === 1 ? hits[0] : null);
            return pick ? [pick.lat, pick.lon] : null;
        };
        let gCoord = g.lat != null && g.lon != null ? [g.lat, g.lon] : null;
        if (!gCoord) {
            for (const c of g.cities) { gCoord = lookup(c, g.dept ? [g.dept] : null); if (gCoord) break; }
        }
        const rCoord = rec.city ? lookup(rec.city, rec.depts) : null;
        const dist = gCoord && rCoord ? haversineKm(gCoord[0], gCoord[1], rCoord[0], rCoord[1]) : null;

        if (citySim >= 0.9 && deptMatch !== false) return { v: 1, reason: 'même commune' };
        if (dist != null) {
            if (dist <= 8) return { v: 0.85, reason: `commune voisine (${Math.round(dist)} km)` };
            if (dist <= 25) return { v: 0.65, reason: `à ${Math.round(dist)} km` };
            if (dist <= 60) return { v: 0.45, reason: `à ${Math.round(dist)} km` };
            return deptMatch ? { v: 0.35, reason: 'même département' } : { v: 0.05, reason: 'lieu éloigné' };
        }
        if (citySim >= 0.9) return { v: 0.3, reason: 'commune homonyme, autre département' };
        if (deptMatch === true) return { v: citySim >= 0.8 ? 0.6 : 0.5, reason: 'même département' };
        if (deptMatch === false) return { v: 0, reason: 'département différent' };
        return { v: 0.4, reason: null };
    }

    // Conjoint du relevé (nom et prénoms) comparé aux conjoints de l'individu. Renvoie null s'il n'y a
    // rien à comparer ou si rien ne correspond ; v vaut 1 (nom + prénom), 0.8 (nom seul), 0.4 (prénom seul).
    function scoreSpouse(p, rec) {
        if (!p.spouses.length || (!rec.spouseSurname && !rec.spouseGivens.length)) return null;
        let best = null;
        p.spouses.forEach((s) => {
            const nameOk = rec.spouseSurname && s.surname && nameSim(s.surname, rec.spouseSurname) >= 0.88;
            let givenOk = false;
            if (rec.spouseGivens.length && s.givens.length) {
                givenOk = s.givens.some((g) => rec.spouseGivens.some((r) => nameSim(g, r) >= 0.88));
            }
            const v = nameOk && givenOk ? 1 : nameOk ? 0.8 : givenOk ? 0.4 : 0;
            if (v && (!best || v > best.v)) {
                best = { v, label: nameOk && givenOk ? 'conjoint ✓ (nom + prénom)' : nameOk ? 'conjoint ✓ (nom)' : 'conjoint : prénom' };
            }
        });
        return best;
    }

    function matchPerson(p, idx, communes, opts) {
        const seen = new Set();
        const cand = [];
        [idx.byPhon.get(phonetic(p.surname).slice(0, 4)), idx.byPrefix.get(p.surname.slice(0, 3))].forEach((list) => {
            (list || []).forEach((k) => { if (!seen.has(k)) { seen.add(k); cand.push(k); } });
        });
        const out = [];
        for (const k of cand) {
            const rec = idx.records[k];
            if (p.sex && rec.sex && p.sex !== rec.sex) continue;
            const sn = nameSim(p.surname, rec.surname);
            if (sn < opts.nameThreshold) continue;
            const date = scoreDate(p, rec, opts.slack);
            if (!date) continue;
            const given = scoreGiven(p, rec);
            if (given.known && given.v < 0.4) continue;
            const place = scorePlace(p, rec, communes);
            let score = WEIGHTS.surname * sn + WEIGHTS.given * given.v + WEIGHTS.date * date.v + WEIGHTS.place * place.v;
            const spouse = scoreSpouse(p, rec);
            if (spouse) score += SPOUSE_BONUS * spouse.v;
            const spouseOk = spouse ? spouse.label : null;
            score = Math.min(1, score);
            if (score < opts.minScore) continue;
            out.push({ rec, score, parts: { surname: sn, given, date, place }, spouseOk });
        }
        out.sort((a, b) => b.score - a.score);
        return out.slice(0, MAX_MATCHES_PER_PERSON);
    }

    // ---- Rendu ---------------------------------------------------------------
    function pct(v) { return Math.round(v * 100) + '%'; }

    function personLabel(p) {
        const i = p.indi;
        const bits = [];
        if (p.birthYear) bits.push('° ' + p.birthYear + (p.place && p.place.raw ? ' ' + escapeHtml(p.place.raw.split(',').slice(0, 2).join(',')) : ''));
        if (p.deathYear) bits.push('† ' + p.deathYear);
        const sp = p.spouses.length ? `<br><small>⚭ ${p.spouses.map((s) => escapeHtml(s.display)).join(', ')}</small>` : '';
        return `<strong>${escapeHtml(i.given || '')} ${escapeHtml(i.surname || '')}</strong><br><small>${bits.join(' · ') || '—'}</small>${sp}`;
    }

    function matchRow(m) {
        const r = m.rec.row;
        const chips = [
            `Nom ${pct(m.parts.surname)}`,
            m.parts.given.known ? `Prénoms ${pct(m.parts.given.v)}` : null,
            ...m.parts.date.reasons,
            m.parts.place.reason ? `lieu : ${m.parts.place.reason}` : null,
            m.spouseOk
        ].filter(Boolean).map((c) => `<span class="gedcom-chip">${escapeHtml(c)}</span>`).join('');
        const spouseText = `${r['Prénoms Conjoint'] || ''} ${r['NOM CONJOINT'] || ''}`.trim();
        const link = r['Permalien'] ? `<a href="${escapeHtml(r['Permalien'])}" target="_blank" rel="noopener">acte</a>` : '';
        return `
            <div class="gedcom-match">
                <div class="gedcom-score" title="Score de vraisemblance">
                    <div class="gedcom-score-bar"><div style="width:${Math.round(m.score * 100)}%"></div></div>
                    <span>${pct(m.score)}</span>
                </div>
                <div class="gedcom-match-body">
                    <strong>${escapeHtml(r['NOM'])} ${escapeHtml(r['Prénoms'])}</strong>
                    — décédé(e) le ${escapeHtml(r['Date de décès'])}, ${escapeHtml(r['Âge'] || '?')} ans,
                    né(e) à ${escapeHtml(r['Lieu de naissance'] || '?')} ${link}
                    ${spouseText ? `<div><small>⚭ ${escapeHtml(spouseText)}</small></div>` : ''}
                    <div>${chips}</div>
                </div>
            </div>`;
    }

    function render(container, groups, stats) {
        if (!groups.length) {
            container.innerHTML = `<p class="text-center">Aucune correspondance trouvée parmi ${stats.analysed} individu(s) analysé(s). Essayez d'élargir la marge d'années, la tolérance sur les noms ou de baisser le score minimum.</p>`;
            return;
        }
        const shown = groups.slice(0, MAX_GROUPS_SHOWN);
        container.innerHTML = `
            <h3>${groups.length} individu(s) du GEDCOM avec au moins une correspondance possible</h3>
            <p class="gedcom-note">${stats.analysed} individu(s) analysé(s) sur ${stats.total} (ceux sans nom, sans date de naissance/décès exploitable ou hors du filtre de sexe sont ignorés).
            Le score est une estimation heuristique : les noms très courants produisent des homonymes, vérifiez toujours l'acte.
            <button type="button" class="btn btn-secondary" id="gedcom-export-btn">Exporter en CSV</button></p>
            <div class="table-container"><table>
                <thead><tr><th>Individu du GEDCOM</th><th>Correspondances dans la base</th></tr></thead>
                <tbody>${shown.map((g) => `<tr><td>${personLabel(g.person)}</td><td>${g.matches.map(matchRow).join('')}</td></tr>`).join('')}</tbody>
            </table></div>
            ${groups.length > shown.length ? `<p class="text-center">… et ${groups.length - shown.length} autre(s) individu(s). Relevez le score minimum pour réduire la liste, ou exportez en CSV.</p>` : ''}`;
        const btn = document.getElementById('gedcom-export-btn');
        if (btn) btn.addEventListener('click', exportCsv);
    }

    function exportCsv() {
        const head = ['GEDCOM id', 'Prénoms', 'Nom', 'Naissance', 'Décès', 'Score', 'Relevé NOM', 'Relevé Prénoms', 'Date de décès', 'Âge', 'Lieu de naissance', 'Permalien'];
        const q = (v) => '"' + String(v == null ? '' : v).replace(/"/g, '""') + '"';
        const lines = [head.map(q).join(',')];
        lastExport.forEach((g) => g.matches.forEach((m) => {
            const r = m.rec.row, i = g.person.indi;
            lines.push([i.id, i.given, i.surname, g.person.birthYear, g.person.deathYear, Math.round(m.score * 100),
                r['NOM'], r['Prénoms'], r['Date de décès'], r['Âge'], r['Lieu de naissance'], r['Permalien']].map(q).join(','));
        }));
        const blob = new Blob(['﻿' + lines.join('\r\n')], { type: 'text/csv;charset=utf-8' });
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = 'correspondances-gedcom.csv';
        a.click();
        setTimeout(() => URL.revokeObjectURL(a.href), 1000);
    }

    // ---- Orchestration ---------------------------------------------------------
    const tick = () => new Promise((resolve) => setTimeout(resolve, 0));

    async function runMatch(file) {
        const app = window.PitieApp;
        const status = document.getElementById('gedcom-status');
        const container = document.getElementById('gedcom-results');
        const setStatus = (msg) => { status.textContent = msg; };

        if (!app || !app.getData().length) {
            setStatus('La base de données est encore en cours de chargement, réessayez dans un instant.');
            return;
        }
        const opts = {
            slack: Math.max(0, parseInt(document.getElementById('gedcom-slack').value, 10) || 0),
            nameThreshold: parseFloat(document.getElementById('gedcom-name-tolerance').value),
            sex: document.getElementById('gedcom-sex').value,
            minScore: (parseInt(document.getElementById('gedcom-min-score').value, 10) || 0) / 100
        };
        container.innerHTML = '';
        try {
            setStatus('Chargement du lecteur GEDCOM…');
            const mod = await loadGedcomModule();
            setStatus('Lecture du fichier…');
            const text = await mod.readGedcomFile(file);
            const parser = new mod.GedcomParser();
            const people = parser.parse(text);

            setStatus('Chargement des communes géolocalisées…');
            const communes = await loadCommuneIndex();
            if (!recordIndex || recordIndex.size !== app.getData().length) {
                recordIndex = buildRecordIndex(app);
                recordIndex.size = app.getData().length;
            }

            const deptCode = (d) => (d ? d.split(' - ')[0] : null);
            const summaries = people
                .map((i) => personSummary(i, parser, deptCode))
                .filter((p) => p.surname && (p.birthYear || p.deathYear))
                .filter((p) => !opts.sex || p.sex === opts.sex);
            const groups = [];
            for (let n = 0; n < summaries.length; n++) {
                const matches = matchPerson(summaries[n], recordIndex, communes, opts);
                if (matches.length) groups.push({ person: summaries[n], matches });
                if (n % 150 === 0) { setStatus(`Analyse… ${n}/${summaries.length}`); await tick(); }
            }
            groups.sort((a, b) => b.matches[0].score - a.matches[0].score);
            lastExport = groups;
            setStatus(`${people.length} individus lus dans « ${file.name} ».`);
            render(container, groups, { analysed: summaries.length, total: people.length });
        } catch (err) {
            console.error('Recherche GEDCOM :', err);
            setStatus('Erreur : ' + (err && err.message ? err.message : err));
        }
    }

    function init() {
        const input = document.getElementById('gedcom-file');
        const zone = document.getElementById('gedcom-dropzone');
        if (!input || !zone) return;
        const handle = (file) => { if (file) runMatch(file); };
        input.addEventListener('change', () => handle(input.files[0]));
        ['dragenter', 'dragover'].forEach((ev) => zone.addEventListener(ev, (e) => { e.preventDefault(); zone.classList.add('dragover'); }));
        ['dragleave', 'drop'].forEach((ev) => zone.addEventListener(ev, (e) => { e.preventDefault(); zone.classList.remove('dragover'); }));
        zone.addEventListener('drop', (e) => handle(e.dataTransfer.files[0]));
    }

    document.addEventListener('DOMContentLoaded', init);
})();
