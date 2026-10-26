/* Equation Solver — exact rational arithmetic (BigInt), surds for irrational roots, Gaussian elimination for systems. */
(function () {
  "use strict";
  var $ = S3.$, $$ = S3.$$;
  var KEY = "eqs.v1";

  // ---------- rationals ----------
  function babs(a) { return a < 0n ? -a : a; }
  function gcd(a, b) { a = babs(a); b = babs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function R(n, d) {
    n = BigInt(n); d = d === undefined ? 1n : BigInt(d);
    if (d === 0n) throw err("Division by zero");
    if (d < 0n) { n = -n; d = -d; }
    var g = gcd(n, d) || 1n;
    return { n: n / g, d: d / g };
  }
  var ZERO = R(0), ONE = R(1);
  function add(a, b) { return R(a.n * b.d + b.n * a.d, a.d * b.d); }
  function sub(a, b) { return R(a.n * b.d - b.n * a.d, a.d * b.d); }
  function mul(a, b) { return R(a.n * b.n, a.d * b.d); }
  function div(a, b) { if (b.n === 0n) throw err("Division by zero"); return R(a.n * b.d, a.d * b.n); }
  function neg(a) { return R(-a.n, a.d); }
  function isZ(a) { return a.n === 0n; }
  function sgn(a) { return a.n > 0n ? 1 : a.n < 0n ? -1 : 0; }
  function eq(a, b) { return a.n === b.n && a.d === b.d; }
  function num(a) { return Number(a.n) / Number(a.d); }
  function err(m) { var e = new Error(m); e.eq = true; return e; }
  function str(a) { var s = a.d === 1n ? String(a.n) : a.n + "/" + a.d; return s.replace("-", "−"); }
  function approx(v) { if (!isFinite(v)) return String(v); var r = +v.toPrecision(10); return String(Math.abs(r) < 1e-12 ? 0 : r).replace("-", "−"); }
  function strA(a) { return a.d === 1n ? str(a) : str(a) + " ≈ " + approx(num(a)); }

  // Coefficients: 3, -2.5, 3/4, -1 1/2, 1e-3, Arabic digits. Empty = 0.
  function parseCoef(s) {
    s = String(s == null ? "" : s).trim().replace(/[٠-٩]/g, function (c) { return c.charCodeAt(0) - 0x660; }).replace(/٫/g, ".").replace(/[−–]/g, "-").replace(/\s+/g, " ");
    if (!s) return ZERO;
    var m;
    if ((m = /^([+-]?)(\d+) (\d+)\/(\d+)$/.exec(s))) { var v = add(R(m[2]), R(m[3], m[4])); return m[1] === "-" ? neg(v) : v; }
    if ((m = /^([+-]?)(\d+)\s*\/\s*(\d+)$/.exec(s))) { if (m[3] === "0" || /^0+$/.test(m[3])) throw err("“" + s + "” divides by zero"); return R((m[1] === "-" ? "-" : "") + m[2], m[3]); }
    if ((m = /^([+-]?)(\d*)(?:\.(\d*))?(?:e([+-]?\d+))?$/i.exec(s)) && (m[2] || m[3])) {
      var frac = m[3] || "", n = BigInt((m[2] || "0") + frac), d = 10n ** BigInt(frac.length), e = m[4] ? parseInt(m[4], 10) : 0;
      if (Math.abs(e) > 300) throw err("Exponent too large");
      if (e > 0) n *= 10n ** BigInt(e); else if (e < 0) d *= 10n ** BigInt(-e);
      return R(m[1] === "-" ? -n : n, d);
    }
    throw err("“" + s + "” is not a number. Use 3, -2.5 or 3/4.");
  }

  // ---------- square roots of rationals: √(p/q) = k·√m with m square-free ----------
  function isqrt(n) { if (n < 2n) return n; var x = BigInt(Math.floor(Math.sqrt(Number(n)))); while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; return x; }
  function squareFree(N) {
    var k = 1n, m = N, f = 2n, steps = 0;
    while (f * f <= m && steps < 200000) {
      while (m % (f * f) === 0n) { m /= f * f; k *= f; }
      f += f === 2n ? 1n : 2n; steps++;
    }
    var r = isqrt(m); if (r * r === m) { k *= r; m = 1n; }
    return { k: k, m: m };
  }
  function sqrtR(D) { var N = D.n * D.d, s = squareFree(N); return { k: R(s.k, D.d), m: s.m }; } // √(n/d) = √(n·d)/d

  // "s√m" text for a positive rational s.
  function surd(s, m) {
    if (m === 1n) return str(s);
    var top = (s.n === 1n ? "" : String(s.n)) + "√" + m;
    return s.d === 1n ? top : top + "/" + s.d;
  }

  // ---------- polynomial text ----------
  var SUPS = { 1: "", 2: "²", 3: "³" };
  function poly(cs, v) { // cs = highest degree first
    var deg = cs.length - 1, parts = [];
    cs.forEach(function (c, i) {
      var p = deg - i; if (isZ(c)) return;
      var a = { n: babs(c.n), d: c.d }, coef = p && eq(a, ONE) ? "" : str(a);
      var term = coef + (p ? (v || "x") + SUPS[p] : "");
      parts.push({ neg: c.n < 0n, t: term });
    });
    if (!parts.length) return "0";
    return parts.map(function (x, i) { return i === 0 ? (x.neg ? "−" : "") + x.t : (x.neg ? " − " : " + ") + x.t; }).join("");
  }
  function lin(cs, vars, rhs) {
    var parts = [];
    cs.forEach(function (c, i) { if (isZ(c)) return; var a = { n: babs(c.n), d: c.d }; parts.push({ neg: c.n < 0n, t: (eq(a, ONE) ? "" : str(a)) + vars[i] }); });
    var left = parts.length ? parts.map(function (x, i) { return i === 0 ? (x.neg ? "−" : "") + x.t : (x.neg ? " − " : " + ") + x.t; }).join("") : "0";
    return left + " = " + str(rhs);
  }

  // ---------- solvers (return {roots|sol, text, steps}) ----------
  function solveLinear(a, b, c) {
    var steps = ["Start: " + poly([a, b]) + " = " + str(c)];
    var rhs = sub(c, b);
    if (!isZ(b)) steps.push((sgn(b) > 0 ? "Subtract " + str(b) : "Add " + str(neg(b))) + " on both sides: " + poly([a, ZERO]) + " = " + str(rhs));
    if (isZ(a)) {
      steps.push("The x term is gone: 0 = " + str(rhs));
      return isZ(rhs) ? { kind: "all", steps: steps.concat(["0 = 0 is always true, so every x is a solution."]) } : { kind: "none", steps: steps.concat(["0 = " + str(rhs) + " is never true, so there is no solution."]) };
    }
    var x = div(rhs, a);
    if (!eq(a, ONE)) steps.push("Divide both sides by " + str(a) + ": x = " + str(x));
    return { kind: "one", roots: [{ re: x }], steps: steps };
  }

  // Root objects: {re: R} exact, {re: R, s: R, m: BigInt, sign: ±1} = re ± s√m, {re, s, m, im: true} complex, or {f: Number, fi: Number} numeric.
  function solveQuadratic(a, b, c, pre) {
    var steps = pre || [];
    if (isZ(a)) { var l = solveLinear(b, c, ZERO); l.steps = steps.concat(["a = 0, so this is a linear equation."], l.steps); return l; }
    steps.push("Equation: " + poly([a, b, c]) + " = 0, with a = " + str(a) + ", b = " + str(b) + ", c = " + str(c));
    var D = sub(mul(b, b), mul(R(4), mul(a, c)));
    steps.push("Discriminant: Δ = b² − 4ac = (" + str(b) + ")² − 4·(" + str(a) + ")·(" + str(c) + ") = " + str(D));
    var r = div(neg(b), mul(R(2), a));
    if (isZ(D)) {
      steps.push("Δ = 0, so there is one repeated real root: x = −b / 2a = " + str(r));
      return { kind: "double", roots: [{ re: r }, { re: r }], D: D, steps: steps };
    }
    var sq = sqrtR(D.n < 0n ? neg(D) : D), s = div(sq.k, mul(R(2), { n: babs(a.n), d: a.d }));
    steps.push("√" + (D.n < 0n ? "(−Δ)" : "Δ") + " = √" + str(D.n < 0n ? neg(D) : D) + " = " + surd(sq.k, sq.m) + (sq.m === 1n ? " (a perfect square, so the roots are rational)" : ""));
    steps.push("Quadratic formula: x = (−b ± √Δ) / 2a = " + str(r) + " ± " + surd(s, sq.m) + (D.n < 0n ? "i" : ""));
    if (D.n < 0n) {
      steps.push("Δ < 0, so the roots are a complex-conjugate pair.");
      return { kind: "complex", roots: [{ re: r, s: s, m: sq.m, im: true, sign: 1 }, { re: r, s: s, m: sq.m, im: true, sign: -1 }], D: D, steps: steps };
    }
    if (sq.m === 1n) {
      var x1 = sub(r, s), x2 = add(r, s);
      steps.push("So x = " + str(x1) + " or x = " + str(x2));
      steps.push("Factored: " + factorText(a, [x1, x2]));
      return { kind: "two", roots: [{ re: x1 }, { re: x2 }], D: D, steps: steps };
    }
    steps.push("Δ > 0 and not a perfect square: two irrational real roots.");
    return { kind: "two", roots: [{ re: r, s: s, m: sq.m, sign: -1 }, { re: r, s: s, m: sq.m, sign: 1 }], D: D, steps: steps };
  }
  function factorText(a, roots) {
    return (eq(a, ONE) ? "" : eq(a, R(-1)) ? "−" : str(a)) + roots.map(function (x) { return isZ(x) ? "x" : "(x " + (sgn(x) > 0 ? "− " + str(x) : "+ " + str(neg(x))) + ")"; }).join("") + " = 0";
  }
  function rootVal(x) { // [re, im] numbers
    if (x.f !== undefined) return [x.f, x.fi || 0];
    if (x.s === undefined) return [num(x.re), 0];
    var t = num(x.s) * Math.sqrt(Number(x.m));
    return x.im ? [num(x.re), x.sign * t] : [num(x.re) + x.sign * t, 0];
  }
  function rootText(x) {
    if (x.f !== undefined) return x.fi ? approx(x.f) + (x.fi < 0 ? " − " : " + ") + approx(Math.abs(x.fi)) + "i" : approx(x.f);
    if (x.s === undefined) return strA(x.re);
    var v = rootVal(x), sur = surd(x.s, x.m) + (x.im ? "i" : ""), head = isZ(x.re) ? (x.sign < 0 ? "−" : "") + sur : str(x.re) + (x.sign < 0 ? " − " : " + ") + sur;
    return head + " ≈ " + (x.im ? approx(v[0]) + (v[1] < 0 ? " − " : " + ") + approx(Math.abs(v[1])) + "i" : approx(v[0]));
  }

  // Cubic: rational root test first (exact), otherwise trigonometric / Cardano with Newton polishing.
  function divisors(n, cap) {
    n = babs(n); var out = [];
    if (n === 0n || n > 10n ** 12n) return null;
    for (var i = 1n; i * i <= n; i++) if (n % i === 0n) { out.push(i); if (i * i !== n) out.push(n / i); if (out.length > cap) return null; }
    return out;
  }
  function evalPoly(cs, x) { var v = ZERO; cs.forEach(function (c) { v = add(mul(v, x), c); }); return v; }
  function solveCubic(a, b, c, d) {
    if (isZ(a)) { var q = solveQuadratic(b, c, d, ["a = 0, so this is a quadratic equation."]); return q; }
    var steps = ["Equation: " + poly([a, b, c, d]) + " = 0"];
    if (isZ(d)) {
      steps.push("d = 0, so x is a factor: x(" + poly([a, b, c]) + ") = 0, giving x = 0");
      var q0 = solveQuadratic(a, b, c, []);
      return { kind: "cubic", roots: [{ re: ZERO }].concat(q0.roots || []), steps: steps.concat(q0.steps), note: q0.kind };
    }
    // integer coefficients
    var L = [a, b, c, d].reduce(function (acc, x) { return acc / gcd(acc, x.d) * x.d; }, 1n);
    var I = [a, b, c, d].map(function (x) { return x.n * (L / x.d); });
    var P = divisors(I[3], 5000), Q = divisors(I[0], 5000), found = null;
    if (P && Q) {
      steps.push("Rational root test: any rational root is ±p/q with p dividing " + babs(I[3]) + " and q dividing " + babs(I[0]) + ".");
      var seen = new Set();
      outer: for (var i = 0; i < Q.length; i++) for (var j = 0; j < P.length; j++) {
        for (var s = 0; s < 2; s++) {
          var cand = R(s ? -P[j] : P[j], Q[i]), key = str(cand);
          if (seen.has(key)) continue; seen.add(key);
          if (isZ(evalPoly([a, b, c, d], cand))) { found = cand; break outer; }
        }
      }
    }
    if (found) {
      // synthetic division
      var b2 = add(b, mul(a, found)), c2 = add(c, mul(b2, found));
      steps.push("x = " + str(found) + " is a root (it makes the left side 0).");
      steps.push("Divide by (x " + (sgn(found) > 0 ? "− " + str(found) : "+ " + str(neg(found))) + ") with synthetic division: " + poly([a, b2, c2]) + " = 0");
      var qd = solveQuadratic(a, b2, c2, []);
      return { kind: "cubic", roots: [{ re: found }].concat(qd.roots || []), steps: steps.concat(qd.steps) };
    }
    steps.push(P && Q ? "No rational root, so the roots are found numerically." : "The coefficients are too large for the rational root test, so the roots are found numerically.");
    var Dl = sub(add(sub(mul(R(18), mul(a, mul(b, mul(c, d)))), mul(R(4), mul(mul(b, mul(b, b)), d))), mul(mul(b, b), mul(c, c))),
      add(mul(R(4), mul(a, mul(c, mul(c, c)))), mul(R(27), mul(mul(a, a), mul(d, d)))));
    steps.push("Discriminant Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d² = " + strA(Dl) + (sgn(Dl) > 0 ? " > 0: three distinct real roots." : " < 0: one real root and a complex-conjugate pair."));
    var A = num(a), B = num(b) / A, C = num(c) / A, Dd = num(d) / A;
    var p = C - B * B / 3, qq = 2 * B * B * B / 27 - B * C / 3 + Dd, shift = -B / 3, roots;
    steps.push("Substitute x = t − b/3a to get t³ + pt + q = 0 with p ≈ " + approx(p) + ", q ≈ " + approx(qq));
    function polish(x) { for (var k = 0; k < 60; k++) { var f = ((x + B) * x + C) * x + Dd, fp = (3 * x + 2 * B) * x + C; if (!fp) break; var nx = x - f / fp; if (Math.abs(nx - x) <= 1e-15 * Math.max(1, Math.abs(x))) { x = nx; break; } x = nx; } return x; }
    if (sgn(Dl) > 0) {
      var m = 2 * Math.sqrt(-p / 3), th = Math.acos(Math.max(-1, Math.min(1, 3 * qq / (p * m)))) / 3;
      roots = [0, 1, 2].map(function (k) { return { f: polish(m * Math.cos(th - 2 * Math.PI * k / 3) + shift) }; }).sort(function (x, y) { return x.f - y.f; });
      steps.push("Trigonometric method: t = 2√(−p/3)·cos(⅓·arccos(3q/2p·√(−3/p)) − 2πk/3), k = 0, 1, 2");
    } else {
      var disc = qq * qq / 4 + p * p * p / 27, sq = Math.sqrt(Math.max(0, disc));
      var r = polish(Math.cbrt(-qq / 2 + sq) + Math.cbrt(-qq / 2 - sq) + shift);
      var e1 = B + r, e0 = C + r * e1; // x² + e1 x + e0 after dividing out (x − r)
      var re = -e1 / 2, im = Math.sqrt(Math.max(0, e0 - e1 * e1 / 4));
      roots = [{ f: r }, { f: re, fi: im }, { f: re, fi: -im }];
      steps.push("Cardano: t = ∛(−q/2 + √(q²/4 + p³/27)) + ∛(−q/2 − √(q²/4 + p³/27)), then x = t − b/3a ≈ " + approx(r));
      steps.push("Dividing out (x − " + approx(r) + ") leaves a quadratic whose roots are " + approx(re) + " ± " + approx(im) + "i");
    }
    return { kind: "cubic", roots: roots, steps: steps, numeric: true };
  }

  // Gauss–Jordan on an augmented matrix of rationals, recording each step.
  function solveSystem(M, vars) {
    var n = vars.length, rows = M.length, A = M.map(function (r) { return r.slice(); }), steps = [], row = 0, pivots = [];
    steps.push({ text: "Augmented matrix", m: snap(A) });
    for (var col = 0; col < n && row < rows; col++) {
      var r = -1;
      for (var i = row; i < rows; i++) if (!isZ(A[i][col])) { r = i; break; }
      if (r < 0) continue;
      var ops = [];
      if (r !== row) { var t = A[r]; A[r] = A[row]; A[row] = t; ops.push("R" + (row + 1) + " ↔ R" + (r + 1)); }
      var pv = A[row][col];
      if (!eq(pv, ONE)) { A[row] = A[row].map(function (x) { return div(x, pv); }); ops.push("R" + (row + 1) + " ← R" + (row + 1) + " ÷ " + paren(pv)); }
      for (i = 0; i < rows; i++) {
        if (i === row || isZ(A[i][col])) continue;
        var f = A[i][col];
        A[i] = A[i].map(function (x, j) { return sub(x, mul(f, A[row][j])); });
        ops.push("R" + (i + 1) + " ← R" + (i + 1) + (sgn(f) > 0 ? " − " + coefText(f) : " + " + coefText(neg(f))) + "R" + (row + 1));
      }
      if (ops.length) steps.push({ text: "Column " + vars[col] + ": " + ops.join(",  "), m: snap(A) });
      pivots.push(col); row++;
    }
    for (i = row; i < rows; i++) if (!isZ(A[i][n])) {
      steps.push({ text: "Row " + (i + 1) + " says 0 = " + str(A[i][n]) + ", which is impossible." });
      return { kind: "none", steps: steps };
    }
    if (pivots.length < n) {
      var free = []; for (var c = 0; c < n; c++) if (pivots.indexOf(c) < 0) free.push(c);
      var names = ["t", "s", "u"], param = {};
      free.forEach(function (fc, k) { param[fc] = names[k]; });
      var sol = vars.map(function (v, c) {
        if (param[c]) return v + " = " + param[c];
        var pr = pivots.indexOf(c), terms = [], k0 = A[pr][n];
        free.forEach(function (fc) { var co = neg(A[pr][fc]); if (!isZ(co)) terms.push({ neg: sgn(co) < 0, t: coefText({ n: babs(co.n), d: co.d }) + param[fc] }); });
        var s = isZ(k0) && terms.length ? "" : str(k0);
        terms.forEach(function (tm, k) { s += (s || k ? (tm.neg ? " − " : " + ") : (tm.neg ? "−" : "")) + tm.t; });
        return v + " = " + s;
      });
      steps.push({ text: "Only " + pivots.length + " pivot" + (pivots.length === 1 ? "" : "s") + " for " + n + " unknowns: " + free.map(function (fc) { return vars[fc]; }).join(", ") + " can be anything." });
      return { kind: "many", param: sol, steps: steps };
    }
    var vals = vars.map(function (v, c) { return A[pivots.indexOf(c)][n]; });
    steps.push({ text: "Read off the solution: " + vars.map(function (v, k) { return v + " = " + str(vals[k]); }).join(", ") });
    var check = M.every(function (r) { var s = ZERO; for (var j = 0; j < n; j++) s = add(s, mul(r[j], vals[j])); return eq(s, r[n]); });
    steps.push({ text: check ? "Check: substituting back satisfies every equation ✓" : "Check failed" });
    return { kind: "one", vals: vals, steps: steps };
  }
  function snap(A) { return A.map(function (r) { return r.map(str); }); }
  function paren(x) { return sgn(x) < 0 || x.d !== 1n ? "(" + str(x) + ")" : str(x); }
  function coefText(x) { return eq(x, ONE) ? "" : x.d !== 1n ? "(" + str(x) + ")" : str(x); }

  // ---------- UI ----------
  var MODES = {
    lin: { title: "a·x + b = c", cells: [["a", "x +"], ["b", "="], ["c", ""]], ex: ["3", "-4", "11"] },
    quad: { title: "a·x² + b·x + c = 0", cells: [["a", "x² +"], ["b", "x +"], ["c", "= 0"]], ex: ["1", "-2", "-1"] },
    cubic: { title: "a·x³ + b·x² + c·x + d = 0", cells: [["a", "x³ +"], ["b", "x² +"], ["c", "x +"], ["d", "= 0"]], ex: ["1", "-6", "11", "-6"] },
    sys2: { title: "Two equations in x and y", rows: 2, vars: ["x", "y"], ex: ["2", "3", "8", "1", "-1", "-1"] },
    sys3: { title: "Three equations in x, y and z", rows: 3, vars: ["x", "y", "z"], ex: ["1", "1", "1", "6", "0", "2", "5", "-4", "2", "5", "-1", "27"] }
  };
  var saved = S3.store(KEY) || {}, mode = MODES[saved.mode] ? saved.mode : "quad", values = saved.values || {}, lastText = "";

  function buildForm() {
    var md = MODES[mode], box = $("#form"); box.textContent = "";
    $("#formTitle").textContent = md.title;
    var vals = values[mode] || md.ex, idx = 0;
    function cell(label, aria) {
      var inp = S3.h("input", { "class": "input eq-c", inputmode: "decimal", autocomplete: "off", spellcheck: "false", "aria-label": aria, placeholder: "0" });
      inp.value = vals[idx++] || ""; return inp;
    }
    if (md.cells) {
      var row = S3.h("div", { "class": "eq-row" });
      md.cells.forEach(function (c) { row.appendChild(cell(c[0], "Coefficient " + c[0])); if (c[1]) row.appendChild(S3.h("span", { "class": "eq-t", text: c[1] })); });
      box.appendChild(row);
    } else {
      for (var r = 0; r < md.rows; r++) {
        var rw = S3.h("div", { "class": "eq-row" });
        md.vars.forEach(function (v, k) { rw.appendChild(cell(v, "Row " + (r + 1) + " coefficient of " + v)); rw.appendChild(S3.h("span", { "class": "eq-t", text: v + (k < md.vars.length - 1 ? " +" : " =") })); });
        rw.appendChild(cell("rhs", "Row " + (r + 1) + " right-hand side"));
        box.appendChild(rw);
      }
    }
    $$(".eq-c", box).forEach(function (i) { i.addEventListener("input", S3.debounce(solve, 150)); i.addEventListener("keydown", function (e) { if (e.key === "Enter") { solve(); S3.done(); } }); });
  }
  function read() { return $$("#form .eq-c").map(function (i) { return i.value; }); }

  function solve() {
    var raw = read(); values[mode] = raw; S3.store(KEY, { mode: mode, values: values });
    var res = $("#result"), st = $("#steps"); res.textContent = ""; st.textContent = ""; $("#preview").textContent = ""; lastText = "";
    try {
      var c = raw.map(parseCoef), out, lines = [];
      if (mode === "lin") { $("#preview").textContent = poly([c[0], c[1]]) + " = " + str(c[2]); out = solveLinear(c[0], c[1], c[2]); }
      else if (mode === "quad") { $("#preview").textContent = poly(c) + " = 0"; out = solveQuadratic(c[0], c[1], c[2]); }
      else if (mode === "cubic") { $("#preview").textContent = poly(c) + " = 0"; out = solveCubic(c[0], c[1], c[2], c[3]); }
      else {
        var md = MODES[mode], n = md.vars.length, M = [];
        for (var r = 0; r < md.rows; r++) M.push(c.slice(r * (n + 1), (r + 1) * (n + 1)));
        $("#preview").textContent = M.map(function (row) { return lin(row.slice(0, n), md.vars, row[n]); }).join("   ·   ");
        out = solveSystem(M, md.vars);
      }
      if (out.kind === "none") lines.push({ big: "No solution", cls: "bad" });
      else if (out.kind === "all") lines.push({ big: "Every x is a solution", cls: "ok" });
      else if (out.kind === "many") { lines.push({ big: "Infinitely many solutions", cls: "ok" }); out.param.forEach(function (p) { lines.push({ t: p }); }); }
      else if (out.vals) out.vals.forEach(function (v, k) { lines.push({ t: MODES[mode].vars[k] + " = " + strA(v) }); });
      else {
        var rs = out.roots, multi = rs.length > 1;
        if (out.kind === "double") lines.push({ t: "x = " + rootText(rs[0]), sub: "repeated root (multiplicity 2)" });
        else rs.forEach(function (x, k) { lines.push({ t: (multi ? "x" + subscript(k + 1) : "x") + " = " + rootText(x), sub: x.im || x.fi ? "complex" : "" }); });
        if (out.D) lines.push({ sub: "Discriminant Δ = " + strA(out.D) });
        if (out.numeric) lines.push({ sub: "Irrational roots, shown to 10 significant digits." });
      }
      lines.forEach(function (l) {
        if (l.big) res.appendChild(S3.h("div", { "class": "eq-big " + (l.cls || ""), text: l.big }));
        else if (l.t) res.appendChild(S3.h("div", { "class": "eq-line mono" }, [l.t, l.sub ? S3.h("span", { "class": "chip", text: l.sub }) : null]));
        else res.appendChild(S3.h("p", { "class": "faint eq-p", text: l.sub }));
      });
      lastText = lines.map(function (l) { return l.big || l.t || l.sub; }).join("\n");
      (out.steps || []).forEach(function (s) {
        if (typeof s === "string") st.appendChild(S3.h("li", { text: s }));
        else st.appendChild(S3.h("li", {}, [S3.h("span", { text: s.text }), s.m ? matrix(s.m) : null]));
      });
    } catch (e) {
      res.appendChild(S3.h("div", { "class": "eq-err", text: e.eq ? e.message : "Something went wrong: " + e.message }));
    }
  }
  function subscript(k) { return "₀₁₂₃₄₅₆₇₈₉"[k]; }
  function matrix(m) {
    var n = m[0].length - 1, t = S3.h("table", { "class": "eq-mat mono" });
    m.forEach(function (r) { var tr = S3.h("tr"); r.forEach(function (x, j) { tr.appendChild(S3.h("td", { "class": j === n ? "rhs" : "", text: x })); }); t.appendChild(tr); });
    return S3.h("div", { "class": "eq-mat-wrap" }, [t]);
  }

  function setMode(m) {
    mode = m;
    $$("#tabs button").forEach(function (b) { b.setAttribute("aria-pressed", String(b.dataset.v === m)); });
    buildForm(); solve();
  }
  $$("#tabs button").forEach(function (b) { b.addEventListener("click", function () { setMode(b.dataset.v); }); });
  $("#example").addEventListener("click", function () { values[mode] = MODES[mode].ex.slice(); buildForm(); solve(); });
  $("#clear").addEventListener("click", function () { values[mode] = []; buildForm(); solve(); var f = $(".eq-c"); if (f) f.focus(); });
  $("#copy").addEventListener("click", function () { if (!lastText) return S3.toast("Nothing to copy yet", "error"); S3.copy(($("#preview").textContent ? $("#preview").textContent + "\n" : "") + lastText); S3.done(); });
  setMode(mode);

  window.S3_DEMO = function () { values.quad = ["1", "-2", "-1"]; setMode("quad"); };

  // ---------- self-test ----------
  window.S3_SELFTEST = function () {
    var f = [];
    function ok(n, c) { if (!c) f.push(n); }
    function P(s) { return parseCoef(s); }
    function near(a, b) { return Math.abs(a - b) < 1e-9 * Math.max(1, Math.abs(b)); }
    var l = solveLinear(P("2"), P("3"), P("7")); ok("linear", l.kind === "one" && str(l.roots[0].re) === "2");
    ok("linear none/all", solveLinear(P("0"), P("1"), P("2")).kind === "none" && solveLinear(P("0"), P("1"), P("1")).kind === "all");
    ok("linear fraction", str(solveLinear(P("3/4"), P("1/2"), P("2")).roots[0].re) === "2");
    var q = solveQuadratic(P("1"), P("-3"), P("2")); ok("quad 1,2", q.kind === "two" && str(q.roots[0].re) === "1" && str(q.roots[1].re) === "2");
    var cx = solveQuadratic(P("1"), P("2"), P("5"));
    ok("quad complex -1±2i", cx.kind === "complex" && str(cx.roots[0].re) === "−1" && str(cx.roots[0].s) === "2" && cx.roots[0].m === 1n && str(cx.D) === "−16");
    ok("complex text", rootText(cx.roots[0]).indexOf("−1 + 2i") === 0 && rootText(cx.roots[1]).indexOf("−1 − 2i") === 0);
    var s2 = solveQuadratic(P("1"), P("0"), P("-2")); ok("quad ±√2", s2.roots[1].m === 2n && str(s2.roots[1].s) === "1" && near(rootVal(s2.roots[1])[0], Math.SQRT2));
    var gold = solveQuadratic(P("1"), P("-1"), P("-1")); ok("golden", rootText(gold.roots[1]).indexOf("1/2 + √5/2") === 0 && near(rootVal(gold.roots[1])[0], (1 + Math.sqrt(5)) / 2));
    var dbl = solveQuadratic(P("2"), P("4"), P("2")); ok("double root", dbl.kind === "double" && str(dbl.roots[0].re) === "−1");
    var sf = squareFree(72n); ok("square-free 72 = 6√2", sf.k === 6n && sf.m === 2n);
    var c1 = solveCubic(P("1"), P("-6"), P("11"), P("-6")), c1r = c1.roots.map(function (x) { return rootVal(x)[0]; }).sort();
    ok("cubic 1,2,3", c1r.length === 3 && near(c1r[0], 1) && near(c1r[1], 2) && near(c1r[2], 3) && c1.roots.every(function (x) { return x.f === undefined; }));
    var c2 = solveCubic(P("1"), P("0"), P("1"), P("1")); ok("cubic numeric", c2.numeric && near(c2.roots[0].f, -0.6823278038280193) && near(c2.roots[1].fi, 1.161541399997252));
    var c3 = solveCubic(P("1"), P("0"), P("-3"), P("2")); ok("cubic double", c3.roots.map(function (x) { return str(x.re); }).sort().join() === "1,1,−2");
    var c4 = solveCubic(P("1"), P("0"), P("-7"), P("6")); ok("cubic rational -3,1,2", c4.roots.map(function (x) { return str(x.re); }).sort().join() === "1,2,−3");
    var c5 = solveCubic(P("1"), P("0"), P("0"), P("-2")); ok("cubic ∛2", c5.numeric && near(c5.roots[0].f, Math.cbrt(2)));
    var c6 = solveCubic(P("1"), P("-3"), P("-1"), P("3")); ok("cubic factors to (x-3)(x²-1)", c6.roots.length === 3 && c6.roots.map(function (x) { return rootVal(x)[0]; }).sort(function (a, b) { return a - b; }).every(function (v, k) { return near(v, [-1, 1, 3][k]); }));
    var c7 = solveCubic(P("1"), P("0"), P("-3"), P("1")), w = [8, 4, 2].map(function (k) { return 2 * Math.cos(k * Math.PI / 9); }).sort(function (a, b) { return a - b; });
    ok("cubic trig branch", c7.numeric && c7.roots.length === 3 && c7.roots.every(function (x, k) { return !x.fi && near(x.f, w[k]); }));
    var sys = solveSystem([[P("1"), P("1"), P("1"), P("6")], [P("0"), P("2"), P("5"), P("-4")], [P("2"), P("5"), P("-1"), P("27")]], ["x", "y", "z"]);
    ok("3x3 (5,3,-2)", sys.kind === "one" && sys.vals.map(str).join() === "5,3,−2");
    var sysf = solveSystem([[P("2"), P("1"), P("-1"), P("8")], [P("-3"), P("-1"), P("2"), P("-11")], [P("-2"), P("1"), P("2"), P("-3")]], ["x", "y", "z"]);
    ok("3x3 (2,3,-1)", sysf.vals.map(str).join() === "2,3,−1");
    var fr = solveSystem([[P("3"), P("2"), P("1")], [P("1"), P("4"), P("2")]], ["x", "y"]); ok("2x2 fractions", fr.vals.map(str).join() === "0,1/2");
    ok("2x2 none", solveSystem([[P("1"), P("1"), P("1")], [P("2"), P("2"), P("3")]], ["x", "y"]).kind === "none");
    var many = solveSystem([[P("1"), P("1"), P("1")], [P("2"), P("2"), P("2")]], ["x", "y"]); ok("2x2 infinite", many.kind === "many" && many.param.join(";") === "x = 1 − t;y = t");
    ok("parse", str(P("-1 1/2")) === "−3/2" && str(P("0.125")) === "1/8" && str(P("2.5e-1")) === "1/4" && str(P("")) === "0" && str(P("٣")) === "3");
    var bad = false; try { P("abc"); } catch (e) { bad = e.eq; } ok("parse rejects", bad);
    return f.length ? f : true;
  };
})();
