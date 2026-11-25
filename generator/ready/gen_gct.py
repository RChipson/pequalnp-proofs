#!/usr/bin/env python3
# Generator of Lean files for the existence rows of the Small algebraic case family (L-gct-241..273).
# Usage: python3 gen_gct.py <row>     (rows known: see EXAMPLES below)
# Each example is checked here with exact Fraction arithmetic before the Lean file is written.
import sys, json
from fractions import Fraction as Fr

HERE = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad/desk'

def statement(row):
    g = json.load(open(HERE + '/gaps.json'))['gaps']
    for r in g:
        if r['id'] == 'L-gct-%d' % row: return r['statement']
    raise KeyError(row)

def lean_q(q):
    q = Fr(q)
    if q.denominator == 1: return str(abs(q.numerator))
    return '(%d / %d)' % (abs(q.numerator), q.denominator)

def lean_poly(terms):
    # terms: list of (coef Fraction, exponent), written as C c * X ^ e with explicit signs
    out = ''
    for i, (c, e) in enumerate(terms):
        c = Fr(c)
        mon = 'C %s' % lean_q(c)
        if e == 1: mon += ' * X'
        elif e > 1: mon += ' * X ^ %d' % e
        if i == 0: out += ('- ' if c < 0 else '') + mon
        else: out += (' - ' if c < 0 else ' + ') + mon
    return out

def peval(terms, x):
    return sum(Fr(c) * x**e for c, e in terms)

def support_lemma(name, terms, bound):
    exps = sorted(e for _, e in terms)
    hs = ['h%d' % e for e in exps]
    setstr = '{' + ', '.join(str(e) for e in exps) + '}'
    L = []
    L.append('lemma %s_support_card : %s.support.card ≤ %d := by' % (name, name, bound))
    L.append('  have hsub : %s.support ⊆ %s := by' % (name, setstr))
    L.append('    intro n hn')
    L.append('    rw [mem_support_iff] at hn')
    L.append('    by_contra hmem')
    L.append('    apply hn')
    if len(exps) > 1:
        L.append('    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem')
        L.append('    obtain ⟨' + ', '.join(hs) + '⟩ := hmem')
    else:
        L.append('    simp only [Finset.mem_singleton] at hmem')
        L.append('    have %s := hmem' % hs[0])
    L.append('    simp [%s, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, %s, %s]' % (name, ', '.join(hs), ', '.join('Ne.symm ' + h for h in hs)))
    L.append('  calc %s.support.card ≤ (%s : Finset ℕ).card := Finset.card_le_card hsub' % (name, setstr))
    L.append('    _ ≤ %d := by decide' % bound)
    return '\n'.join(L)

ROOT_BETWEEN = '''lemma root_between (p : Polynomial ℝ) (a b : ℝ) (hab : a ≤ b)
    (h : p.eval a * p.eval b < 0) : ∃ r ∈ Set.Ioo a b, p.eval r = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨ha, hb⟩
    exact ⟨r, hr, by simpa using hr0⟩
  · have hb : p.eval b < 0 := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo' hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨hb, ha⟩
    exact ⟨r, hr, by simpa using hr0⟩'''

def T_def(points):
    L = ['noncomputable def T (k : ℕ) : ℝ :=']
    s = '  '
    for i, p in enumerate(points[:-1]):
        s += 'if k = %d then %s else ' % (i, lean_q(p) if Fr(p) >= 0 else '(-%s)' % lean_q(p))
        if (i + 1) % 4 == 0: L.append(s.rstrip()); s = '  '
    p = points[-1]
    s += lean_q(p) if Fr(p) >= 0 else '(-%s)' % lean_q(p)
    L.append(s)
    return '\n'.join(L)

def tail(ns, n, positive, hne_expr):
    # n = number of roots (points has n+1 entries); produces sign lemmas users, exists_roots
    L = []
    L.append('lemma T_lt : ∀ k : ℕ, k < %d → T k < T (k + 1) := by' % n)
    L.append('  intro k hk')
    L.append('  interval_cases k <;> simp [T] <;> norm_num')
    L.append('')
    if positive:
        L.append('lemma T_nonneg : ∀ k : ℕ, k < %d → 0 ≤ T k := by' % n)
        L.append('  intro k hk')
        L.append('  interval_cases k <;> simp [T] <;> norm_num')
        L.append('')
    L.append('lemma H_ne_zero : H ≠ 0 := by')
    L.append('  intro h')
    L.append('  have := H_sign 0 (by norm_num)')
    L.append('  simp [h] at this')
    L.append('')
    cond = ' ∧ 0 < x' if positive else ''
    L.append('lemma exists_roots : ∃ s : Finset ℝ, s.card = %d ∧ ∀ x ∈ s, x ∈ H.roots.toFinset%s := by' % (n, cond))
    L.append('  have hr : ∀ k : Fin %d, ∃ r ∈ Set.Ioo (T k) (T ((k : ℕ) + 1)), H.eval r = 0 := by' % n)
    L.append('    intro k')
    L.append('    exact root_between H _ _ (le_of_lt (T_lt k k.isLt)) (H_sign k k.isLt)')
    L.append('  choose r hr hr0 using hr')
    L.append('  have hmono : StrictMono r := by')
    L.append('    apply Fin.strictMono_iff_lt_succ.2')
    L.append('    intro i')
    L.append('    have h1 : r i.castSucc < T ((i.castSucc : ℕ) + 1) := (hr i.castSucc).2')
    L.append('    have h2 : T (i.succ : ℕ) < r i.succ := (hr i.succ).1')
    L.append('    have h3 : ((i.castSucc : Fin %d) : ℕ) + 1 = (i.succ : ℕ) := by simp' % n)
    L.append('    rw [h3] at h1')
    L.append('    exact lt_trans h1 h2')
    L.append('  refine ⟨Finset.univ.image r, ?_, ?_⟩')
    L.append('  · rw [Finset.card_image_of_injective _ hmono.injective]')
    L.append('    simp')
    L.append('  · intro x hx')
    L.append('    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx')
    if positive:
        L.append('    refine ⟨?_, lt_of_le_of_lt (T_nonneg i i.isLt) (hr i).1⟩')
    L.append('    rw [Multiset.mem_toFinset, mem_roots H_ne_zero]')
    L.append('    exact hr0 i')
    return '\n'.join(L)

def gen_fg1(row, fterms, gterms, points, tbound, N, positive=True, heart=4000000):
    # f*g+1 rows
    ns = 'PEqualNP.Outside.L_gct_%d' % row
    n = len(points) - 1
    assert n > N
    # exact check
    vals = [peval(fterms, Fr(p)) * peval(gterms, Fr(p)) + 1 for p in points]
    assert all(vals[i] * vals[i + 1] < 0 for i in range(n)), 'signs do not alternate'
    assert all(Fr(points[i]) < Fr(points[i + 1]) for i in range(n))
    if positive: assert Fr(points[0]) >= 0
    assert len(fterms) <= tbound and len(gterms) <= tbound
    L = ['import Mathlib', 'import PEqualNP.Defs', '', 'open Polynomial', '', 'namespace %s' % ns, '']
    L.append('noncomputable def F : Polynomial ℝ :=\n  ' + lean_poly(fterms)); L.append('')
    L.append('noncomputable def G : Polynomial ℝ :=\n  ' + lean_poly(gterms)); L.append('')
    L.append('noncomputable def H : Polynomial ℝ := F * G + 1'); L.append('')
    L.append(T_def(points)); L.append('')
    L.append(support_lemma('F', fterms, tbound)); L.append('')
    L.append(support_lemma('G', gterms, tbound)); L.append('')
    L.append(ROOT_BETWEEN); L.append('')
    L.append('set_option maxHeartbeats %d in' % heart)
    L.append('lemma H_sign : ∀ k : ℕ, k < %d → H.eval (T k) * H.eval (T (k + 1)) < 0 := by' % n)
    L.append('  intro k hk')
    L.append('  interval_cases k <;>')
    L.append('    simp [H, F, G, T, eval_add, eval_mul, eval_sub, eval_neg, eval_pow, eval_X, eval_C, eval_one] <;>')
    L.append('    norm_num')
    L.append('')
    L.append(tail(ns, n, positive, None)); L.append('')
    L.append('end %s' % ns); L.append('')
    st = statement(row)
    L.append('theorem %s : %s := by' % (ns, st))
    L.append('  intro hall')
    L.append('  have hb := hall %s.F %s.G' % (ns, ns))
    L.append('    ⟨%s.F_support_card, %s.G_support_card⟩' % (ns, ns))
    L.append('  obtain ⟨s, hs, hsub⟩ := %s.exists_roots' % ns)
    if positive:
        L.append('  have hle : s.card ≤ ((%s.H.roots.toFinset).filter (fun x : ℝ => 0 < x)).card :=' % ns)
        L.append('    Finset.card_le_card (fun x hx => Finset.mem_filter.mpr (hsub x hx))')
        L.append('  have hb\' : ((%s.H.roots.toFinset).filter (fun x : ℝ => 0 < x)).card ≤ %d := hb' % (ns, N))
    else:
        L.append('  have hle : s.card ≤ (%s.H.roots.toFinset).card :=' % ns)
        L.append('    Finset.card_le_card (fun x hx => hsub x hx)')
        L.append('  have hb\' : (%s.H.roots.toFinset).card ≤ %d := hb' % (ns, N))
    L.append('  omega')
    src = '\n'.join(L) + '\n'
    assert '"' not in src
    path = HERE + '/gct/L_gct_%d.lean' % row
    open(path, 'w').write(src)
    print('wrote', path, len(src.encode()), 'bytes;', n, 'roots certified, bound', N)

def ex265():
    # f = (x-1)^2 (46x-47)^2 (a nonnegative quartic with two double roots close together),
    # g = -(1/2116) * (13/10 + 100 x^3 + 11000 x^14 + 830000 x^50 + 38000000 x^170):
    # -f*g is a sum of five separated bumps on (0,1), crossing the level 1 nine times there,
    # then twice more between the double roots 1 and 47/46 and once after 47/46.
    f = [(2116, 4), (-8556, 3), (12973, 2), (-8742, 1), (2209, 0)]
    g = [(Fr(-13, 21160), 0), (Fr(-100, 2116), 3), (Fr(-11000, 2116), 14), (Fr(-830000, 2116), 50), (Fr(-38000000, 2116), 170)]
    pts = [Fr(0), Fr(1, 5), Fr(1, 3), Fr(3, 5), Fr(3, 4), Fr(6, 7), Fr(10, 11), Fr(20, 21), Fr(40, 41), Fr(1), Fr(53, 52), Fr(47, 46), Fr(8, 7)]
    gen_fg1(265, f, g, pts, 5, 11)

EXAMPLES = {265: ex265}
if __name__ == '__main__':
    for a in sys.argv[1:]:
        EXAMPLES[int(a)]()
