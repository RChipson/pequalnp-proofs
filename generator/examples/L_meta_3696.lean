import Mathlib
import PEqualNP.Defs

-- An accepted incident pair must have both of its input wires among the wires the output
-- depends on, and a circuit with s gates of fan-in at most two depends on at most s + 1
-- wires. Two points lie on one common line, so the accepted pairs form a bipartite graph
-- with no four-cycle on those wires, and the counting bound for such graphs gives at
-- most 24 s pairs while s is at most 4512.
namespace PEqualNP.Outside.L_meta_3696
open PEqualNP.CircuitLowerBounds

-- The arithmetic core: with a ≤ b, a + b ≤ 4513, the incidence bound forces
-- I ≤ 24 (a + b) - 24.
lemma arith_int (a b I : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hsum : a + b ≤ 4513)
    (hI : 24 * (a + b) - 23 ≤ I) : b * (I + a * (a - 1)) < I ^ 2 := by
  set c : ℤ := 24 * a - 23 with hc
  have hc1 : 1 ≤ c := by omega
  have hT : (24 * (a + b) - 23) * ((24 * (a + b) - 23) - b) ≤ I * (I - b) := by
    have h1 : 0 ≤ (24 * (a + b) - 23) - b := by omega
    have h2 : 0 ≤ I - (24 * (a + b) - 23) := by omega
    nlinarith [mul_nonneg h2 h1, mul_nonneg h2 (by omega : (0:ℤ) ≤ I)]
  have hphi : b * (a * (a - 1)) < (24 * (a + b) - 23) * ((24 * (a + b) - 23) - b) := by
    have key : (24 * (a + b) - 23) * ((24 * (a + b) - 23) - b) - b * (a * (a - 1))
        = 552 * b ^ 2 + (47 * c - a * (a - 1)) * b + c ^ 2 := by
      rw [hc]; ring
    have hb1 : 1 ≤ b := by omega
    by_cases hA : a * (a - 1) ≤ 47 * c
    · have : 0 ≤ (47 * c - a * (a - 1)) * b := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg b, sq_nonneg c]
    · push Not at hA
      by_cases ha' : a ≤ 2255
      · set D : ℤ := a * (a - 1) - 47 * c with hD
        have hD0 : 0 < D := by omega
        have h1 : 1000 * D ≤ 46960 * c := by
          rw [hD, hc]
          nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ a - 1) (by omega : (0:ℤ) ≤ 2255 - a)]
        have h2 : (1000 * D) ^ 2 ≤ (46960 * c) ^ 2 :=
          pow_le_pow_left₀ (by omega) h1 2
        have h3 : 2208 * (552 * b ^ 2 + (47 * c - a * (a - 1)) * b + c ^ 2)
            = (1104 * b - D) ^ 2 + (2208 * c ^ 2 - D ^ 2) := by
          rw [hD]; ring
        have h4 : 0 < 2208 * c ^ 2 - D ^ 2 := by
          nlinarith [sq_nonneg c, mul_pos (by omega : (0:ℤ) < c) (by omega : (0:ℤ) < c)]
        nlinarith [sq_nonneg (1104 * b - D)]
      · have ha2 : a = 2256 := by omega
        have hb2 : b = 2256 ∨ b = 2257 := by omega
        rcases hb2 with hb2 | hb2 <;> subst ha2 <;> subst hb2 <;> norm_num
  nlinarith

lemma arith_nat (a b I s : ℕ) (h1 : I ^ 2 ≤ b * (I + (a * a - a)))
    (h2 : I ^ 2 ≤ a * (I + (b * b - b))) (hab : a + b ≤ s + 1) (hs : s ≤ 4512) :
    I ≤ 24 * s := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : I ^ 2 ≤ 0 := by simpa using h2
    have : I = 0 := by simpa using this
    omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have : I ^ 2 ≤ 0 := by simpa using h1
    have : I = 0 := by simpa using this
    omega
  by_contra hcon
  push Not at hcon
  have e1 : ((a * a - a : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
    have : a ≤ a * a := Nat.le_mul_self a
    push_cast [Nat.cast_sub this]; ring
  have e2 : ((b * b - b : ℕ) : ℤ) = (b : ℤ) * ((b : ℤ) - 1) := by
    have : b ≤ b * b := Nat.le_mul_self b
    push_cast [Nat.cast_sub this]; ring
  have h1' : (I : ℤ) ^ 2 ≤ (b : ℤ) * ((I : ℤ) + (a : ℤ) * ((a : ℤ) - 1)) := by
    have := (Nat.cast_le (α := ℤ)).mpr h1
    push_cast at this; rw [e1] at this; exact this
  have h2' : (I : ℤ) ^ 2 ≤ (a : ℤ) * ((I : ℤ) + (b : ℤ) * ((b : ℤ) - 1)) := by
    have := (Nat.cast_le (α := ℤ)).mpr h2
    push_cast at this; rw [e2] at this; exact this
  have hI : 24 * ((a : ℤ) + (b : ℤ)) - 23 ≤ (I : ℤ) := by omega
  rcases le_total a b with hle | hle
  · have := arith_int (a : ℤ) (b : ℤ) (I : ℤ) (by omega) (by omega) (by omega) hI
    omega
  · have := arith_int (b : ℤ) (a : ℤ) (I : ℤ) (by omega) (by omega) (by omega)
      (by omega)
    omega


lemma kst {α β : Type} [DecidableEq α] [DecidableEq β] (T : Finset (α × β)) (A : Finset α)
    (B : Finset β) (hA : ∀ e ∈ T, e.1 ∈ A) (hB : ∀ e ∈ T, e.2 ∈ B)
    (huniq : ∀ e ∈ T, ∀ e' ∈ T, ∀ f ∈ T, ∀ f' ∈ T, e.2 = e'.2 → f.2 = f'.2 →
      e.1 = f.1 → e'.1 = f'.1 → e.1 ≠ e'.1 → e.2 = f.2) :
    T.card ^ 2 ≤ B.card * (T.card + (A.card * A.card - A.card)) := by
  let d : β → ℕ := fun l => (T.filter fun e => e.2 = l).card
  have hsum : ∑ l ∈ B, d l = T.card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun e : α × β => e.2) (fun e he => hB e he)).symm
  have hcs : (∑ l ∈ B, d l) ^ 2 ≤ B.card * ∑ l ∈ B, d l ^ 2 := sq_sum_le_card_mul_sum_sq
  let Q := (T ×ˢ T).filter fun x : (α × β) × (α × β) => x.1.2 = x.2.2
  have hQ : ∑ l ∈ B, d l ^ 2 = Q.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : (α × β) × (α × β) => x.1.2) (t := B)
      (fun x hx => hB x.1 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)]
    apply Finset.sum_congr rfl
    intro l _
    have hfib : (Q.filter fun x => x.1.2 = l) =
        (T.filter fun e => e.2 = l) ×ˢ (T.filter fun e => e.2 = l) := by
      ext ⟨e, e'⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨he, he'⟩, h⟩, hl⟩
        exact ⟨⟨he, hl⟩, ⟨he', h.symm.trans hl⟩⟩
      · rintro ⟨⟨he, hl⟩, ⟨he', hl'⟩⟩
        exact ⟨⟨⟨he, he'⟩, hl.trans hl'.symm⟩, hl⟩
    rw [hfib, Finset.card_product, sq]
  have hQle : Q.card ≤ T.card + (A.card * A.card - A.card) := by
    have hsplit : Q = (Q.filter fun x => x.1.1 = x.2.1) ∪ (Q.filter fun x => ¬ x.1.1 = x.2.1) :=
      (Finset.filter_union_filter_not_eq _ Q).symm
    rw [hsplit]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, Finset.mem_filter,
          Finset.mem_product] at hx
        exact hx.1.1.1
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, Finset.mem_filter,
          Finset.mem_product] at hx hy
        have hx2 : x.2 = x.1 := Prod.ext hx.2.symm hx.1.2.symm
        have hy2 : y.2 = y.1 := Prod.ext hy.2.symm hy.1.2.symm
        have hxy' : x.1 = y.1 := hxy
        exact Prod.ext hxy' (by rw [hx2, hy2]; exact hxy')
    · rw [← Finset.offDiag_card]
      apply Finset.card_le_card_of_injOn (fun x => (x.1.1, x.2.1))
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, Finset.mem_filter,
          Finset.mem_product] at hx
        simp only [Finset.mem_coe, Finset.mem_offDiag]
        exact ⟨hA _ hx.1.1.1, hA _ hx.1.1.2, hx.2⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, Finset.mem_filter,
          Finset.mem_product] at hx hy
        simp only [Prod.mk.injEq] at hxy
        have hl := huniq x.1 hx.1.1.1 x.2 hx.1.1.2 y.1 hy.1.1.1 y.2 hy.1.1.2 hx.1.2 hy.1.2
          hxy.1 hxy.2 hx.2
        have h1 : x.1 = y.1 := Prod.ext hxy.1 hl
        have h2 : x.2 = y.2 := Prod.ext hxy.2 (by rw [← hx.1.2, ← hy.1.2]; exact hl)
        exact Prod.ext h1 h2
  calc T.card ^ 2 = (∑ l ∈ B, d l) ^ 2 := by rw [hsum]
    _ ≤ B.card * ∑ l ∈ B, d l ^ 2 := hcs
    _ = B.card * Q.card := by rw [hQ]
    _ ≤ B.card * (T.card + (A.card * A.card - A.card)) := Nat.mul_le_mul_left _ hQle

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def need : ℕ → List Gate → Finset ℕ → Finset ℕ
  | _, [], N => N
  | L, g :: gs, N =>
    if L ∈ need (L + 1) gs N then (need (L + 1) gs N).erase L ∪ g.inputs.toFinset
    else need (L + 1) gs N

lemma need_card (gs : List Gate) : ∀ (L : ℕ) (N : Finset ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (need L gs N).card ≤ N.card + gs.length := by
  induction gs with
  | nil => intro L N _; simp [need]
  | cons g gs ih =>
    intro L N h
    have ih' := ih (L + 1) N (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have hg := h g (by simp)
    simp only [need]
    split_ifs with hL
    · have h1 : ((need (L + 1) gs N).erase L).card + 1 = (need (L + 1) gs N).card :=
        Finset.card_erase_add_one hL
      have h2 : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hg
      have h3 := Finset.card_union_le ((need (L + 1) gs N).erase L) g.inputs.toFinset
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

lemma getD_snoc (l : List Bool) (v : Bool) (i : Nat) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma need_sem (gs : List Gate) : ∀ (N : Finset ℕ) (w w' : List Bool), w.length = w'.length →
    (∀ i ∈ need w.length gs N, w.getD i false = w'.getD i false) →
    ∀ i ∈ N, (W gs w).getD i false = (W gs w').getD i false := by
  induction gs with
  | nil =>
    intro N w w' _ h i hi
    exact h i (by simpa [need] using hi)
  | cons g gs ih =>
    intro N w w' hlen h i hi
    rw [W_cons, W_cons]
    have hneed : need w.length (g :: gs) N =
        if w.length ∈ need (w.length + 1) gs N then
          (need (w.length + 1) gs N).erase w.length ∪ g.inputs.toFinset
        else need (w.length + 1) gs N := rfl
    refine ih N _ _ (by simp [hlen]) ?_ i hi
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rw [getD_snoc, getD_snoc, ← hlen]
    by_cases h1 : k < w.length
    · rw [if_pos h1, if_pos h1]
      apply h k
      rw [hneed]
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hk⟩)
      · exact hk
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k = w.length
      · rw [if_pos h2, if_pos h2]
        subst h2
        have hmap : (g.inputs.map fun i => w.getD i false) =
            (g.inputs.map fun i => w'.getD i false) := by
          apply List.map_congr_left
          intro i' hi'
          apply h i'
          rw [hneed, if_pos hk]
          exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi')
        rw [hmap]
      · rw [if_neg h2, if_neg h2]

lemma ofFn_getD {m : Nat} (f : Fin m → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simpa using h

lemma eval_agree (C : Circuit) (m : ℕ) (z z' : Fin m → Bool)
    (h : ∀ i ∈ need m C.gates {C.output}, ∀ hi : i < m, z ⟨i, hi⟩ = z' ⟨i, hi⟩) :
    C.eval (List.ofFn z) = C.eval (List.ofFn z') := by
  have key := need_sem C.gates {C.output} (List.ofFn z) (List.ofFn z') (by simp) (by
    intro i hi
    rw [List.length_ofFn] at hi
    rw [ofFn_getD, ofFn_getD]
    split_ifs with hlt
    · exact h i hi hlt
    · rfl) C.output (by simp)
  exact key

theorem main (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (hq : 1 ≤ q)
    (huniq : ∀ a b : Fin n, a ≠ b → ∃! l : Fin n, R a l ∧ R b l) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hsound : ∀ x : Fin (n + n) → Bool,
      Fintype.card { l : Fin n // x (Fin.natAdd n l) = true } ≤ q →
      (¬ ∃ (p : Fin n) (l : Fin n), R p l ∧ x (Fin.castAdd n p) = true ∧
        x (Fin.natAdd n l) = true) →
      PEqualNP.MetaComplexity.circuitFun (n + n) C x = false)
    (hsize : C.size ≤ 4512) :
    (Finset.univ.filter (fun e : Fin n × Fin n => R e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + n) C (fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) = true)).card ≤ 24 * C.size := by
  have hNd_card : (need (n + n) C.gates {C.output}).card ≤ 1 + C.size := by
    have := need_card C.gates (n + n) {C.output} hfan
    simpa [Circuit.size] using this
  let A : Finset (Fin n) := Finset.univ.filter fun p => p.val ∈ need (n + n) C.gates {C.output}
  let B : Finset (Fin n) :=
    Finset.univ.filter fun l => n + l.val ∈ need (n + n) C.gates {C.output}
  have hAB : A.card + B.card ≤ C.size + 1 := by
    have h1 : (A.image fun p : Fin n => p.val).card = A.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have h2 : (B.image fun l : Fin n => n + l.val).card = B.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))
    have hdisj : Disjoint (A.image fun p : Fin n => p.val)
        (B.image fun l : Fin n => n + l.val) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hi'
      have := p.isLt
      omega
    have hsub : (A.image fun p : Fin n => p.val) ∪ (B.image fun l : Fin n => n + l.val) ⊆
        need (n + n) C.gates {C.output} := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hp).2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hl).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, h1, h2] at hc
    omega
  have hmem : ∀ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => R e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + n) C (fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) = true)), R e.1 e.2 ∧ e.1 ∈ A ∧ e.2 ∈ B := by
    intro e he
    obtain ⟨hR, hacc⟩ := (Finset.mem_filter.mp he).2
    have h1 : C.eval (List.ofFn fun w : Fin (n + n) =>
        decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) = true := hacc
    refine ⟨hR, ?_, ?_⟩
    · by_contra hp
      have hp' : e.1.val ∉ need (n + n) C.gates {C.output} :=
        fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hrej : PEqualNP.MetaComplexity.circuitFun (n + n) C
          (fun w : Fin (n + n) => decide (w = Fin.natAdd n e.2)) = false := by
        apply hsound
        · refine le_trans ?_ hq
          rw [Fintype.card_le_one_iff_subsingleton]
          constructor
          rintro ⟨l, hl⟩ ⟨l', hl'⟩
          simp only [decide_eq_true_eq] at hl hl'
          apply Subtype.ext
          have e1 := congrArg Fin.val (hl.trans hl'.symm)
          simp at e1
          exact Fin.ext e1
        · rintro ⟨p, l, _, hp1, _⟩
          simp only [decide_eq_true_eq] at hp1
          have e1 := congrArg Fin.val hp1
          simp at e1
          have := p.isLt
          omega
      have h2 : C.eval (List.ofFn fun w : Fin (n + n) => decide (w = Fin.natAdd n e.2)) = false :=
        hrej
      have heq : C.eval (List.ofFn fun w : Fin (n + n) =>
          decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) =
          C.eval (List.ofFn fun w : Fin (n + n) => decide (w = Fin.natAdd n e.2)) := by
        apply eval_agree
        intro i hi hlt
        have hne : i ≠ e.1.val := fun h => hp' (h ▸ hi)
        have hne' : (⟨i, hlt⟩ : Fin (n + n)) ≠ Fin.castAdd n e.1 :=
          fun h => hne (by simpa using congrArg Fin.val h)
        simp [hne']
      rw [heq, h2] at h1
      exact absurd h1 (by simp)
    · by_contra hl
      have hl' : n + e.2.val ∉ need (n + n) C.gates {C.output} :=
        fun h => hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hrej : PEqualNP.MetaComplexity.circuitFun (n + n) C
          (fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1)) = false := by
        apply hsound
        · refine le_trans (le_of_eq ?_) (Nat.zero_le q)
          rw [Fintype.card_eq_zero_iff]
          constructor
          rintro ⟨l, hl0⟩
          simp only [decide_eq_true_eq] at hl0
          have e1 := congrArg Fin.val hl0
          simp at e1
          have := e.1.isLt
          omega
        · rintro ⟨p, l, _, _, hl1⟩
          simp only [decide_eq_true_eq] at hl1
          have e1 := congrArg Fin.val hl1
          simp at e1
          have := e.1.isLt
          omega
      have h2 : C.eval (List.ofFn fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1)) = false :=
        hrej
      have heq : C.eval (List.ofFn fun w : Fin (n + n) =>
          decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) =
          C.eval (List.ofFn fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1)) := by
        apply eval_agree
        intro i hi hlt
        have hne : i ≠ n + e.2.val := fun h => hl' (h ▸ hi)
        have hne' : (⟨i, hlt⟩ : Fin (n + n)) ≠ Fin.natAdd n e.2 := by
          intro h
          have e1 := congrArg Fin.val h
          simp at e1
          omega
        show decide ((⟨i, hlt⟩ : Fin (n + n)) = Fin.castAdd n e.1 ∨
          (⟨i, hlt⟩ : Fin (n + n)) = Fin.natAdd n e.2) =
          decide ((⟨i, hlt⟩ : Fin (n + n)) = Fin.castAdd n e.1)
        simp only [hne', or_false]
      rw [heq, h2] at h1
      exact absurd h1 (by simp)
  have k1 := kst (Finset.univ.filter (fun e : Fin n × Fin n => R e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + n) C (fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) = true)) A B (fun e he => (hmem e he).2.1) (fun e he => (hmem e he).2.2) (by
    intro e he e' he' f hf f' hf' h1 h2 h3 h4 hne
    obtain ⟨l, _, hl⟩ := huniq e.1 e'.1 hne
    have a1 : e.2 = l := hl e.2 ⟨(hmem e he).1, h1 ▸ (hmem e' he').1⟩
    have a2 : f.2 = l := hl f.2 ⟨h3 ▸ (hmem f hf).1, by rw [h4, h2]; exact (hmem f' hf').1⟩
    exact a1.trans a2.symm)
  have k2 := kst ((Finset.univ.filter (fun e : Fin n × Fin n => R e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + n) C (fun w : Fin (n + n) => decide (w = Fin.castAdd n e.1 ∨ w = Fin.natAdd n e.2)) = true)).map ⟨Prod.swap, Prod.swap_injective⟩) B A (by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he
      exact (hmem e0 he0).2.2) (by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he
      exact (hmem e0 he0).2.1) (by
    intro e he e' he' f hf f' hf' h1 h2 h3 h4 hne
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨e0', he0', rfl⟩ := Finset.mem_map.mp he'
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_map.mp hf
    obtain ⟨f0', hf0', rfl⟩ := Finset.mem_map.mp hf'
    simp only [Function.Embedding.coeFn_mk, Prod.fst_swap, Prod.snd_swap] at h1 h2 h3 h4 hne ⊢
    by_contra hpp
    obtain ⟨l, _, hl⟩ := huniq e0.1 f0.1 hpp
    have a1 : e0.2 = l := hl e0.2 ⟨(hmem e0 he0).1, h3 ▸ (hmem f0 hf0).1⟩
    have a2 : e0'.2 = l := hl e0'.2 ⟨h1 ▸ (hmem e0' he0').1, by
      rw [h4, h2]; exact (hmem f0' hf0').1⟩
    exact hne (a1.trans a2.symm))
  rw [Finset.card_map] at k2
  exact arith_nat A.card B.card _ C.size k1 k2 hAB hsize

end PEqualNP.Outside.L_meta_3696

theorem PEqualNP.Outside.L_meta_3696 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) → x8 x9 → x9.size ≤ (4512 : ℕ) → (x7 x9).card ≤ (24 : ℕ) * x9.size := by
  intro x1 x2 x3 x4 h1 huniq x7 x8 C hfan hsound hsize
  exact PEqualNP.Outside.L_meta_3696.main x1 x2 x3 h1 huniq C hfan hsound hsize
