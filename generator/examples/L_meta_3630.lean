import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3630

open PEqualNP.CircuitLowerBounds

-- Where a wire of the old circuit sits in the new one: inputs stay, the first given wire is
-- the new first gate, the second given wire is at position t, later wires move up by s.
def sig (t s k : ℕ) : ℕ := if k < 9 then k else if k = 9 then 10 else if k = 10 then t else k + s

def mapGate (t s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig t s)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (t s : ℕ) (WC WD : List Bool) : Prop :=
  WD.length = WC.length + s ∧ 11 ≤ WC.length ∧ ∀ k, WD.getD (sig t s k) false = WC.getD k false

lemma rel_step (t s : ℕ) (ht : t < 11 + s) (WC WD : List Bool) (g : Gate) (h : Rel t s WC WD) :
    Rel t s (step WC g) (step WD (mapGate t s g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (mapGate t s g).op.eval ((mapGate t s g).inputs.map fun i => WD.getD i false)
      = g.op.eval (g.inputs.map fun i => WC.getD i false) := by
    simp only [mapGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step, h1]; omega, by simp [step]; omega, ?_⟩
  intro k
  simp only [step, hv]
  rcases Nat.lt_trichotomy k WC.length with hk | hk | hk
  · have hlt : sig t s k < WD.length := by
      unfold sig
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hk]
    exact h3 k
  · have he : sig t s k = WD.length := by
      unfold sig
      split_ifs <;> omega
    rw [he, hk, List.getD_append_right _ _ _ _ (le_refl _),
      List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · have hge : WD.length < sig t s k := by
      unfold sig
      split_ifs <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (t s : ℕ) (ht : t < 11 + s) (gs : List Gate) :
    ∀ WC WD : List Bool, Rel t s WC WD →
      Rel t s (gs.foldl step WC) ((gs.map (mapGate t s)).foldl step WD) := by
  induction gs with
  | nil => intro WC WD h; exact h
  | cons g gs ih =>
    intro WC WD h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step t s ht WC WD g h)

lemma rd (x : Fin 9 → Bool) (l : List Bool) (k : ℕ) (hk : k < 9) :
    (List.ofFn x ++ l).getD k false = x ⟨k, hk⟩ := by
  interval_cases k <;> simp [List.getD_eq_getElem?_getD]

lemma rd2 (x : Fin 9 → Bool) (l : List Bool) (j : ℕ) :
    (List.ofFn x ++ l).getD (9 + j) false = l.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma rd9 (x : Fin 9 → Bool) (l : List Bool) :
    (List.ofFn x ++ l).getD 9 false = l.getD 0 false := rd2 x l 0

lemma rd10 (x : Fin 9 → Bool) (l : List Bool) :
    (List.ofFn x ++ l).getD 10 false = l.getD 1 false := rd2 x l 1

lemma rd11 (x : Fin 9 → Bool) (l : List Bool) :
    (List.ofFn x ++ l).getD 11 false = l.getD 2 false := rd2 x l 2

lemma init_rel (x : Fin 9 → Bool) (v a1 : Bool) (ext : List Bool) (t s : ℕ)
    (hs : ext.length = s) (ha : a1 = (x 0 || x 4))
    (ht : (List.ofFn x ++ ([false, a1] ++ ext)).getD t false = v) :
    Rel t s (List.ofFn x ++ [x 0 || x 4, v]) (List.ofFn x ++ ([false, a1] ++ ext)) := by
  refine ⟨by simp [hs]; omega, by simp, ?_⟩
  intro k
  unfold sig
  split_ifs with h1 h2 h3
  · rw [rd x _ k h1, rd x _ k h1]
  · subst h2
    rw [rd10, rd9, ha]
    rfl
  · subst h3
    rw [ht, rd10]
    rfl
  · rw [List.getD_eq_default _ _ (by simp [hs]; omega), List.getD_eq_default _ _ (by simp; omega)]

def gA : Gate := ⟨.or, [0, 4]⟩

lemma aval (x : Fin 9 → Bool) :
    gA.op.eval (gA.inputs.map fun i => (List.ofFn x ++ [false]).getD i false) = (x 0 || x 4) := by
  simp [gA, GateOp.eval, List.getD_eq_getElem?_getD]

lemma build (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (pre : List Gate)
    (hpre : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (t s : ℕ) (ht : t < 11 + s) (v : (Fin 9 → Bool) → Bool)
    (hinit : ∀ x : Fin 9 → Bool,
      Rel t s (List.ofFn x ++ [x 0 || x 4, v x]) (pre.foldl step (List.ofFn x ++ [false]))) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size + pre.length ∧
      ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x ++ [x 0 || x 4, v x]) := by
  refine ⟨⟨pre ++ C.gates.map (mapGate t s), sig t s C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hpre g hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have := hf g0 hg0
      exact ⟨this.1, by simpa [mapGate] using this.2⟩
  · simp [Circuit.size]
    omega
  · intro x
    have h := rel_fold t s ht C.gates _ _ (hinit x)
    change ((pre ++ C.gates.map (mapGate t s)).foldl step (List.ofFn x ++ [false])).getD
      (sig t s C.output) false = (C.gates.foldl step (List.ofFn x ++ [x 0 || x 4, v x])).getD
        C.output false
    rw [List.foldl_append]
    exact h.2.2 C.output

lemma legalA : ∀ g ∈ [gA], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  exact ⟨by simp [gA], by simp [gA]⟩

lemma preA (x : Fin 9 → Bool) :
    [gA].foldl step (List.ofFn x ++ [false]) = List.ofFn x ++ ([false, (x 0 || x 4)] ++ []) := by
  simp only [List.foldl_cons, List.foldl_nil, step, aval]
  simp

lemma orval (x : Fin 9 → Bool) (l : List Bool) (a b : Fin 9) :
    GateOp.or.eval ([a.val, b.val].map fun i => (List.ofFn x ++ l).getD i false) = (x a || x b) := by
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [rd x l a.val a.isLt, rd x l b.val b.isLt]

def gB (a b : Fin 9) : Gate := ⟨.or, [a.val, b.val]⟩

lemma preAB (x : Fin 9 → Bool) (a b : Fin 9) :
    [gA, gB a b].foldl step (List.ofFn x ++ [false]) =
      List.ofFn x ++ ([false, (x 0 || x 4)] ++ [x a || x b]) := by
  have h1 : step (List.ofFn x ++ [false]) gA = List.ofFn x ++ [false, (x 0 || x 4)] := by
    simp only [step, aval]
    simp
  have h2 : step (List.ofFn x ++ [false, (x 0 || x 4)]) (gB a b) =
      List.ofFn x ++ ([false, (x 0 || x 4)] ++ [x a || x b]) := by
    have := orval x [false, (x 0 || x 4)] a b
    simp only [step, gB, this]
    simp
  simp only [List.foldl_cons, List.foldl_nil, h1, h2]

lemma main (C : Circuit) (X : Finset (Fin 9)) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hX : X.card ≤ 2) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      (D.size ≤ C.size + if X.card ≤ 1 ∨ X = {0, 4} then 1 else 2) ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) =
        C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ j ∈ X, x j = true)]) := by
  by_cases h04 : X = {0, 4}
  · subst h04
    obtain ⟨D, h1, h2, h3⟩ := build C hf [gA] legalA 10 0 (by omega)
      (fun x => decide (∃ j ∈ ({0, 4} : Finset (Fin 9)), x j = true)) (by
        intro x
        rw [preA]
        apply init_rel x _ _ [] 10 0 rfl rfl
        rw [rd10]
        simp)
    exact ⟨D, h1, by simpa using h2, h3⟩
  have hc : X.card = 0 ∨ X.card = 1 ∨ X.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have hX0 : X = ∅ := Finset.card_eq_zero.mp hc
    subst hX0
    obtain ⟨D, h1, h2, h3⟩ := build C hf [gA] legalA 9 0 (by omega)
      (fun x => decide (∃ j ∈ (∅ : Finset (Fin 9)), x j = true)) (by
        intro x
        rw [preA]
        apply init_rel x _ _ [] 9 0 rfl rfl
        rw [rd9]
        simp)
    exact ⟨D, h1, by simpa using h2, h3⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    obtain ⟨D, h1, h2, h3⟩ := build C hf [gA] legalA a.val 0 (by omega)
      (fun x => decide (∃ j ∈ ({a} : Finset (Fin 9)), x j = true)) (by
        intro x
        rw [preA]
        apply init_rel x _ _ [] a.val 0 rfl rfl
        rw [rd x _ a.val a.isLt]
        simp)
    exact ⟨D, h1, by simpa using h2, h3⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    have legalAB : ∀ g ∈ [gA, gB a b], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨by simp [gA], by simp [gA]⟩
      · exact ⟨by simp [gB], by simp [gB]⟩
    obtain ⟨D, h1, h2, h3⟩ := build C hf [gA, gB a b] legalAB 11 1 (by omega)
      (fun x => decide (∃ j ∈ ({a, b} : Finset (Fin 9)), x j = true)) (by
        intro x
        rw [preAB]
        apply init_rel x _ _ [x a || x b] 11 1 rfl rfl
        rw [rd11]
        simp)
    refine ⟨D, h1, ?_, h3⟩
    have hcard : ¬ (({a, b} : Finset (Fin 9)).card ≤ 1) := by omega
    rw [if_neg (by tauto)]
    simpa using h2

end PEqualNP.Outside.L_meta_3630

theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) :=
  fun C X hf hX => PEqualNP.Outside.L_meta_3630.main C X hf hX
