import Mathlib
import PEqualNP.Defs

-- A finite check on an explicit circuit with fourteen inputs. The circuit is run once
-- on packed truth tables (one bit for each of the 16384 inputs), a general lemma shows
-- that bit m of each packed wire is the value of that wire on input m, and the packed
-- output is compared with the packed edge function.
namespace PEqualNP.Outside.L_meta_3751
open PEqualNP.CircuitLowerBounds

def tt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i =>
    if i = k then 2 ^ (2 ^ k) * (2 ^ (2 ^ k) - 1) + 0 else 2 ^ (2 ^ k) * tt k i + tt k i

lemma tt_lt : ∀ k i, tt k i < 2 ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro i; simp [tt]
  | succ k ih =>
    intro i
    have hw : (2 : Nat) ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [← pow_add]; congr 1; ring
    have hpos : 0 < (2 : Nat) ^ (2 ^ k) := by positivity
    unfold tt
    split_ifs with h
    · rw [hw, Nat.add_zero]
      exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hpos (by norm_num)) hpos
    · have ha := ih i
      rw [hw]
      nlinarith

lemma low_bits (k i m : Nat) (hi : i < k) (hm : 2 ^ k ≤ m) :
    (m - 2 ^ k).testBit i = m.testBit i := by
  have h1 : (m - 2 ^ k) % 2 ^ k = m % 2 ^ k := by
    conv_rhs => rw [← Nat.sub_add_cancel hm]
    rw [Nat.add_mod_right]
  have h2 := Nat.testBit_mod_two_pow (m - 2 ^ k) k i
  have h3 := Nat.testBit_mod_two_pow m k i
  rw [h1] at h2
  simp only [hi, decide_true, Bool.true_and] at h2 h3
  rw [← h2, h3]

lemma top_bit (k m : Nat) (hm : m < 2 ^ (k + 1)) : m.testBit k = decide (2 ^ k ≤ m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2 ^ k ≤ m
  · have : m / 2 ^ k = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using h
      · rw [pow_succ] at hm; omega
    simp [this, h]
  · have : m / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

lemma tt_bit : ∀ k i m, i < k → m < 2 ^ k → (tt k i).testBit m = m.testBit i := by
  intro k
  induction k with
  | zero => intro i m hi _; omega
  | succ k ih =>
    intro i m hi hm
    have hm2 : m < 2 ^ k + 2 ^ k := by rw [pow_succ] at hm; omega
    unfold tt
    split_ifs with h
    · subst h
      rw [Nat.testBit_two_pow_mul_add _ (by positivity), top_bit i m hm]
      split_ifs with h1
      · simp
        omega
      · rw [Nat.testBit_two_pow_sub_one]
        simp
        constructor <;> omega
    · have hik : i < k := by omega
      rw [Nat.testBit_two_pow_mul_add _ (tt_lt k i)]
      split_ifs with h1
      · exact ih i m hik h1
      · rw [ih i (m - 2 ^ k) hik (by omega)]
        exact low_bits k i m hik (by omega)

def tts : List Nat := (List.range 14).map (tt 14)

def full : Nat := 2 ^ 16384 - 1

lemma tts_ok (m : Nat) (hm : m < 16384) (i : Nat) (hi : i < 14) :
    (tts.getD i 0).testBit m = m.testBit i := by
  have h : tts.getD i 0 = tt 14 i := by
    unfold tts
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  rw [h]
  exact tt_bit 14 i m hi (by norm_num; exact hm)

def stepN (w : List Nat) (g : Gate) : List Nat :=
  w ++ [match g.op with
    | GateOp.and => (g.inputs.map fun i => w.getD i 0).foldl Nat.land full
    | GateOp.or => (g.inputs.map fun i => w.getD i 0).foldl Nat.lor 0
    | _ => 0]

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma full_bit (m : Nat) (hm : m < 16384) : full.testBit m = true := by
  unfold full
  rw [Nat.testBit_two_pow_sub_one]
  simpa using hm

lemma land_fold (m : Nat) (l : List Nat) : ∀ acc : Nat,
    (l.foldl Nat.land acc).testBit m = (acc.testBit m && l.all fun v => v.testBit m) := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [Nat.testBit_land, Bool.and_assoc]

lemma lor_fold (m : Nat) (l : List Nat) : ∀ acc : Nat,
    (l.foldl Nat.lor acc).testBit m = (acc.testBit m || l.any fun v => v.testBit m) := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [Nat.testBit_lor, Bool.or_assoc]

lemma getD_snocN (l : List Nat) (v : Nat) (i : Nat) :
    (l ++ [v]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then v else 0 := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma getD_snocB (l : List Bool) (v : Bool) (i : Nat) :
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

lemma link (m : Nat) (hm : m < 16384) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w : List Nat) (bw : List Bool), w.length = bw.length →
      (∀ i, (w.getD i 0).testBit m = bw.getD i false) →
      ∀ i, ((gs.foldl stepN w).getD i 0).testBit m = (gs.foldl stepB bw).getD i false := by
  induction gs with
  | nil => intro w bw _ h i; exact h i
  | cons g gs ih =>
    intro w bw hlen h i
    rw [List.foldl_cons, List.foldl_cons]
    refine ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [stepN, stepB, hlen]) ?_ i
    intro k
    have hmap : (g.inputs.map fun i => bw.getD i false) =
        (g.inputs.map fun i => w.getD i 0).map fun v => v.testBit m := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      exact (h j).symm
    unfold stepN stepB
    rw [getD_snocN, getD_snocB, hlen]
    by_cases h1 : k < bw.length
    · rw [if_pos h1, if_pos h1]; exact h k
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : k = bw.length
      · rw [if_pos h2, if_pos h2]
        rcases hop g (by simp) with ho | ho
        · rw [ho]
          simp only [GateOp.eval]
          rw [land_fold, full_bit m hm, hmap]
          simp [List.all_map]
        · rw [ho]
          simp only [GateOp.eval]
          rw [lor_fold, hmap]
          simp [List.any_map]
      · rw [if_neg h2, if_neg h2]; simp

def bitsOf (m : Nat) : Fin 14 → Bool := fun i => m.testBit i.val

lemma ofFn_getD {k : Nat} (f : Fin k → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < k then f ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simpa using h

lemma start_ok (m : Nat) (hm : m < 16384) (i : Nat) :
    (tts.getD i 0).testBit m = (List.ofFn (bitsOf m)).getD i false := by
  rw [ofFn_getD]
  split_ifs with h
  · exact tts_ok m hm i h
  · have h1 : tts.length ≤ i := by
      have : tts.length = 14 := by simp [tts]
      omega
    rw [List.getD_eq_default _ _ h1]
    simp

def packed (C : Circuit) : Nat := (C.gates.foldl stepN tts).getD C.output 0

lemma eval_packed (C : Circuit) (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (m : Nat) (hm : m < 16384) :
    PEqualNP.MetaComplexity.circuitFun 14 C (bitsOf m) = (packed C).testBit m := by
  have h := link m hm C.gates hop tts (List.ofFn (bitsOf m)) (by simp [tts])
    (start_ok m hm) C.output
  exact h.symm

def edgeN (L : List (Fin 14 × Fin 14)) : Nat :=
  L.foldl (fun acc e => Nat.lor acc (Nat.land (tts.getD e.1.val 0) (tts.getD e.2.val 0))) 0

lemma edge_fold (m : Nat) (hm : m < 16384) (L : List (Fin 14 × Fin 14)) : ∀ acc : Nat,
    (L.foldl (fun acc e => Nat.lor acc (Nat.land (tts.getD e.1.val 0) (tts.getD e.2.val 0)))
      acc).testBit m =
      (acc.testBit m || L.any fun e => bitsOf m e.1 && bitsOf m e.2) := by
  induction L with
  | nil => intro acc; simp
  | cons e L ih =>
    intro acc
    rw [List.foldl_cons, ih]
    have h1 := tts_ok m hm e.1.val e.1.isLt
    have h2 := tts_ok m hm e.2.val e.2.isLt
    have h3 : (Nat.lor acc (Nat.land (tts.getD e.1.val 0) (tts.getD e.2.val 0))).testBit m =
        (acc.testBit m || (bitsOf m e.1 && bitsOf m e.2)) := by
      show (acc ||| (tts.getD e.1.val 0 &&& tts.getD e.2.val 0)).testBit m = _
      rw [Nat.testBit_or, Nat.testBit_and, h1, h2]
      rfl
    rw [h3, List.any_cons, Bool.or_assoc]

lemma edge_packed (m : Nat) (hm : m < 16384) (L : List (Fin 14 × Fin 14)) :
    decide (∃ e ∈ L, bitsOf m e.1 = true ∧ bitsOf m e.2 = true) = (edgeN L).testBit m := by
  unfold edgeN
  rw [edge_fold m hm L 0]
  simp only [Nat.zero_testBit, Bool.false_or]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

lemma bits_surj (x : Fin 14 → Bool) : ∃ m, m < 16384 ∧ bitsOf m = x := by
  refine ⟨Nat.ofBits x, ?_, ?_⟩
  · have := Nat.ofBits_lt_two_pow x
    simpa using this
  · funext i
    unfold bitsOf
    rw [Nat.testBit_ofBits_lt _ _ i.2]

theorem main (C : Circuit) (L : List (Fin 14 × Fin 14))
    (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (heq : packed C = edgeN L) (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 C x =
      decide (∃ e ∈ L, x e.1 = true ∧ x e.2 = true) := by
  obtain ⟨m, hm, rfl⟩ := bits_surj x
  rw [eval_packed C hop m hm, edge_packed m hm L, heq]

end PEqualNP.Outside.L_meta_3751

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3751 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }], output := 56 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 43 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  have hao : PEqualNP.TopForm.IsAO2 14 C := by subst hC; decide +kernel
  refine ⟨hao, by subst hC; decide +kernel, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_3751.main C _ hao.1 (by subst hC; decide +kernel)
  · subst hC; decide +kernel
