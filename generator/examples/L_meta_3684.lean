import Mathlib
import PEqualNP.Defs

-- A line whose pair input is accepted while the all-points input is rejected forces a
-- gate that reads that line's input wire directly, is true on the pair input and false
-- on the all-false input. A gate reads at most two wires, so each gate serves at most
-- two lines.
namespace PEqualNP.Outside.L_meta_3684
open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

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

lemma W_input (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, getD_snoc, W_length, if_pos (by omega)]
    exact ih

lemma op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (fX fY : Nat → Bool)
    (hx : g.op.eval (g.inputs.map fX) = true) (hy : g.op.eval (g.inputs.map fY) = false) :
    ∃ i ∈ g.inputs, fX i = true ∧ fY i = false := by
  rcases hg with h | h
  · rw [h] at hx hy
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false, Function.comp_apply,
      id] at hx hy
    obtain ⟨i, hi, hfy⟩ := hy
    exact ⟨i, hi, hx i hi, by simpa using hfy⟩
  · rw [h] at hx hy
    simp only [GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false, Function.comp_apply,
      id] at hx hy
    obtain ⟨i, hi, hfx⟩ := hx
    exact ⟨i, hi, hfx, by simpa using hy i hi⟩

lemma W_mono (gs : List Gate) (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (Z Y : List Bool) (hlen : Z.length = Y.length)
    (h : ∀ i, Z.getD i false = true → Y.getD i false = true) :
    ∀ i, (W gs Z).getD i false = true → (W gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => mono g' (List.mem_append_left _ hg'))
    have hg := mono g (by simp)
    intro i hi
    rw [W_snoc, getD_snoc, W_length] at hi ⊢
    by_cases h1 : i < Z.length + gs.length
    · rw [if_pos h1] at hi
      rw [if_pos (by omega)]
      exact ih' i hi
    · rw [if_neg h1] at hi
      rw [if_neg (by omega)]
      by_cases h2 : i = Z.length + gs.length
      · rw [if_pos h2] at hi
        rw [if_pos (by omega)]
        by_contra hne
        have hy : g.op.eval (g.inputs.map fun i => (W gs Y).getD i false) = false := by
          simpa using hne
        obtain ⟨i', _, hzi, hyi⟩ := op_mono g hg _ _ hi hy
        rw [ih' i' hzi] at hyi
        exact absurd hyi (by simp)
      · rw [if_neg h2] at hi
        exact absurd hi (by simp)

lemma core (gs : List Gate) (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X Y : List Bool) (hlen : X.length = Y.length) (a : Nat)
    (hXY : ∀ i, X.getD i false = true → Y.getD i false = false → i = a) :
    ∀ i, X.length ≤ i → (W gs X).getD i false = true → (W gs Y).getD i false = false →
      ∃ j, ∃ hj : j < gs.length, a ∈ (gs[j]).inputs ∧
        (W gs X).getD (X.length + j) false = true ∧
        (W gs Y).getD (X.length + j) false = false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi hx hy
    rw [show W [] X = X from rfl, List.getD_eq_default _ _ hi] at hx
    exact absurd hx (by simp)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => mono g' (List.mem_append_left _ hg'))
    have hg := mono g (by simp)
    intro i hi hx hy
    rw [W_snoc, getD_snoc, W_length] at hx hy
    have lift : (∃ j, ∃ hj : j < gs.length, a ∈ (gs[j]).inputs ∧
        (W gs X).getD (X.length + j) false = true ∧
        (W gs Y).getD (X.length + j) false = false) →
        ∃ j, ∃ hj : j < (gs ++ [g]).length, a ∈ ((gs ++ [g])[j]).inputs ∧
        (W (gs ++ [g]) X).getD (X.length + j) false = true ∧
        (W (gs ++ [g]) Y).getD (X.length + j) false = false := by
      rintro ⟨j, hj, ha, h1, h2⟩
      refine ⟨j, by simp; omega, ?_, ?_, ?_⟩
      · rw [List.getElem_append_left hj]; exact ha
      · rw [W_snoc, getD_snoc, W_length, if_pos (by omega)]; exact h1
      · rw [W_snoc, getD_snoc, W_length, if_pos (by omega)]; exact h2
    by_cases h1 : i < X.length + gs.length
    · rw [if_pos h1] at hx
      rw [if_pos (by omega)] at hy
      exact lift (ih' i hi hx hy)
    · rw [if_neg h1] at hx
      rw [if_neg (by omega)] at hy
      by_cases h2 : i = X.length + gs.length
      · rw [if_pos h2] at hx
        rw [if_pos (by omega)] at hy
        obtain ⟨i', hi', hxi, hyi⟩ := op_mono g hg _ _ hx hy
        by_cases h3 : i' < X.length
        · rw [W_input gs X i' h3] at hxi
          rw [W_input gs Y i' (by omega)] at hyi
          have hia := hXY i' hxi hyi
          subst hia
          refine ⟨gs.length, by simp, ?_, ?_, ?_⟩
          · simpa using hi'
          · rw [W_snoc, getD_snoc, W_length, if_neg (by omega), if_pos rfl]; exact hx
          · rw [W_snoc, getD_snoc, W_length, if_neg (by omega), if_pos (by omega)]; exact hy
        · exact lift (ih' i' (by omega) hxi hyi)
      · rw [if_neg h2] at hx
        exact absurd hx (by simp)

lemma ofFn_getD {m : Nat} (f : Fin m → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simpa using h

lemma diff_input (n : Nat) (p l : Fin n) (i : Nat)
    (hx : (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))).getD i false = true)
    (hy : (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)).getD i false = false) :
    i = n + l.val := by
  rw [ofFn_getD] at hx hy
  by_cases h : i < n + n
  · rw [dif_pos h] at hx hy
    by_cases hin : i < n
    · exfalso
      have e : (⟨i, h⟩ : Fin (n + n)) = Fin.castAdd n ⟨i, hin⟩ := rfl
      rw [e, Fin.addCases_left] at hy
      exact absurd hy (by simp)
    · simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hx
      rcases hx with hx | hx
      · have e := congrArg Fin.val hx
        simp at e
        omega
      · have e := congrArg Fin.val hx
        simp at e
        omega
  · rw [dif_neg h] at hx
    exact absurd hx (by simp)

lemma zero_getD (m i : Nat) : (List.replicate m false).getD i false = false := by
  by_cases h : i < m
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simpa using h

theorem main (n : ℕ) (C C3 : Circuit) (hout : C.output = C3.output)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : C.eval (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)) = false)
    (x8 : Fin n → Finset (Fin n))
    (hB : ∀ (x9 x10 : Fin n), x10 ∈ x8 x9 → C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n x10) (Fin.natAdd n x9))) = true ∧ C3.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n x10) (Fin.natAdd n x9))) = false) :
    Fintype.card { x10 : Fin n // (x8 x10).Nonempty } ≤
      2 * Fintype.card { x10 : Fin C.size // ((C.wires (List.replicate (n + n) false)).getD (n + n + ↑x10) false = false ∧ ∃ (x11 : Fin n), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (n + n) C (↑x10) (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n x12) (Fin.natAdd n x11)) = true) } := by
  have mono' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hmono g hg).1
    simpa using this
  have key : ∀ l : Fin n, (x8 l).Nonempty → ∃ j : Fin C.size,
      ((C.wires (List.replicate (n + n) false)).getD (n + n + ↑j) false = false ∧ ∃ (x11 : Fin n), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (n + n) C (↑j) (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n x12) (Fin.natAdd n x11)) = true) ∧ (n + l.val) ∈ (C.gates[j.val]'j.isLt).inputs := by
    rintro l ⟨p, hp⟩
    obtain ⟨hC, hC3⟩ := hB l p hp
    have lX : (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))).length = n + n := by simp
    have lY : (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)).length = n + n := by simp
    have hox : (W C.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l)))).getD C.output false = true := hC
    have hoy : (W C.gates (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool))).getD C.output false = false := hA
    have hge : (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))).length ≤ C.output := by
      by_contra hlt
      push Not at hlt
      have h3 : (W C3.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l)))).getD C3.output false = false := hC3
      rw [← hout, W_input _ _ _ hlt] at h3
      rw [W_input _ _ _ hlt, h3] at hox
      exact absurd hox (by simp)
    obtain ⟨j, hj, ha, h1, h2⟩ := core C.gates mono' (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))) (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)) (by rw [lX, lY]) (n + l.val)
      (fun i hx hy => diff_input n p l i hx hy) C.output hge hox hoy
    rw [lX] at h1 h2
    refine ⟨⟨j, hj⟩, ⟨?_, l, p, hp, h1⟩, ha⟩
    by_contra hne
    have hz : (W C.gates (List.replicate (n + n) false)).getD (n + n + j) false = true := by
      have h0 : (C.wires (List.replicate (n + n) false)).getD (n + n + j) false = true := by
        simpa using hne
      exact h0
    have hzero : ∀ i, (List.replicate (n + n) false).getD i false = true →
        (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)).getD i false = true := by
      intro i hi
      rw [zero_getD] at hi
      exact absurd hi (by simp)
    have hy := W_mono C.gates mono' (List.replicate (n + n) false) (List.ofFn fun x6 : Fin (n + n) => (Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) x6 : Bool)) (by rw [lY]; simp)
      hzero (n + n + j) hz
    rw [hy] at h2
    exact absurd h2 (by simp)
  choose φ hφ using key
  let f : { l : Fin n // (x8 l).Nonempty } → { x10 : Fin C.size // ((C.wires (List.replicate (n + n) false)).getD (n + n + ↑x10) false = false ∧ ∃ (x11 : Fin n), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (n + n) C (↑x10) (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n x12) (Fin.natAdd n x11)) = true) } :=
    fun a => ⟨φ a.1 a.2, (hφ a.1 a.2).1⟩
  have hfib : ∀ b ∈ (Finset.univ.image f), (Finset.univ.filter fun a => f a = b).card ≤ 2 := by
    intro b _
    have hsub : (Finset.univ.filter fun a => f a = b).card ≤
        ((C.gates[b.1.val]'b.1.isLt).inputs.toFinset).card := by
      apply Finset.card_le_card_of_injOn (fun a => n + a.1.val)
      · intro a ha
        have hab : f a = b := (Finset.mem_filter.mp ha).2
        have hin := (hφ a.1 a.2).2
        simp only [Finset.mem_coe, List.mem_toFinset]
        rw [← hab]
        exact hin
      · intro a _ a' _ h
        apply Subtype.ext
        apply Fin.ext
        simpa using h
    exact hsub.trans ((List.toFinset_card_le _).trans (hmono _ (List.getElem_mem _)).2)
  refine le_trans (le_of_eq Finset.card_univ.symm) ?_
  refine le_trans (Finset.card_le_mul_card_image (f := f) Finset.univ 2 hfib) ?_
  exact Nat.mul_le_mul_left 2 (Finset.card_le_univ _)

end PEqualNP.Outside.L_meta_3684

theorem PEqualNP.Outside.L_meta_3684 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x2.output = x3.output →     PEqualNP.MetaComplexity.Monotone2 x2 →       x2.eval (List.ofFn fun (x6 : Fin (x1 + x1)) => Fin.addCases (fun (x7 : Fin x1) => Bool.true) (fun (x7 : Fin x1) => Bool.false) x6) = Bool.false →         have x7 : Fin x1 → Fin x1 → Fin (x1 + x1) → Bool := fun (x7 x8 : Fin x1) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x7) (Fin.natAdd x1 x8);         ∀ (x8 : Fin x1 → Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x10 ∈ x8 x9 → x2.eval (List.ofFn (x7 x10 x9)) = Bool.true ∧ x3.eval (List.ofFn (x7 x10 x9)) = Bool.false) → Fintype.card { x10 : Fin x1 // (x8 x10).Nonempty } ≤ (2 : ℕ) * Fintype.card { x10 : Fin x2.size // (x2.wires (List.replicate (x1 + x1) Bool.false)).getD (x1 + x1 + ↑x10) Bool.false = Bool.false ∧ ∃ (x11 : Fin x1), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (x1 + x1) x2 (↑x10) (x7 x12 x11) = Bool.true } := by
  intro n C C3 hout hmono hA x7 x8 hB
  exact PEqualNP.Outside.L_meta_3684.main n C C3 hout hmono hA x8 hB
