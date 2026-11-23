import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627

open PEqualNP.CircuitLowerBounds

lemma fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]
      simp
    · simp [hl]

lemma getD_app_ge (W l : List Bool) (k : ℕ) :
    (W ++ l).getD (W.length + k) false = l.getD k false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma getD_app_len (W l : List Bool) :
    (W ++ l).getD W.length false = l.getD 0 false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma getD_app_lt (W l : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ l).getD i false = W.getD i false :=
  List.getD_append _ _ _ _ h

lemma upd {n : ℕ} (x : Fin n → Bool) (u : Fin n) (b : Bool) (h : x u = b) :
    Function.update x u b = x := by
  rw [← h]
  exact Function.update_eq_self u x

lemma getD_len_add (W : List Bool) (k : ℕ) : W.getD (W.length + k) false = false :=
  List.getD_eq_default _ _ (by omega)

lemma final {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (u v : Fin n) (A B : Bool)
    (hA : A = F (Function.update x u (x v))) (hB : B = F (Function.update x u (!(x v)))) :
    (A && !((x u || x v) && !(x u && x v)) || B && ((x u || x v) && !(x u && x v))) = F x := by
  by_cases h : x u = x v
  · rw [upd x u (x v) h] at hA
    rw [hA, h]
    cases h3 : x v <;> simp
  · have h' : x u = !(x v) := by
      cases h1 : x u <;> cases h2 : x v <;> simp_all
    rw [upd x u _ h'] at hB
    rw [hB, h']
    cases h3 : x v <;> simp

lemma pick {n : ℕ} (C : Circuit) (G : (Fin n → Bool) → Bool) (o : ℕ)
    (ho : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o false = G x) :
    ∃ p : ℕ, (p < n + C.gates.length ∨ p = n + C.gates.length + 8) ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = G x := by
  by_cases h : o < n + C.gates.length
  · exact ⟨o, Or.inl h, ho⟩
  · refine ⟨n + C.gates.length + 8, Or.inr rfl, fun x => ?_⟩
    obtain ⟨t, ht, hl⟩ := fold_prefix C.gates (List.ofFn x)
    have hw : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
    have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      rw [hw]
      simp [hl]
    have e1 : (C.wires (List.ofFn x)).getD o false = false :=
      List.getD_eq_default _ _ (by omega)
    have e2 : (C.wires (List.ofFn x)).getD (n + C.gates.length + 8) false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [e2, ← ho x, e1]

lemma main : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  intro n s F u v hC
  obtain ⟨C, hfan, hsize, o1, o2, ho⟩ := hC
  obtain ⟨p1, hp1, hA⟩ :=
    pick C (fun x => F (Function.update x u (x v))) o1 (fun x => (ho x).1)
  obtain ⟨p2, hp2, hB⟩ :=
    pick C (fun x => F (Function.update x u (!(x v)))) o2 (fun x => (ho x).2)
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [u, v]⟩, ⟨GateOp.and, [u, v]⟩,
      ⟨GateOp.not, [n + C.gates.length + 1]⟩,
      ⟨GateOp.and, [n + C.gates.length, n + C.gates.length + 2]⟩,
      ⟨GateOp.not, [n + C.gates.length + 3]⟩,
      ⟨GateOp.and, [p1, n + C.gates.length + 4]⟩,
      ⟨GateOp.and, [p2, n + C.gates.length + 3]⟩,
      ⟨GateOp.or, [n + C.gates.length + 5, n + C.gates.length + 6]⟩],
      n + C.gates.length + 7⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hfan g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
    unfold Circuit.size at hsize
    omega
  · intro x
    obtain ⟨t, ht, hl⟩ := fold_prefix C.gates (List.ofFn x)
    have hw : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
    have hA' := hA x
    have hB' := hB x
    rw [hw] at hA' hB'
    simp only [Circuit.eval, Circuit.wires, List.foldl_append]
    rw [ht]
    have hlen : n + C.gates.length = (List.ofFn x ++ t).length := by simp [hl]
    have hu : (u : ℕ) < (List.ofFn x ++ t).length := by simp; omega
    have hv : (v : ℕ) < (List.ofFn x ++ t).length := by simp; omega
    have hxu : (List.ofFn x ++ t).getD u false = x u := by
      rw [List.getD_append _ _ _ _ (by simp)]
      simp
    have hxv : (List.ofFn x ++ t).getD v false = x v := by
      rw [List.getD_append _ _ _ _ (by simp)]
      simp
    rw [hlen] at hp1 hp2
    rw [hlen]
    generalize List.ofFn x ++ t = W at hA' hB' hu hv hxu hxv hp1 hp2 ⊢
    clear hA hB ho hw ht hlen hl hfan hsize
    rcases hp1 with hp1 | rfl <;> rcases hp2 with hp2 | rfl <;>
    (try rw [getD_len_add] at hA') <;> (try rw [getD_len_add] at hB') <;>
    simp (disch := assumption) only [List.foldl_cons, List.foldl_nil, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append, getD_app_ge,
      getD_app_len, getD_app_lt, hxu, hxv, List.getD_cons_zero, List.getD_cons_succ,
      List.getD_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      List.headD_cons, id_eq, Bool.and_true, Bool.or_false] <;>
    exact final F x u v _ _ hA' hB'

end PEqualNP.Outside.L_meta_627

theorem PEqualNP.Outside.L_meta_627 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  exact PEqualNP.Outside.L_meta_627.main
