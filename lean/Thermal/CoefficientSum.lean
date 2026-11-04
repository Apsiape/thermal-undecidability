import Thermal.CoefficientCorrect
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

def inputAssignment (a : RuleCode) (l : List Lattice) (n : ℕ) :
    inputSupport (decodeRule a) l.toFinset → Fin (decodeRule a).q :=
  fun i => ⟨assignmentDigit ((qValue a,inputList (a,l)),(n,i.val)),
    Nat.mod_lt _ (by change 0<a.1+2; omega)⟩

def supportListEquiv (a : RuleCode) (l : List Lattice) :
    (inputList (a,l)).toFinset ≃ inputSupport (decodeRule a) l.toFinset where
  toFun i := ⟨i.val,by rw [←inputList_set]; exact i.property⟩
  invFun i := ⟨i.val,by rw [inputList_set]; exact i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def inputAssignmentEquiv (a : RuleCode) (l : List Lattice) :
    Fin (assignmentCount (a,l)) ≃ (inputSupport (decodeRule a) l.toFinset → Fin (decodeRule a).q) :=
  (patternEquiv (qValue a) (inputList (a,l)) (List.nodup_dedup _)).trans
    (Equiv.arrowCongr (supportListEquiv a l) (Equiv.refl _))

theorem inputAssignmentEquiv_apply (a : RuleCode) (l : List Lattice)
    (n : Fin (assignmentCount (a,l))) :
    inputAssignmentEquiv a l n = inputAssignment a l n.val := by
  rfl

theorem evalAt_inputAssignment (a : RuleCode) (l : List Lattice) (n : ℕ) (i : l.toFinset) :
    evalAt (a,(inputList (a,l),(n,i.val))) =
      (blockMap (decodeRule a) l.toFinset (inputAssignment a l n) i).val := by
  rw [evalAt_correct]
  rfl

theorem pairTerm_correct (a : RuleCode) (l : List Lattice) (hl : l.Nodup) (n m : ℕ) :
    pairTerm ((a,l),(n,m)) =
      ∏ i : l.toFinset,integerKernel (decodeRule a).q
        (blockMap (decodeRule a) l.toFinset (inputAssignment a l n) i)
        (blockMap (decodeRule a) l.toFinset (inputAssignment a l m) i) := by
  unfold pairTerm
  rw [←List.prod_eq_foldr,←List.prod_toFinset _ hl]
  rw [←Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro i _
  rw [evalAt_inputAssignment,evalAt_inputAssignment]
  simp only [intKernel,integerKernel,Fin.val_inj]
  rfl

theorem foldr_range_sum (N : ℕ) (f : ℕ → ℤ) :
    ((List.range N).map f).foldr (·+·) 0 = ∑ n∈Finset.range N,f n := by
  rw [←List.sum_eq_foldr]
  have he : (List.range N).toFinset = Finset.range N := by ext i; simp
  rw [←he]
  exact (List.sum_toFinset f (List.nodup_range (n := N))).symm

theorem sum_inputAssignment (a : RuleCode) (l : List Lattice)
    (f : (inputSupport (decodeRule a) l.toFinset → Fin (decodeRule a).q) → ℤ) :
    (∑ n∈Finset.range (assignmentCount (a,l)),f (inputAssignment a l n)) = ∑ x,f x := by
  rw [←Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (inputAssignmentEquiv a l) _ _ (fun n => rfl)

theorem finiteNumerator_correct (a : RuleCode) (l : List Lattice) (hl : l.Nodup) :
    finiteNumerator (a,l) = collisionNumerator (decodeRule a) l.toFinset := by
  unfold finiteNumerator
  simp_rw [foldr_range_sum,pairTerm_correct a l hl]
  rw [collisionNumerator_input]
  trans ∑ x : inputSupport (decodeRule a) l.toFinset → Fin (decodeRule a).q,
    ∑ m∈Finset.range (assignmentCount (a,l)),
      ∏ i : l.toFinset,integerKernel (decodeRule a).q
        (blockMap (decodeRule a) l.toFinset x i)
        (blockMap (decodeRule a) l.toFinset (inputAssignment a l m) i)
  · exact sum_inputAssignment a l (fun x =>
      ∑ m∈Finset.range (assignmentCount (a,l)),
        ∏ i : l.toFinset,integerKernel (decodeRule a).q
          (blockMap (decodeRule a) l.toFinset x i)
          (blockMap (decodeRule a) l.toFinset (inputAssignment a l m) i))
  · apply Finset.sum_congr rfl
    intro x _
    exact sum_inputAssignment a l (fun y =>
      ∏ i : l.toFinset,integerKernel (decodeRule a).q
        (blockMap (decodeRule a) l.toFinset x i)
        (blockMap (decodeRule a) l.toFinset y i))

theorem finiteNumerator_pos_iff (a : RuleCode) (l : List Lattice) (hl : l.Nodup) :
    0<finiteNumerator (a,l) ↔ 0<c (decodeRule a) l.toFinset := by
  rw [finiteNumerator_correct a l hl,coefficient_integer_numerator]
  have hd : (0 : ℚ)<(decodeRule a).q^(2*(inputSupport (decodeRule a) l.toFinset).card) := by
    have hq : (0 : ℚ)<(decodeRule a).q := by
      exact_mod_cast (show 0<(decodeRule a).q from by have := (decodeRule a).two_le; omega)
    positivity
  rw [div_pos_iff_of_pos_right hd]
  exact_mod_cast (Iff.rfl : 0<collisionNumerator (decodeRule a) l.toFinset ↔
    0<collisionNumerator (decodeRule a) l.toFinset)

end
end Thermal


