import Thermal.RuleCoding
import Thermal.FiniteReduction
import Thermal.CoefficientAlgorithm
import Mathlib.Data.List.NodupEquivFin
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

def listIndexEquiv (l : List Lattice) (hl : l.Nodup) : l.toFinset ≃ Fin l.length where
  toFun i := ⟨l.idxOf i.val,List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp i.property)⟩
  invFun j := ⟨l.get j,List.mem_toFinset.mpr (List.get_mem _ _)⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv j := by apply Fin.ext; simp [hl,List.get_idxOf]

def patternEquiv (q : ℕ) (l : List Lattice) (hl : l.Nodup) :
    Fin (q^l.length) ≃ (l.toFinset → Fin q) :=
  finFunctionFinEquiv.symm.trans
    (Equiv.arrowCongr (listIndexEquiv l hl).symm (Equiv.refl (Fin q)))

theorem patternEquiv_val (q : ℕ) (hq : 0<q) (l : List Lattice) (hl : l.Nodup)
    (n : Fin (q^l.length)) (i : l.toFinset) :
    (patternEquiv q l hl n i).val = assignmentDigit ((q,l),(n.val,i.val)) := by
  rfl

theorem inputList_set (a : RuleCode) (l : List Lattice) :
    (inputList (a,l)).toFinset = inputSupport (decodeRule a) l.toFinset := by
  ext x
  simp only [inputList,inputSupport,neighborhood,decodeRule,List.mem_toFinset,
    List.mem_dedup,List.mem_flatMap,List.mem_map,Finset.mem_biUnion,Finset.mem_image]

theorem evalAt_correct (a : RuleCode) (l : List Lattice) (n : ℕ) (i : Lattice) :
    evalAt (a,(l,(n,i))) = ((decodeRule a).global
      (fun j => ⟨assignmentDigit ((qValue a,l),(n,j)),Nat.mod_lt _ (by change 0<a.1+2; omega)⟩) i).val := by
  unfold evalAt evalLocal
  simp only [List.foldl_map]
  have hf := @List.foldl_attach Lattice ℕ (0::a.2.1)
    (fun acc j => acc*qValue a + assignmentDigit ((qValue a,l),(n,i+j))) 0
  exact congrArg (fun k => ((a.2.2[k]?).getD 0) % qValue a) hf.symm

/-- Push integer tests through the unnormalized finite preimage count. -/
theorem outputCount_expect (F : CA) (T : Finset Lattice) (f : (T → Fin F.q) → ℤ) :
    (∑ a,outputCount F T a*f a) = ∑ x,f (blockMap F T x) := by
  unfold outputCount
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

theorem collisionNumerator_input (F : CA) (T : Finset Lattice) :
    collisionNumerator F T = ∑ x : inputSupport F T → Fin F.q,
      ∑ y : inputSupport F T → Fin F.q,
        ∏ i : T,integerKernel F.q (blockMap F T x i) (blockMap F T y i) := by
  unfold collisionNumerator
  simp_rw [mul_assoc,← mul_sum]
  rw [outputCount_expect]
  simp_rw [outputCount_expect]

end
end Thermal

