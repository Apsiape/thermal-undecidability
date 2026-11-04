import Thermal.CoefficientSum
import Thermal.SearchAlgorithm
import Thermal.ConnectedWitness
import Thermal.BalanceSource
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

theorem list_map_identity_nat (l : List ℕ) : l.map (fun m => m) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,ih]

theorem raiseBase_spec (l : List ℕ) (n : ℕ) :
    Denumerable.raise' l n = (raiseBase l).map (fun m => m+n) := by
  induction l generalizing n with
  | nil => rfl
  | cons m l ih =>
    simp only [Denumerable.raise',raiseBase,List.foldr_cons,List.map_cons,shiftList]
    rw [ih]
    simp [raiseBase,shiftList,List.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem candidateList_set (n : ℕ) :
    (candidateList n).toFinset = Denumerable.ofNat (Finset Lattice) n := by
  have hh := raiseBase_spec (Denumerable.ofNat (List ℕ) n) 0
  simp only [Nat.add_zero,list_map_identity_nat] at hh
  unfold candidateList
  rw [←hh]
  change _ = Finset.map (Denumerable.eqv Lattice).symm.toEmbedding
    (Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0)
  ext i
  simp [Denumerable.raise'Finset,Denumerable.eqv]
  change (∃ a∈Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0,
    Denumerable.ofNat Point a=i) ↔
      Denumerable.eqv Point i∈Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : Denumerable.eqv Point i=a := by
      rw [←he]
      exact (Denumerable.eqv Point).apply_symm_apply a
    rw [hai]; exact ha
  · intro hi
    exact ⟨Denumerable.eqv Point i,hi,(Denumerable.eqv Point).symm_apply_apply i⟩

theorem candidateList_nodup (n : ℕ) : (candidateList n).Nodup := by
  unfold candidateList
  apply List.Nodup.map (Denumerable.eqv Lattice).symm.injective
  have hh := raiseBase_spec (Denumerable.ofNat (List ℕ) n) 0
  simp only [Nat.add_zero,list_map_identity_nat] at hh
  rw [←hh]
  exact (Denumerable.raise'_sorted _ _).nodup

theorem candidateList_complete (P : Finset Lattice) : ∃ n,(candidateList n).toFinset=P := by
  refine ⟨Denumerable.eqv (Finset Lattice) P,?_⟩
  rw [candidateList_set]
  exact (Denumerable.eqv (Finset Lattice)).symm_apply_apply P

theorem maskSubset_subset (l : List Lattice) (m : ℕ) :
    (maskSubset (l,m)).toFinset ⊆ l.toFinset := by
  intro i hi
  simpa only [maskSubset,List.mem_toFinset,List.mem_filter,decide_eq_true_eq] using
    (List.mem_filter.mp (List.mem_toFinset.mp hi)).1

theorem maskSubset_complete (l : List Lattice) (hl : l.Nodup)
    (S : Finset Lattice) (hS : S⊆l.toFinset) :
    ∃ m<2^l.length,(maskSubset (l,m)).toFinset=S := by
  let f : l.toFinset → Fin 2 := fun i => if i.val∈S then 1 else 0
  let n := (patternEquiv 2 l hl).symm f
  have hd (i : l.toFinset) : n.val/2^(l.idxOf i.val)%2 = (if i.val∈S then 1 else 0) := by
    change assignmentDigit ((2,l),(n.val,i.val)) = _
    rw [←patternEquiv_val 2 (by omega) l hl n i]
    simp only [n,Equiv.apply_symm_apply]
    dsimp [f]
    split_ifs <;> rfl
  refine ⟨n.val,n.isLt,?_⟩
  ext i
  simp only [maskSubset,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨hi,hbit⟩
    have he := hd ⟨i,List.mem_toFinset.mpr hi⟩
    by_contra hn
    simp [hn] at he
    omega
  · intro hi
    have hil := hS hi
    refine ⟨List.mem_toFinset.mp hil,?_⟩
    rw [hd ⟨i,hil⟩]
    simp [hi]

end
end Thermal



