import Thermal.MinimalSearch
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

theorem searchProgram_connected (a : RuleCode) (n : ℕ) (P : Finset Lattice)
    (h : searchProgram (a,n)=some P) : ConnectedWitness (decodeRule a) P := by
  unfold searchProgram at h
  split_ifs at h with hm
  · have he : (candidateList n).toFinset=P := (candidateList_set n).trans (Option.some.inj h)
    obtain ⟨hne,hpos,hmin⟩ := (minimalPositive_iff a _ (candidateList_nodup n)).mp hm
    rw [←he]
    refine ⟨hne,hpos,minimal_positive_connected _ _ hne hpos ?_⟩
    intro S hS hSne hSpos
    apply Nat.le_of_not_lt
    intro hc
    exact hmin S hS hSne hc hSpos

theorem searchProgram_complete (a : RuleCode) (hn : ¬(decodeRule a).Onto) :
    ∃ n P,searchProgram (a,n)=some P := by
  obtain ⟨T,hT⟩ := connected_witness (decodeRule a) hn
  let sizes : ℕ → Prop := fun k => ∃ P : Finset Lattice,
    P.card=k ∧ P.Nonempty ∧ 0<c (decodeRule a) P
  have hex : ∃ k,sizes k := ⟨T.card,T,rfl,hT.1,hT.2.1⟩
  obtain ⟨P,hcard,hne,hpos⟩ := Nat.find_spec hex
  have hmin (S : Finset Lattice) (hSne : S.Nonempty) (hSpos : 0<c (decodeRule a) S) :
      P.card≤S.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨S,rfl,hSne,hSpos⟩
  obtain ⟨n,he⟩ := candidateList_complete P
  have hm : MinimalPositive (a,candidateList n) := by
    apply (minimalPositive_iff a _ (candidateList_nodup n)).mpr
    rw [he]
    refine ⟨hne,hpos,?_⟩
    intro S hS hSne hc hSpos
    have := hmin S hSne hSpos
    omega
  refine ⟨n,P,?_⟩
  simp only [searchProgram,hm,ite_true]
  rw [←candidateList_set,he]

/-- Uniform total exhaustive search, with the original statement unchanged. -/
theorem witness_search : ∃ search : RuleCode × ℕ → Option (Finset Lattice),
  Computable search ∧
  (∀ code n P,search (code,n)=some P → P.Nonempty ∧ 0<c (decodeRule code) P) ∧
  (∀ code,¬(decodeRule code).Onto → ∃ n P,search (code,n)=some P) := by
  exact ⟨Algorithm.searchProgram,Algorithm.prim_searchProgram.to_comp,
    fun a n P h => ⟨(searchProgram_connected a n P h).1,
      (searchProgram_connected a n P h).2.1⟩,searchProgram_complete⟩

/-- Exact detection relative to the explicitly named published balance theorem. -/
theorem searchProgram_exact (H : PublishedCA.KariTaati_Corollary21) (a : RuleCode) :
    (∃ n P,searchProgram (a,n)=some P) ↔ ¬(decodeRule a).Onto := by
  constructor
  · rintro ⟨n,P,h⟩ ho
    have hp := searchProgram_connected a n P h
    have hz := (coefficient_detection H (decodeRule a)).mpr ho P hp.1
    linarith [hp.2.1]
  · exact searchProgram_complete a

end
end Thermal

