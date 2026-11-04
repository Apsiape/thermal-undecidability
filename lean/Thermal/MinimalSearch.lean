import Thermal.SearchCorrect
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

theorem maskSubset_nodup (l : List Lattice) (hl : l.Nodup) (m : ℕ) :
    (maskSubset (l,m)).Nodup := hl.filter _

theorem minimalPositive_iff (a : RuleCode) (l : List Lattice) (hl : l.Nodup) :
    MinimalPositive (a,l) ↔ l.toFinset.Nonempty ∧ 0<c (decodeRule a) l.toFinset ∧
      ∀ S : Finset Lattice,S⊆l.toFinset → S.Nonempty → S.card<l.toFinset.card →
        ¬0<c (decodeRule a) S := by
  have hc := List.toFinset_card_of_nodup hl
  have hn : 0<l.length ↔ l.toFinset.Nonempty := by rw [←hc,Finset.card_pos]
  constructor
  · rintro ⟨hne,hpos,hmin⟩
    refine ⟨hn.mp hne,(finiteNumerator_pos_iff a l hl).mp hpos,?_⟩
    intro S hS hSne hSc hposS
    obtain ⟨m,hm,he⟩ := maskSubset_complete l hl S hS
    apply hmin m (List.mem_range.mpr hm)
    have hmc := List.toFinset_card_of_nodup (maskSubset_nodup l hl m)
    refine ⟨?_,?_,?_⟩
    · rw [←hmc,he]; exact Finset.card_pos.mpr hSne
    · rw [←hmc,he,←hc]; exact hSc
    · apply (finiteNumerator_pos_iff a _ (maskSubset_nodup l hl m)).mpr
      rw [he]; exact hposS
  · rintro ⟨hne,hpos,hmin⟩
    refine ⟨hn.mpr hne,(finiteNumerator_pos_iff a l hl).mpr hpos,?_⟩
    intro m hm hsm
    obtain ⟨hlen,hlt,hnum⟩ := hsm
    have hmc := List.toFinset_card_of_nodup (maskSubset_nodup l hl m)
    apply hmin (maskSubset (l,m)).toFinset (maskSubset_subset l m)
    · apply Finset.card_pos.mp; rw [hmc]; exact hlen
    · rw [hmc,hc]; exact hlt
    · exact (finiteNumerator_pos_iff a _ (maskSubset_nodup l hl m)).mp hnum

/-- Minimal positive finite coefficients are connected; this is the finite part
of connected_witness, with its minimality hypothesis exposed. -/
theorem minimal_positive_connected (F : CA) (P : Finset Lattice)
    (hne : P.Nonempty) (hpos : 0<c F P)
    (hmin : ∀ S : Finset Lattice,S⊆P → S.Nonempty → 0<c F S → P.card≤S.card) :
    ((overlapGraph F).induce (P : Set Lattice)).Connected := by
  obtain ⟨v,hv⟩ := hne
  let G := (overlapGraph F).induce (P : Set Lattice)
  let vP : P := ⟨v,hv⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨vP,fun w => ?_⟩
  by_contra hnreach
  let S := P.filter (fun i => ∃ hi : i∈P, G.Reachable vP ⟨i,hi⟩)
  have hSP : S⊆P := filter_subset _ _
  have hvS : v∈S := mem_filter.mpr ⟨hv,⟨hv,SimpleGraph.Reachable.rfl⟩⟩
  have hwS : w.val∉S := by
    intro hw
    obtain ⟨hi,hr⟩ := (mem_filter.mp hw).2
    exact hnreach hr
  have hsd : Disjoint (inputSupport F S) (inputSupport F (P\S)) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp hx
    obtain ⟨n,hn,hni⟩ := mem_image.mp hxi
    obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp hy
    obtain ⟨n',hn',hnj⟩ := mem_image.mp hxj
    have hjP := (mem_sdiff.mp hj).1
    have hjn := (mem_sdiff.mp hj).2
    obtain ⟨hiP,hr⟩ := (mem_filter.mp hi).2
    have hij : i≠j := by intro he; subst j; exact hjn hi
    have hadj : G.Adj ⟨i,hiP⟩ ⟨j,hjP⟩ :=
      ⟨hij,n,hn,n',hn',hni.trans hnj.symm⟩
    have hrj : G.Reachable vP ⟨j,hjP⟩ := hr.trans hadj.reachable
    exact hjn (mem_filter.mpr ⟨hjP,⟨hjP,hrj⟩⟩)
  have hfac := coefficient_factorization F S (P\S) hsd
  rw [union_sdiff_of_subset hSP] at hfac
  have hspos : 0<c F S := by
    rw [hfac] at hpos
    have hs0 := coefficient_nonneg F S
    have ht0 := coefficient_nonneg F (P\S)
    nlinarith
  have hcard : S.card<P.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSP,by
    intro he
    exact hwS (he.symm ▸ w.property)⟩)
  have := hmin S hSP ⟨v,hvS⟩ hspos
  omega

end
end Thermal
