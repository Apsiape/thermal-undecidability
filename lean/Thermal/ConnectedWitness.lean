import Thermal.Factorization

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem connected_witness (F : CA) (hn : ¬F.Onto) : ∃ P, ConnectedWitness F P := by
  obtain ⟨T,ht,hp⟩ := nononto_positive_coefficient F hn
  let candidates := T.powerset.filter (fun P => P.Nonempty ∧ 0<c F P)
  have hcand : candidates.Nonempty := ⟨T,by simp [candidates,ht,hp]⟩
  obtain ⟨P,hP,hmin⟩ := exists_min_image candidates card hcand
  have hPT : P⊆T := mem_powerset.mp (mem_filter.mp hP).1
  obtain ⟨hne,hpos⟩ := (mem_filter.mp hP).2
  refine ⟨P,hne,hpos,?_⟩
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
  have hScand : S∈candidates := by
    exact mem_filter.mpr ⟨mem_powerset.mpr (hSP.trans hPT),⟨⟨v,hvS⟩,hspos⟩⟩
  have hcard : S.card<P.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSP,by
    intro he
    exact hwS (he.symm ▸ w.property)⟩)
  have := hmin S hScand
  omega

end
end Thermal
