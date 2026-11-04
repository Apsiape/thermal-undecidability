import Thermal.MoreCore

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem localWeight_congr (F : CA) (Q : ℕ) (M : Model F Q) (r : Bool)
    (ξ η : Config F.q Q) (he : ∀i∈support F r, ξ i=η i) :
    localWeight M ξ (0,r)=localWeight M η (0,r) := by
  have h0 := he 0 (by simp [support])
  have hr := he (step r) (by simp [support])
  have hglob (b : Bool) : F.global (replica ξ r b) 0=F.global (replica η r b) 0 := by
    unfold CA.global
    congr 1
    funext n
    simp only [zero_add]
    unfold replica
    rw [he n.val (by simp [support,n.property])]
  simp only [localWeight,hiddenWeight,zero_add,h0,hr,hglob]

theorem weight_table_enumeration (F : CA) (Q : ℕ) (M : Model F Q) (r : Bool) :
    ∃ table : List ℚ, ∀ ξ, localWeight M ξ (0,r) ∈ table := by
  by_cases hQ : Q=0
  · subst Q
    refine ⟨[],fun ξ => ?_⟩
    exact Fin.elim0 (ξ 0).1
  · let b : Config F.q Q := fun _ => (⟨0,by omega⟩,fun _ => ⟨0,by have := F.two_le; omega⟩)
    let table := (univ : Finset (support F r → Site F.q Q)).toList.map
      (fun a => localWeight M (paste (support F r) a b) (0,r))
    refine ⟨table,fun ξ => ?_⟩
    have he : localWeight M ξ (0,r)=
        localWeight M (paste (support F r) (fun i => ξ i.val) b) (0,r) := by
      apply localWeight_congr
      intro i hi
      simp [paste,hi]
    rw [he]
    exact List.mem_map.mpr ⟨(fun i => ξ i.val),by simp, rfl⟩

end
end Thermal
