import Thermal.FiniteReduction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem global_extend_block (F : CA) (T : Finset Lattice)
    (x : inputSupport F T → Fin F.q) (i : T) :
    F.global (extendPattern F (inputSupport F T) x) i.val = blockMap F T x i := by
  unfold CA.global blockMap
  congr 1
  funext n
  have hm : i.val+n.val ∈ inputSupport F T := by
    exact mem_biUnion.mpr ⟨i.val,i.property,mem_image.mpr ⟨n.val,n.property,rfl⟩⟩
  simp [extendPattern,hm]

theorem positive_output_has_preimage (F : CA) (T : Finset Lattice) (a : T → Fin F.q)
    (hp : 0<outputLaw F T a) : ∃ x, blockMap F T x=a := by
  by_contra hn
  push Not at hn
  have he : outputLaw F T a=0 := by simp [outputLaw,hn]
  linarith

/-- Compactness bridge on the infinite full shift, never a finite torus. -/
theorem finite_block_surjective_onto (F : CA)
    (hf : ∀ (T : Finset Lattice) (a : T → Fin F.q), ∃ x, blockMap F T x=a) : F.Onto := by
  letI : TopologicalSpace (Fin F.q) := ⊥
  letI : DiscreteTopology (Fin F.q) := ⟨rfl⟩
  intro y
  let E : Lattice → Set (Lattice → Fin F.q) := fun i => {x | F.global x i=y i}
  have hc (i : Lattice) : IsClosed (E i) := by
    apply isClosed_eq _ continuous_const
    exact (continuous_of_discreteTopology : Continuous F.rule).comp
      (continuous_pi (fun n => continuous_apply (i+n.val)))
  have hfin (T : Finset Lattice) : (⋂ i ∈ T, E i).Nonempty := by
    obtain ⟨x,hx⟩ := hf T (fun i => y i.val)
    refine ⟨extendPattern F (inputSupport F T) x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change F.global _ i=y i
    rw [global_extend_block F T x ⟨i,hi⟩]
    exact congrFun hx ⟨i,hi⟩
  obtain ⟨x,hx⟩ := CompactSpace.iInter_nonempty hc hfin
  refine ⟨x,funext (fun i => ?_)⟩
  exact Set.mem_iInter.mp hx i

theorem balanced_onto (F : CA) (hb : Balanced F) : F.Onto := by
  apply finite_block_surjective_onto F
  intro T a
  apply positive_output_has_preimage F T a
  rw [hb T a]
  have hq : (0 : ℚ)<F.q := by have := F.two_le; exact_mod_cast (by omega : 0<F.q)
  positivity

theorem nononto_positive_coefficient (F : CA) (hn : ¬F.Onto) :
    ∃ T, T.Nonempty ∧ 0<c F T := by
  by_contra h
  apply hn
  apply balanced_onto F
  apply zero_coefficients_uniform F
  intro T ht
  have hz : ¬0<c F T := by
    intro hp
    exact h ⟨T,ht,hp⟩
  exact le_antisymm (le_of_not_gt hz) (coefficient_nonneg F T)

end
end Thermal
