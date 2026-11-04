import Thermal.Detection
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

/-! Source contract: Kari--Taati, Statistical Mechanics of Surjective Cellular Automata,
    arXiv:1311.2319v3, Corollary 21, printed p.20, explicit full-shift sentence.
    The contract below is its two-dimensional finite-alphabet specialization.
    It mentions no Thermal.CA, outputLaw, collision, interaction, or Gibbs model. -/
namespace PublishedCA
open MeasureTheory ProbabilityTheory
noncomputable section
local instance symbolMeasurable (q : ℕ) : MeasurableSpace (Fin q) := ⊤

def uniform (q : ℕ) : Measure ((ℤ × ℤ) → Fin q) :=
  Measure.infinitePi (fun _ : ℤ × ℤ => (uniformOn Set.univ : Measure (Fin q)))

/-- The explicitly stated full-shift specialization in Corollary 21.
    This is an assumption type, not an axiom declaration or a proved theorem. -/
def KariTaati_Corollary21 : Prop := ∀ (q : ℕ), 2≤q →
  ∀ (N : Finset (ℤ × ℤ)) (rule : (N → Fin q) → Fin q),
    let Φ := fun (x : (ℤ × ℤ) → Fin q) i => rule (fun n => x (i+n.val))
    Function.Surjective Φ ↔ Measure.map Φ (uniform q) = uniform q

end
end PublishedCA

namespace Thermal
open Finset MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
local instance symbolMeasurable (q : ℕ) : MeasurableSpace (Fin q) := ⊤

theorem uniform_finite (q : ℕ) (K : Finset Lattice) :
    Measure.pi (fun _ : K => (uniformOn Set.univ : Measure (Fin q))) =
      (uniformOn Set.univ : Measure (K → Fin q)) := by
  simpa using (uniformOn_pi (f := fun _ : K => (Set.univ : Set (Fin q)))).symm

theorem uniform_map_block_mass (F : CA) (T : Finset Lattice) (a : T → Fin F.q) :
    ((Measure.map (blockMap F T)
      (Measure.pi (fun _ : inputSupport F T => (uniformOn Set.univ : Measure (Fin F.q))))) {a}).toReal =
        (outputLaw F T a : ℝ) := by
  rw [uniform_finite,Measure.map_apply (measurable_of_finite _) (measurableSet_singleton a)]
  have hs : (blockMap F T) ⁻¹' {a} =
      ((univ.filter (fun x => blockMap F T x=a) : Finset (inputSupport F T → Fin F.q)) : Set _) := by
    ext x; simp
  rw [hs,uniformOn_univ,Measure.count_apply_finset]
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,ENNReal.toReal_div,
    ENNReal.toReal_natCast,outputLaw]
  push_cast
  congr 1
  have hcount : (∑ x : inputSupport F T → Fin F.q,
      if blockMap F T x=a then (1 : ℚ) else 0) =
        ((univ.filter (fun x => blockMap F T x=a) : Finset (inputSupport F T → Fin F.q)).card : ℚ) := by
    simp
  exact_mod_cast hcount.symm

theorem balance (H : PublishedCA.KariTaati_Corollary21) (F : CA) :
    F.Onto ↔ Balanced F := by
  refine ⟨fun ho => ?_,balanced_onto F⟩
  letI : Nonempty (Fin F.q) := ⟨⟨0,by have := F.two_le; omega⟩⟩
  have hpres : Measure.map F.global (PublishedCA.uniform F.q)=PublishedCA.uniform F.q :=
    (H F.q F.two_le F.N F.rule).mp ho
  intro T a
  have hglobal : Measurable F.global := by
    apply Measurable.of_eval
    intro i
    exact (measurable_of_finite F.rule).comp (Measurable.of_eval (fun (n : F.N) => measurable_pi_apply (i+n.val)))
  have hb : Measurable (blockMap F T) := measurable_of_finite _
  have hres (K : Finset Lattice) : Measurable (K.restrict : (Lattice → Fin F.q) → (K → Fin F.q)) := Measurable.of_eval (fun (i : K) => measurable_pi_apply i.val)
  have hmap : Measure.map (blockMap F T)
      (Measure.pi (fun _ : inputSupport F T => (uniformOn Set.univ : Measure (Fin F.q)))) =
      Measure.pi (fun _ : T => (uniformOn Set.univ : Measure (Fin F.q))) := by
    calc
      _ = Measure.map (blockMap F T) (Measure.map (inputSupport F T).restrict (PublishedCA.uniform F.q)) := by
        rw [PublishedCA.uniform,Measure.infinitePi_map_restrict]
      _ = Measure.map (T.restrict ∘ F.global) (PublishedCA.uniform F.q) := by
        rw [Measure.map_map hb (hres _)]
        rfl
      _ = Measure.map T.restrict (Measure.map F.global (PublishedCA.uniform F.q)) :=
        (Measure.map_map (hres _) hglobal).symm
      _ = _ := by rw [hpres,PublishedCA.uniform,Measure.infinitePi_map_restrict]
  have he := congrArg (fun μ : Measure (T → Fin F.q) => (μ {a}).toReal) hmap
  rw [uniform_map_block_mass,uniform_finite,uniformOn_univ] at he
  simp only [Measure.count_singleton,one_div,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,Nat.cast_pow] at he
  have he' : (outputLaw F T a : ℝ)=1/(F.q : ℝ)^T.card := by
    simpa [ENNReal.toReal_pow,ENNReal.toReal_natCast,one_div] using he
  apply (Rat.cast_injective (α := ℝ))
  push_cast
  exact he'

theorem coefficient_detection (H : PublishedCA.KariTaati_Corollary21) (F : CA) :
    (∀ T, T.Nonempty → c F T=0) ↔ F.Onto :=
  ⟨fun hz => balanced_onto F (zero_coefficients_uniform F hz),
    fun ho => balanced_coefficient_zero F ((balance H F).mp ho)⟩

theorem positive_coefficient_nononto (H : PublishedCA.KariTaati_Corollary21)
    (F : CA) (T : Finset Lattice) (ht : T.Nonempty) (hp : 0<c F T) : ¬F.Onto := by
  intro ho
  have hz := balanced_coefficient_zero F ((balance H F).mp ho) T ht
  linarith

/-- Public finite cancellation entry point, relative to the exact named balance contract. -/
theorem onto_collision_core_published (H : PublishedCA.KariTaati_Corollary21)
    (F : CA) (ho : F.Onto) :
    (∀ T, T.Nonempty → c F T=0) ∧ (∀ ε C, W F ε C=1) :=
  onto_collision_core F (fun h => (balance H F).mp h) ho

end
end Thermal
