import Thermal.Definitions
import Thermal.FiniteCore
namespace Thermal
open Finset
noncomputable section

theorem coefficient_nonneg (F : CA) (T : Finset Lattice) : 0 ≤ c F T :=
  collision_nonneg F.q F.two_le (outputLaw F T)

theorem balanced_coefficient_zero (F : CA) (hb : Balanced F) (T : Finset Lattice)
    (ht : T.Nonempty) : c F T=0 := by
  obtain ⟨t,ht⟩ := ht
  letI : Nonempty T := ⟨⟨t,ht⟩⟩
  have hp : outputLaw F T = fun _ => 1/(F.q : ℚ)^T.card := funext (hb T)
  unfold c
  rw [hp]
  exact collision_uniform F.q _

theorem w_sum (q : ℕ) (ε : ℚ) (a : Fin q) : ∑ b, w q ε a b = q := by
  simp only [w, sum_add_distrib, ← mul_sum, h_sum, mul_zero, add_zero]
  simp

theorem balanced_W (F : CA) (hb : Balanced F) (ε : ℚ) (C : Finset Lattice) :
    W F ε C=1 := by
  have hp : outputLaw F C = fun _ => 1/(F.q : ℚ)^C.card := funext (hb C)
  have hsum (x : C → Fin F.q) :
      (∑ y : C → Fin F.q, ∏ i, w F.q ε (x i) (y i)) = (F.q : ℚ)^C.card := by
    rw [← Fintype.prod_sum]
    simp only [w_sum]
    simp
  have hq : (F.q : ℚ) ≠ 0 := by have := F.two_le; exact_mod_cast (by omega : F.q ≠ 0)
  have hn : (F.q : ℚ)^C.card ≠ 0 := pow_ne_zero _ hq
  unfold W
  simp_rw [hp, ← mul_sum, hsum]
  simp [Fintype.card_pi, Fintype.card_coe]
  field_simp

theorem onto_collision_core (F : CA) (balance : F.Onto → Balanced F) (ho : F.Onto) :
    (∀ T, T.Nonempty → c F T=0) ∧ (∀ ε C, W F ε C=1) :=
  ⟨balanced_coefficient_zero F (balance ho), balanced_W F (balance ho)⟩

end
end Thermal

