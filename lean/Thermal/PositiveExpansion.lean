import Thermal.FiniteReduction
namespace Thermal
open Finset
noncomputable section

def z (F : CA) (ε : ℚ) (T : Finset Lattice) : ℚ := ε^(2*T.card)*c F T

theorem z_nonneg (F : CA) (ε : ℚ) (T : Finset Lattice) : 0≤z F ε T := by
  unfold z
  apply mul_nonneg _ (coefficient_nonneg F T)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg ε) _

theorem W_sum_z (F : CA) (ε : ℚ) (C : Finset Lattice) :
    W F ε C=∑ T∈C.powerset,z F ε T := W_expansion F ε C

theorem W_ge_one (F : CA) (ε : ℚ) (C : Finset Lattice) : 1≤W F ε C := by
  rw [W_expansion]
  exact expansion_ge_one (c F) ε C (coefficient_empty_closed F) (coefficient_nonneg F)

/-- The reduced rational denominator actually divides the padded two-replica power. -/
theorem coefficient_den_divides (F : CA) (T : Finset Lattice) :
    (c F T).den ∣ F.q^(2*(inputSupport F T).card) := by
  have he : c F T = Rat.divInt (collisionNumerator F T) ((F.q : ℤ)^(2*(inputSupport F T).card)) := by
    rw [coefficient_integer_numerator,Rat.divInt_eq_div]
    simp
  have hd : ((c F T).den : ℤ) ∣ (F.q : ℤ)^(2*(inputSupport F T).card) := by
    rw [he]
    exact Rat.den_dvd _ _
  exact_mod_cast hd

end
end Thermal
