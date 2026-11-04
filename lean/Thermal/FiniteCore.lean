import Thermal.Core

namespace Thermal
open Finset

/-- The centered one-symbol kernel is its own Gram matrix, up to q. -/
theorem h_gram (q : ℕ) (a b : Fin q) :
    (∑ k : Fin q, h q a k*h q b k) = (q : ℚ)*h q a b := by
  classical
  by_cases hab : a=b
  · subst b
    have he (k : Fin q) : h q a k*h q a k =
        ((q : ℚ)^2-2*q)*(if k=a then 1 else 0)+1 := by
      by_cases hk : k=a <;> simp_all [h, eq_comm] <;> ring
    simp_rw [he]
    simp [sum_add_distrib, mul_sum, h]
    ring
  · have he (k : Fin q) : h q a k*h q b k =
        -(q : ℚ)*(if k=a then 1 else 0) + -(q : ℚ)*(if k=b then 1 else 0)+1 := by
      by_cases hka : k=a <;> by_cases hkb : k=b <;> simp_all [h, eq_comm] <;> ring
    simp_rw [he]
    simp [sum_add_distrib, mul_sum, h, hab]

section Gram
variable {Ω K : Type} [Fintype Ω] [Fintype K]

/-- Algebraic two-replica sum-of-squares identity. No positivity assumption on p. -/
theorem gram_sum_squares (p : Ω → ℚ) (v : Ω → K → ℚ) :
    (∑ x, ∑ y, p x*p y*(∑ k, v x k*v y k)) =
      ∑ k, (∑ x, p x*v x k)^2 := by
  classical
  calc
    _ = ∑ x, ∑ k, ∑ y, p x*p y*(v x k*v y k) := by
      apply sum_congr rfl
      intro x _
      simp_rw [mul_sum]
      rw [sum_comm]
    _ = ∑ k, ∑ x, ∑ y, p x*p y*(v x k*v y k) := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      simp_rw [pow_two, sum_mul, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring
end Gram

section Tensor
variable {I : Type} [Fintype I] [DecidableEq I]

def tensorFeature (q : ℕ) (x k : I → Fin q) : ℚ := ∏ i, h q (x i) (k i)

theorem tensor_gram (q : ℕ) (x y : I → Fin q) :
    (∑ k : I → Fin q, tensorFeature q x k * tensorFeature q y k) =
      (q : ℚ)^(Fintype.card I) * ∏ i, h q (x i) (y i) := by
  classical
  simp_rw [tensorFeature, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (k : Fin q) => h q (x i) k*h q (y i) k)]
  simp_rw [h_gram]
  rw [prod_mul_distrib]
  simp

theorem collision_sum_squares (q : ℕ) (p : (I → Fin q) → ℚ) :
    (q : ℚ)^(Fintype.card I) * collision q p =
      ∑ k, (∑ x, p x*tensorFeature q x k)^2 := by
  rw [← gram_sum_squares p (tensorFeature q)]
  simp_rw [tensor_gram]
  unfold collision
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

theorem collision_nonneg (q : ℕ) (hq : 2 ≤ q) (p : (I → Fin q) → ℚ) :
    0 ≤ collision q p := by
  have hs : 0 ≤ (q : ℚ)^(Fintype.card I)*collision q p := by
    rw [collision_sum_squares]
    exact sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : (0 : ℚ) < (q : ℚ)^(Fintype.card I) := by
    apply pow_pos
    exact_mod_cast (by omega : 0 < q)
  exact nonneg_of_mul_nonneg_right hs hp
end Tensor
end Thermal

