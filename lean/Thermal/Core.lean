import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Thermal
open Finset

abbrev Lattice := ℤ × ℤ

/-- A finite local table on the full two-dimensional shift. -/
structure CA where
  q : ℕ
  two_le : 2 ≤ q
  N : Finset Lattice
  neighborhood_nonempty : N.Nonempty
  rule : (N → Fin q) → Fin q

def CA.global (F : CA) (x : Lattice → Fin F.q) (i : Lattice) : Fin F.q :=
  F.rule (fun n => x (i + n.val))

def CA.Onto (F : CA) : Prop := Function.Surjective F.global

def epsilon (q m : ℕ) : ℚ := 1 / (100 * (q : ℚ) * ((m : ℚ) + 1)^2)

def h (q : ℕ) (a b : Fin q) : ℚ := if a = b then (q : ℚ) - 1 else -1

def w (q : ℕ) (ε : ℚ) (a b : Fin q) : ℚ := 1 + ε^2 * h q a b

theorem h_lower (q : ℕ) (a b : Fin q) : -1 ≤ h q a b := by
  unfold h
  split_ifs <;> linarith [Nat.cast_nonneg (α := ℚ) q]

theorem h_upper (q : ℕ) (a b : Fin q) : h q a b ≤ (q : ℚ) - 1 := by
  unfold h
  split_ifs <;> linarith [Nat.cast_nonneg (α := ℚ) q]

theorem h_sum (q : ℕ) (a : Fin q) : ∑ b : Fin q, h q a b = 0 := by
  classical
  have hh : h q a = fun b => (if b = a then (q : ℚ) else 0) - 1 := by
    funext b
    simp only [h]
    split_ifs <;> simp_all
  rw [hh, sum_sub_distrib]
  simp

theorem epsilon_pos (q m : ℕ) (hq : 2 ≤ q) : 0 < epsilon q m := by
  unfold epsilon
  have : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  positivity

theorem epsilon_lt_one (q m : ℕ) (hq : 2 ≤ q) : epsilon q m < 1 := by
  unfold epsilon
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hd : (1 : ℚ) < 100 * (q : ℚ) * ((m : ℚ) + 1)^2 := by nlinarith [sq_nonneg (m : ℚ)]
  exact (div_lt_one (by linarith : (0 : ℚ) < 100 * (q : ℚ) * ((m : ℚ) + 1)^2)).2 hd

theorem w_bounds (q : ℕ) (ε : ℚ) (a b : Fin q) :
    1 - ε^2 ≤ w q ε a b ∧ w q ε a b ≤ 1 + ((q : ℚ) - 1)*ε^2 := by
  have hl := mul_le_mul_of_nonneg_left (h_lower q a b) (sq_nonneg ε)
  have hu := mul_le_mul_of_nonneg_left (h_upper q a b) (sq_nonneg ε)
  constructor <;> unfold w <;> nlinarith

theorem w_positive (q : ℕ) (ε : ℚ) (he0 : 0 ≤ ε) (he1 : ε < 1)
    (a b : Fin q) : 0 < w q ε a b := by
  have hl := (w_bounds q ε a b).1
  have hs : ε^2 < 1 := by nlinarith
  linarith

/-- Ising normalization used in (2.3), with arbitrary rational p in (0,1). -/
def isingWeight (q : ℕ) (ε p : ℚ) (same : Bool) (a b : Fin q) : ℚ :=
  p * (if same then 1 else 0) + (1-p) * w q ε a b

theorem isingWeight_positive (q : ℕ) (ε p : ℚ) (he0 : 0 ≤ ε) (he1 : ε < 1)
    (hp0 : 0 ≤ p) (hp1 : p < 1) (same : Bool) (a b : Fin q) :
    0 < isingWeight q ε p same a b := by
  have hw := w_positive q ε he0 he1 a b
  have hc : 0 < (1-p)*w q ε a b := mul_pos (by linarith) hw
  cases same <;> simp [isingWeight] <;> linarith

/-- Potts tables use integer square-root odds (3 for Q=9; 257 for Q=66049). -/
def pottsWeight (q : ℕ) (ε v : ℚ) (same : Bool) (a b : Fin q) : ℚ :=
  w q ε a b + v * (if same then 1 else 0)

theorem pottsWeight_positive (q : ℕ) (ε v : ℚ) (he0 : 0 ≤ ε) (he1 : ε < 1)
    (hv : 0 ≤ v) (same : Bool) (a b : Fin q) :
    0 < pottsWeight q ε v same a b := by
  have hw := w_positive q ε he0 he1 a b
  cases same <;> simp [pottsWeight] <;> linarith

section Finite
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Collision of two independent samples from a rational finite-output law. -/
def collision (q : ℕ) (p : (I → Fin q) → ℚ) : ℚ :=
  ∑ x, ∑ y, p x * p y * ∏ i, h q (x i) (y i)

/-- The collision is zero for a nonempty uniform output block. -/
theorem collision_uniform (q : ℕ) [Nonempty I] (r : ℚ) :
    collision (I := I) q (fun _ => r) = 0 := by
  classical
  unfold collision
  apply sum_eq_zero
  intro x _
  rw [← mul_sum]
  have he : (∑ y : I → Fin q, ∏ i, h q (x i) (y i)) = 0 := by
    rw [← Fintype.prod_sum]
    simp only [h_sum]
    simp
  rw [he, mul_zero]

/-- Positive-coefficient expansion, separated from the probability model. -/
def expansion {J : Type} [DecidableEq J] (c : Finset J → ℚ) (ε : ℚ) (C : Finset J) : ℚ :=
  ∑ T ∈ C.powerset, ε^(2*T.card) * c T

theorem expansion_eq_one_of_vanish {J : Type} [DecidableEq J]
    (c : Finset J → ℚ) (ε : ℚ) (C : Finset J) (hc0 : c ∅ = 1)
    (hc : ∀ T, T.Nonempty → c T = 0) : expansion c ε C = 1 := by
  classical
  unfold expansion
  rw [sum_eq_single ∅]
  · simp [hc0]
  · intro T _ hT
    rw [hc T (Finset.nonempty_iff_ne_empty.mpr hT), mul_zero]
  · simp

theorem expansion_ge_one {J : Type} [DecidableEq J]
    (c : Finset J → ℚ) (ε : ℚ) (C : Finset J) (hc0 : c ∅ = 1)
    (hc : ∀ T, 0 ≤ c T) : 1 ≤ expansion c ε C := by
  classical
  have hnon : ∀ T ∈ C.powerset, (0 : ℚ) ≤ ε^(2*T.card) * c T := by
    intro T _
    apply mul_nonneg _ (hc T)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg ε) _
  have hh := single_le_sum hnon (show (∅ : Finset J) ∈ C.powerset by simp)
  simpa [expansion, hc0] using hh

end Finite
end Thermal


