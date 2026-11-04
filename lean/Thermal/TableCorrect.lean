import Thermal.RuleCoding
import Thermal.TableProgram
namespace Thermal
open Finset Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable



theorem algorithm_ncard (a : RuleCode) : ncard a = (decodeRule a).N.card := by
  exact (List.card_toFinset (l := 0::a.2.1)).symm

theorem maximum_map_eq_sup {α : Type} [DecidableEq α] (l : List α) (f : α → ℕ) :
    maximum (l.map f) = l.toFinset.sup f := by
  induction l with
  | nil => simp [maximum]
  | cons a l ih => simp [maximum, List.foldr_map, ← ih, Finset.sup_insert]

theorem algorithm_diameter (l : List Lattice) : diameter l = supportDiameter l.toFinset := by
  unfold diameter supportDiameter
  rw [maximum_map_eq_sup]
  congr 1
  funext i
  exact maximum_map_eq_sup l (distance i)

theorem algorithm_radius (a : RuleCode) : ruleRadius a = radius (decodeRule a) := by
  unfold ruleRadius radius
  rw [algorithm_diameter,algorithm_diameter]
  congr 1 <;> congr 1 <;> ext i <;>
    simp [neighborhood,decodeRule,support,step]

theorem denominator_pos (a : RuleCode) : 0 < denominator a := by
  unfold denominator qValue
  positivity

theorem algorithm_epsilon (a : RuleCode) : epsilon (decodeRule a).q (decodeRule a).N.card =
    1/(denominator a : ℚ) := by
  rw [← algorithm_ncard]
  simp [epsilon,denominator,qValue,decodeRule]

theorem algorithm_epsilonU (a : RuleCode) : epsilonU (decodeRule a) =
    1/(uniqueDenominator a : ℚ) := by
  unfold epsilonU uniqueDenominator
  rw [algorithm_epsilon,← algorithm_radius,← algorithm_ncard]
  have hd : (0 : ℚ) < denominator a := by exact_mod_cast denominator_pos a
  have he : (0 : ℚ) < 16*qValue a*(ncard a+2)*2^ruleRadius a := by
    unfold qValue
    positivity
  rw [Nat.cast_max]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_pow]
  change min (1/(denominator a : ℚ)) (1/(16*qValue a*(ncard a+2)*2^ruleRadius a)) = _
  rcases le_total (denominator a : ℚ) (16*qValue a*(ncard a+2)*2^ruleRadius a) with h|h
  · rw [max_eq_right h,min_eq_right (one_div_le_one_div_of_le hd h)]
  · rw [max_eq_left h,min_eq_left (one_div_le_one_div_of_le he h)]

theorem ruleDigit_correct (a : RuleCode) (Q : ℕ) (hQ : 0<Q) (n : ℕ) (r : Fin 4) :
    ruleDigit (a,(Q,(n,r.val))) =
      ((decodeRule a).rule (fun i => (codedConfig (decodeRule a) Q hQ n i.val).2 r)).val := by
  unfold ruleDigit evalLocal
  simp only [List.foldl_map]
  have hf := @List.foldl_attach Lattice ℕ (0::a.2.1)
    (fun acc i => acc*qValue a + inputDigit ((qValue a,Q),(n,(i,r.val)))) 0
  exact congrArg (fun k => ((a.2.2[k]?).getD 0) % qValue a) hf.symm

theorem fraction_correct (q D v k : ℕ) (hD : 0<D) (hk : 0<k)
    (same equal : Bool) :
    ratDecode (fraction ((q,D),(v,(k,(same,equal))))) =
      (v : ℚ)/k*(if same then 1 else 0) +
      (1/(k : ℚ))*(1+(1/(D : ℚ))^2*(if equal then (q : ℚ)-1 else -1)) := by
  have hD2 : 1 ≤ D^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hkD : 1 ≤ k*D^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hDn : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hkn : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [fraction,ratDecode]
  cases same <;> cases equal <;>
    simp [Nat.cast_sub hD2,Nat.cast_sub hkD,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] <;>
    field_simp <;> ring

end
end Thermal


