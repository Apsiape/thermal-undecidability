import Thermal.MoreCore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.ModEq

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def siteDigit (q Q : ℕ) (s : Site q Q) : Fin (Q*q^4) :=
  Fin.cast (Nat.mul_comm (q^4) Q) (finProdFinEquiv (finFunctionFinEquiv s.2,s.1))

def decodeSite (q Q : ℕ) (hq : 0<q) (hQ : 0<Q) (n : ℕ) : Site q Q := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero Q := ⟨by omega⟩
  exact (Fin.ofNat Q n,fun r => Fin.ofNat q (n/Q/q^r.val))

theorem fin_digits_spec {b n : ℕ} (d : Fin n → Fin b) (i : Fin n) :
    (finFunctionFinEquiv d).val / b^i.val % b = (d i).val := by
  exact congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply d) i)

theorem decode_siteDigit (q Q : ℕ) (hq : 0<q) (hQ : 0<Q) (s : Site q Q) :
    decodeSite q Q hq hQ (siteDigit q Q s).val=s := by
  let H := (finFunctionFinEquiv s.2).val
  have hv : (siteDigit q Q s).val = s.1.val+Q*H := rfl
  have hd : (s.1.val+Q*H)/Q=H := by
    rw [Nat.add_mul_div_left _ _ hQ,Nat.div_eq_of_lt s.1.isLt,zero_add]
  apply Prod.ext
  · apply Fin.ext
    change (siteDigit q Q s).val % Q=s.1.val
    rw [hv,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt s.1.isLt]
  · funext r
    apply Fin.ext
    change (siteDigit q Q s).val/Q/q^r.val%q=(s.2 r).val
    rw [hv,hd]
    exact fin_digits_spec s.2 r

/-- Decoding a site depends only on the digit modulo Q*q^4. -/
theorem decodeSite_mod (q Q : ℕ) (hq : 0<q) (hQ : 0<Q) (n : ℕ) :
    decodeSite q Q hq hQ (n%(Q*q^4))=decodeSite q Q hq hQ n := by
  apply Prod.ext
  · apply Fin.ext
    change (n%(Q*q^4))%Q=n%Q
    exact Nat.mod_mod_of_dvd n (dvd_mul_right Q (q^4))
  · funext r
    apply Fin.ext
    change ((n%(Q*q^4))/Q/q^r.val)%q=(n/Q/q^r.val)%q
    rw [Nat.mod_mul_right_div_self]
    rw [← Nat.mod_mul_right_div_self (n/Q%q^4) (q^r.val) q,
      ← Nat.mod_mul_right_div_self (n/Q) (q^r.val) q]
    congr 1
    exact Nat.mod_mod_of_dvd (n/Q) (by
      rw [← pow_succ]
      exact pow_dvd_pow q (by have := r.isLt; omega))

/-- Every finite collection of sites is attained by the natural-number digit coding. -/
theorem finite_digit_coding_complete (q Q : ℕ) (hq : 0<q) (hQ : 0<Q)
    (K : Finset Lattice) (ξ : Config q Q) :
    ∃ n, ∀ i∈K, decodeSite q Q hq hQ (n/(Q*q^4)^(Encodable.encode i))=ξ i := by
  let B := Q*q^4
  let k := K.sup Encodable.encode+1
  let d : Fin k → Fin B := fun j => siteDigit q Q (ξ ((Encodable.decode (α := Lattice) j.val).getD 0))
  refine ⟨(finFunctionFinEquiv d).val,fun i hi => ?_⟩
  have hik : Encodable.encode i<k := Nat.lt_succ_of_le (le_sup (f := Encodable.encode) hi)
  let j : Fin k := ⟨Encodable.encode i,hik⟩
  have hd := fin_digits_spec d j
  have hdi : d j=siteDigit q Q (ξ i) := by
    change siteDigit q Q (ξ ((Encodable.decode (Encodable.encode i)).getD 0))=siteDigit q Q (ξ i)
    rw [Encodable.encodek]
    rfl
  have hmod : (finFunctionFinEquiv d).val/B^(Encodable.encode i)%B=(siteDigit q Q (ξ i)).val := by
    simpa only [j,hdi] using hd
  rw [← decodeSite_mod q Q hq hQ, hmod]
  exact decode_siteDigit q Q hq hQ (ξ i)

end
end Thermal
