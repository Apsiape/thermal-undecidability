import Thermal.CollisionBridge
namespace Thermal
open Finset
noncomputable section

theorem physical_dimensions : 2*4^4=512 ∧ 9*4^4=2304 ∧ 66049*4^4=16908544 := by norm_num

theorem exploration_rational_budget :
    (2*(128/961 : ℚ)+1/64)=17345/61504 ∧ (17345/61504 : ℚ)<1/3 ∧
    2/(1-(17345/61504 : ℚ))=123008/44159 ∧ (123008/44159 : ℚ)<3 := by norm_num

theorem h_abs_bound (q : ℕ) (hq : 2≤q) (a b : Fin q) : |h q a b|≤(q : ℚ)-1 := by
  unfold h
  split_ifs <;> have hq' : (2 : ℚ)≤q := by exact_mod_cast hq
  · rw [abs_of_nonneg (by linarith)]
  · norm_num
    linarith

theorem collision_upper {I : Type} [Fintype I] [DecidableEq I]
    (q : ℕ) (hq : 2≤q) (p : (I → Fin q) → ℚ) (hp0 : ∀x, 0≤p x) (hp : ∑x,p x=1) :
    collision q p ≤ ((q : ℚ)-1)^(Fintype.card I) := by
  classical
  have hu (x y : I → Fin q) : (∏i,h q (x i) (y i))≤((q : ℚ)-1)^(Fintype.card I) := by
    calc
      _ ≤ |∏i,h q (x i) (y i)| := le_abs_self _
      _ = ∏i,|h q (x i) (y i)| := abs_prod _ _
      _ ≤ ∏_i : I, ((q : ℚ)-1) := prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => h_abs_bound q hq (x i) (y i))
      _ = _ := by simp
  calc
    _ ≤ ∑x, ∑y,p x*p y*((q : ℚ)-1)^(Fintype.card I) := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hu x y) (mul_nonneg (hp0 x) (hp0 y))
    _ = _ := by
      simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
      rw [hp]
      simp

theorem outputLaw_nonneg (F : CA) (T : Finset Lattice) (a : T → Fin F.q) : 0≤outputLaw F T a := by
  unfold outputLaw
  positivity

theorem outputLaw_total (F : CA) (T : Finset Lattice) : ∑a,outputLaw F T a=1 := by
  classical
  unfold outputLaw
  rw [← sum_div, sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  have hq : (F.q : ℚ)≠0 := by have := F.two_le; exact_mod_cast (by omega : F.q ≠ 0)
  simp [Fintype.card_pi, hq]

theorem coefficient_upper_closed (F : CA) (T : Finset Lattice) : c F T≤((F.q : ℚ)-1)^T.card := by
  simpa [c] using collision_upper F.q F.two_le (outputLaw F T) (outputLaw_nonneg F T) (outputLaw_total F T)

theorem coefficient_empty_closed (F : CA) : c F ∅=1 := by
  classical
  have hprod (x y : (∅ : Finset Lattice) → Fin F.q) : (∏i,h F.q (x i) (y i))=1 := by simp
  unfold c collision
  simp_rw [hprod, mul_one, ← mul_sum, outputLaw_total, mul_one]
  exact outputLaw_total F ∅

theorem local_weight_positive {F : CA} {Q : ℕ} (M : Model F Q)
    (he : 0≤M.ε ∧ M.ε<1) (ho : ∀ r, 0≤M.openWeight r)
    (hc : ∀ r, 0<M.closedScale r) (ξ : Config F.q Q) (e : Edge) :
    0<localWeight M ξ e := by
  have hh : 0<hiddenWeight F Q M.ε ξ e := w_positive F.q M.ε he.1 he.2 _ _
  have hx := mul_pos (hc e.2) hh
  have ho' : 0≤M.openWeight e.2*(if (ξ e.1).1=(ξ (e.1+step e.2)).1 then (1 : ℚ) else 0) := by
    apply mul_nonneg (ho e.2)
    split_ifs <;> norm_num
  unfold localWeight
  linarith

theorem ising_local_positive (F : CA) (ξ : Config F.q 2) (e : Edge) :
    0<localWeight (ising F) ξ e := by
  apply local_weight_positive
  · exact ⟨(epsilon_pos F.q F.N.card F.two_le).le, epsilon_lt_one F.q F.N.card F.two_le⟩
  · intro r; cases r <;> norm_num [ising]
  · intro r; cases r <;> norm_num [ising]

theorem potts_local_positive (F : CA) (v : ℕ) (ε : ℚ) (he : 0≤ε ∧ ε<1)
    (ξ : Config F.q (v*v)) (e : Edge) : 0<localWeight (potts F v ε) ξ e := by
  apply local_weight_positive _ he
  · intro r; dsimp [potts]; positivity
  · intro r; norm_num [potts]

theorem epsilonU_pos (F : CA) : 0<epsilonU F := by
  unfold epsilonU
  apply lt_min (epsilon_pos F.q F.N.card F.two_le)
  have hq : (0 : ℚ)<F.q := by have := F.two_le; exact_mod_cast (by omega : 0<F.q)
  positivity

theorem epsilonU_lt_one (F : CA) : epsilonU F<1 :=
  lt_of_le_of_lt (min_le_left _ _) (epsilon_lt_one F.q F.N.card F.two_le)

theorem magnetic_local_positive (F : CA) (ξ : Config F.q 9) (e : Edge) :
    0<localWeight (magnetic F) ξ e := potts_local_positive F 3 _
      ⟨(epsilon_pos F.q F.N.card F.two_le).le,epsilon_lt_one F.q F.N.card F.two_le⟩ ξ e

theorem unique_local_positive (F : CA) (ξ : Config F.q 66049) (e : Edge) :
    0<localWeight (uniqueModel F) ξ e := potts_local_positive F 257 _
      ⟨(epsilonU_pos F).le,epsilonU_lt_one F⟩ ξ e

end
end Thermal
