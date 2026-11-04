import Thermal.MoreCore

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Split a finite assignment into its restriction and the unused coordinates. -/
def splitPatterns {α A : Type} [DecidableEq α] (S T : Finset α) (hst : S ⊆ T) :
    (T → A) ≃ (S → A) × (↥(T \ S) → A) where
  toFun x := (fun i => x ⟨i.val,hst i.property⟩,
    fun i => x ⟨i.val,(mem_sdiff.mp i.property).1⟩)
  invFun x i := if hi : i.val ∈ S then x.1 ⟨i.val,hi⟩
    else x.2 ⟨i.val,mem_sdiff.mpr ⟨i.property,hi⟩⟩
  left_inv x := by funext i; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i; simp [i.property]
    · funext i; simp [(mem_sdiff.mp i.property).2]

theorem sum_restrict {α A : Type} [DecidableEq α] [Fintype A]
    (S T : Finset α) (hst : S ⊆ T) (f : (S → A) → ℚ) :
    (∑ x : T → A, f (fun i => x ⟨i.val,hst i.property⟩)) =
      (Fintype.card A : ℚ)^(T \ S).card * ∑ x, f x := by
  classical
  trans ∑ x : (S → A) × (↥(T \ S) → A), f x.1
  · exact Fintype.sum_equiv (splitPatterns S T hst) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type]
  simp [← sum_mul, mul_comm]

theorem average_restrict {α : Type} [DecidableEq α] (q : ℕ) (hq : 0 < q)
    (S T : Finset α) (hst : S ⊆ T) (f : (S → Fin q) → ℚ) :
    (∑ x : T → Fin q, f (fun i => x ⟨i.val,hst i.property⟩)) / (q : ℚ)^T.card =
      (∑ x, f x) / (q : ℚ)^S.card := by
  rw [sum_restrict]
  have hc : T.card = (T \ S).card + S.card := by
    rw [card_sdiff_of_subset hst]; have := card_le_card hst; omega
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp only [Fintype.card_fin]
  rw [hc, pow_add]
  field_simp

theorem inputSupport_mono (F : CA) {S T : Finset Lattice} (hst : S ⊆ T) :
    inputSupport F S ⊆ inputSupport F T := by
  intro x hx
  rcases mem_biUnion.mp hx with ⟨i,hi,hx⟩
  exact mem_biUnion.mpr ⟨i,hst hi,hx⟩

theorem blockMap_restrict (F : CA) (S T : Finset Lattice) (hst : S ⊆ T)
    (x : inputSupport F T → Fin F.q) :
    (fun i : S => blockMap F T x ⟨i.val,hst i.property⟩) =
      blockMap F S (fun j => x ⟨j.val,inputSupport_mono F hst j.property⟩) := rfl

/-- Push a finite test through the exact padded output distribution. -/
theorem outputLaw_expect (F : CA) (T : Finset Lattice) (f : (T → Fin F.q) → ℚ) :
    (∑ a, outputLaw F T a * f a) =
      (∑ x, f (blockMap F T x)) / (F.q : ℚ)^(inputSupport F T).card := by
  unfold outputLaw
  simp_rw [div_mul_eq_mul_div, sum_mul, ← sum_div]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro x _
  simp

theorem outputLaw_restrict_expect (F : CA) (S T : Finset Lattice) (hst : S ⊆ T)
    (f : (S → Fin F.q) → ℚ) :
    (∑ b, outputLaw F T b * f (fun i => b ⟨i.val,hst i.property⟩)) =
      ∑ a, outputLaw F S a * f a := by
  rw [outputLaw_expect, outputLaw_expect]
  simp_rw [blockMap_restrict F S T hst]
  exact average_restrict F.q (by have := F.two_le; omega)
    _ _ (inputSupport_mono F hst) (fun x => f (blockMap F S x))

theorem outputLaw_marginal (F : CA) (S T : Finset Lattice) (hST : S⊆T)
    (a : S → Fin F.q) :
    (∑ b : T → Fin F.q, outputLaw F T b *
      (if (fun i : S => b ⟨i.val,hST i.property⟩)=a then 1 else 0)) = outputLaw F S a := by
  rw [outputLaw_restrict_expect F S T hST (fun b => if b=a then 1 else 0)]
  simp

/-- Integer preimage count; no rational encoding is used in this definition. -/
def outputCount (F : CA) (T : Finset Lattice) (a : T → Fin F.q) : ℤ :=
  ∑ x : inputSupport F T → Fin F.q, if blockMap F T x = a then 1 else 0

def integerKernel (q : ℕ) (a b : Fin q) : ℤ := if a=b then (q : ℤ)-1 else -1

def collisionNumerator (F : CA) (T : Finset Lattice) : ℤ :=
  ∑ a, ∑ b, outputCount F T a * outputCount F T b * ∏ i, integerKernel F.q (a i) (b i)

theorem outputLaw_integer_numerator (F : CA) (T : Finset Lattice) (a : T → Fin F.q) :
    outputLaw F T a = (outputCount F T a : ℚ) / (F.q : ℚ)^(inputSupport F T).card := by
  simp [outputLaw, outputCount]

theorem coefficient_integer_numerator (F : CA) (T : Finset Lattice) :
    c F T = (collisionNumerator F T : ℚ) / (F.q : ℚ)^(2*(inputSupport F T).card) := by
  have hk (a b : Fin F.q) : (integerKernel F.q a b : ℚ) = h F.q a b := by
    simp [integerKernel,h]
  unfold c collision collisionNumerator
  push_cast
  simp_rw [hk, outputLaw_integer_numerator, div_mul_div_comm, div_mul_eq_mul_div,
    ← sum_div]
  congr 1
  rw [two_mul, pow_add]

theorem coefficient_denominator (F : CA) (T : Finset Lattice) :
    ∃ k : ℤ, c F T = k / (F.q : ℚ)^(2*(inputSupport F T).card) :=
  ⟨collisionNumerator F T, coefficient_integer_numerator F T⟩

theorem inputSupport_card (F : CA) (T : Finset Lattice) :
    (inputSupport F T).card ≤ F.N.card*T.card := by
  unfold inputSupport
  calc
    _ ≤ T.card*F.N.card := card_biUnion_le_card_mul _ _ _ (fun _ _ => card_image_le)
    _ = _ := Nat.mul_comm _ _

theorem coefficient_lower (F : CA) (T : Finset Lattice) (hc : 0<c F T) :
    (F.q : ℚ)^(-(2*F.N.card*T.card : ℕ) : ℤ) ≤ c F T := by
  have hq : (0 : ℚ)<F.q := by have := F.two_le; exact_mod_cast (by omega : 0<F.q)
  have hd := pow_pos hq (2*(inputSupport F T).card)
  have hn : (0 : ℚ)<(collisionNumerator F T : ℚ) := by
    rw [coefficient_integer_numerator] at hc
    exact (div_pos_iff_of_pos_right hd).mp hc
  have hnz : 1 ≤ collisionNumerator F T := by exact_mod_cast hn
  have hnq : (1 : ℚ) ≤ (collisionNumerator F T : ℚ) := by exact_mod_cast hnz
  rw [zpow_neg, zpow_natCast, inv_eq_one_div]
  calc
    _ ≤ 1/(F.q : ℚ)^(2*(inputSupport F T).card) := by
      apply one_div_le_one_div_of_le hd
      apply pow_le_pow_right₀ (by have := F.two_le; exact_mod_cast (by omega : 1≤F.q))
      have := inputSupport_card F T
      nlinarith
    _ ≤ _ := by
      rw [coefficient_integer_numerator]
      exact div_le_div_of_nonneg_right hnq hd.le

theorem outputLaw_pair_restrict_expect (F : CA) (S T : Finset Lattice) (hst : S ⊆ T)
    (f : (S → Fin F.q) → (S → Fin F.q) → ℚ) :
    (∑ b, ∑ d, outputLaw F T b * outputLaw F T d *
      f (fun i => b ⟨i.val,hst i.property⟩) (fun i => d ⟨i.val,hst i.property⟩)) =
      ∑ a, ∑ e, outputLaw F S a * outputLaw F S e * f a e := by
  simp_rw [mul_assoc, ← mul_sum]
  simp_rw [outputLaw_restrict_expect F S T hst]
  exact outputLaw_restrict_expect F S T hst (fun a => ∑ e, outputLaw F S e * f a e)

/-- An arbitrary extension used solely to express subset products without dependent sums. -/
def extendPattern (F : CA) (C : Finset Lattice) (x : C → Fin F.q) (i : Lattice) : Fin F.q :=
  if hi : i∈C then x ⟨i,hi⟩ else ⟨0,by have := F.two_le; omega⟩

theorem extendPattern_on (F : CA) (C : Finset Lattice) (x : C → Fin F.q) (i : C) :
    extendPattern F C x i.val = x i := by simp [extendPattern,i.property]

theorem subset_collision (F : CA) (S C : Finset Lattice) (hst : S ⊆ C) :
    (∑ x, ∑ y, outputLaw F C x * outputLaw F C y *
      ∏ i ∈ S, h F.q (extendPattern F C x i) (extendPattern F C y i)) = c F S := by
  have he (x y : C → Fin F.q) :
      (∏ i ∈ S, h F.q (extendPattern F C x i) (extendPattern F C y i)) =
        ∏ i : S, h F.q (x ⟨i.val,hst i.property⟩) (y ⟨i.val,hst i.property⟩) := by
    calc
      _ = ∏ i : S, h F.q (extendPattern F C x i.val) (extendPattern F C y i.val) :=
        (prod_coe_sort S _).symm
      _ = _ := by
        apply prod_congr rfl
        intro i _
        simp [extendPattern,hst i.property]
  simp_rw [he]
  exact outputLaw_pair_restrict_expect F S C hst (fun x y => ∏i,h F.q (x i) (y i))

theorem W_expansion (F : CA) (ε : ℚ) (C : Finset Lattice) :
    W F ε C = expansion (c F) ε C := by
  have hp (x y : C → Fin F.q) :
      (∏ i : C, w F.q ε (x i) (y i)) =
        ∑ S ∈ C.powerset, ε^(2*S.card) *
          ∏ i ∈ S, h F.q (extendPattern F C x i) (extendPattern F C y i) := by
    calc
      _ = ∏ i ∈ C, (1+ε^2*h F.q (extendPattern F C x i) (extendPattern F C y i)) := by
        calc
          _ = ∏ i : C, (1+ε^2*h F.q (extendPattern F C x i.val) (extendPattern F C y i.val)) := by
            apply prod_congr rfl
            intro i _
            simp only [extendPattern_on,w]
          _ = _ := prod_coe_sort C (fun i => 1+ε^2*h F.q (extendPattern F C x i) (extendPattern F C y i))
      _ = _ := by
        rw [prod_one_add]
        apply sum_congr rfl
        intro S _
        rw [prod_mul_distrib, prod_const, ← pow_mul]
  unfold W expansion
  simp_rw [hp, mul_sum]
  simp_rw [sum_comm (s := univ) (t := C.powerset)]
  apply sum_congr rfl
  intro S hs
  -- Move the subset coefficient outside the two replica sums.
  calc
    _ = ε^(2*S.card) * (∑ x, ∑ y, outputLaw F C x * outputLaw F C y *
        ∏ i ∈ S, h F.q (extendPattern F C x i) (extendPattern F C y i)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [subset_collision F S C (mem_powerset.mp hs)]


/-- Vanishing collision forces every centered tensor moment to vanish. -/
theorem zero_coefficient_tensorMoment (F : CA) (S : Finset Lattice)
    (hz : c F S=0) (k : S → Fin F.q) :
    (∑ x, outputLaw F S x * tensorFeature F.q x k)=0 := by
  have hs : (∑ k, (∑ x, outputLaw F S x * tensorFeature F.q x k)^2)=0 := by
    rw [← collision_sum_squares]
    simpa only [Fintype.card_coe,c,mul_zero] using
      congrArg (fun z : ℚ => (F.q : ℚ)^S.card*z) hz
  have hk := (sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs k (mem_univ k)
  exact (sq_eq_zero_iff).mp hk

theorem delta_tensor {I : Type} [Fintype I] [DecidableEq I] (q : ℕ)
    (x a : I → Fin q) :
    (∏ i, (1+h q (x i) (a i))) = if x=a then (q : ℚ)^(Fintype.card I) else 0 := by
  classical
  by_cases hx : x=a
  · subst x; simp [h]
  · rw [ite_eq_right_iff.mpr (fun h => (hx h).elim)]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    apply prod_eq_zero (mem_univ i)
    simp [h,hi]

theorem zero_coefficients_uniform (F : CA) (hz : ∀ S, S.Nonempty → c F S=0) :
    Balanced F := by
  intro T a
  have hp (x : T → Fin F.q) :
      (∏ i : T, (1+h F.q (x i) (a i))) =
        ∑ S ∈ T.powerset, ∏ i ∈ S, h F.q (extendPattern F T x i) (extendPattern F T a i) := by
    calc
      _ = ∏ i ∈ T, (1+h F.q (extendPattern F T x i) (extendPattern F T a i)) := by
        calc
          _ = ∏ i : T, (1+h F.q (extendPattern F T x i.val) (extendPattern F T a i.val)) := by
            apply prod_congr rfl
            intro i _
            simp only [extendPattern_on]
          _ = _ := prod_coe_sort T (fun i => 1+h F.q (extendPattern F T x i) (extendPattern F T a i))
      _ = _ := prod_one_add _
  have hm (S : Finset Lattice) (hs : S∈T.powerset) (hne : S≠∅) :
      (∑ x, outputLaw F T x * ∏ i ∈ S,
        h F.q (extendPattern F T x i) (extendPattern F T a i))=0 := by
    have hst := mem_powerset.mp hs
    have he (x : T → Fin F.q) :
        (∏ i ∈ S, h F.q (extendPattern F T x i) (extendPattern F T a i)) =
          tensorFeature F.q (fun i : S => x ⟨i.val,hst i.property⟩)
            (fun i : S => a ⟨i.val,hst i.property⟩) := by
      unfold tensorFeature
      calc
        _ = ∏ i : S, h F.q (extendPattern F T x i.val) (extendPattern F T a i.val) :=
          (prod_coe_sort S _).symm
        _ = _ := by
          apply prod_congr rfl
          intro i _
          simp [extendPattern,hst i.property]
    simp_rw [he]
    rw [outputLaw_restrict_expect F S T hst
      (fun x => tensorFeature F.q x (fun i : S => a ⟨i.val,hst i.property⟩))]
    exact zero_coefficient_tensorMoment F S (hz S (nonempty_iff_ne_empty.mpr hne)) _
  have hid : outputLaw F T a * (F.q : ℚ)^T.card = 1 := by
    calc
      _ = ∑ x, outputLaw F T x * ∏ i : T, (1+h F.q (x i) (a i)) := by
        simp_rw [delta_tensor]
        simp
      _ = ∑ S ∈ T.powerset, ∑ x, outputLaw F T x *
          ∏ i ∈ S, h F.q (extendPattern F T x i) (extendPattern F T a i) := by
        simp_rw [hp,mul_sum]
        rw [sum_comm]
      _ = ∑ x, outputLaw F T x := by
        rw [sum_eq_single ∅]
        · simp
        · intro S hs hne
          exact hm S hs hne
        · simp
      _ = 1 := outputLaw_total F T
  have hq : (F.q : ℚ)^T.card ≠ 0 := by
    apply pow_ne_zero
    have := F.two_le
    exact_mod_cast (by omega : F.q≠0)
  exact (eq_div_iff hq).mpr hid

end
end Thermal
