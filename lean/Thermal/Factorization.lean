import Thermal.Detection

namespace Thermal
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def splitCoverPatterns {α A : Type} [DecidableEq α] (S T U : Finset α)
    (hs : S ⊆ U) (ht : T ⊆ U) (hd : Disjoint S T) (hu : U=S∪T) :
    (U → A) ≃ (S → A) × (T → A) where
  toFun x := (fun i => x ⟨i.val,hs i.property⟩,fun i => x ⟨i.val,ht i.property⟩)
  invFun x i := if hi : i.val∈S then x.1 ⟨i.val,hi⟩ else x.2 ⟨i.val,by
    have hm : i.val∈S∪T := hu ▸ i.property; exact (mem_union.mp hm).resolve_left hi⟩
  left_inv x := by funext i; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i; simp [i.property]
    · funext i
      have hn : i.val∉S := by exact fun h => (disjoint_left.mp hd h i.property)
      simp [hn]

theorem average_cover_mul {α : Type} [DecidableEq α] (q : ℕ) (hq : 0<q)
    (S T U : Finset α) (hs : S ⊆ U) (ht : T ⊆ U) (hd : Disjoint S T) (hu : U=S∪T)
    (f : (S → Fin q) → ℚ) (g : (T → Fin q) → ℚ) :
    (∑ x : U → Fin q, f (fun i => x ⟨i.val,hs i.property⟩) *
      g (fun i => x ⟨i.val,ht i.property⟩)) / (q : ℚ)^U.card =
      ((∑ x, f x)/(q : ℚ)^S.card) * ((∑ y, g y)/(q : ℚ)^T.card) := by
  have he : (∑ x : U → Fin q, f (fun i => x ⟨i.val,hs i.property⟩) *
      g (fun i => x ⟨i.val,ht i.property⟩)) = (∑ x, f x)*(∑ y,g y) := by
    calc
      _ = ∑ z : (S → Fin q) × (T → Fin q), f z.1*g z.2 :=
        Fintype.sum_equiv (splitCoverPatterns S T U hs ht hd hu) _ _ (fun _ => rfl)
      _ = _ := by rw [Fintype.sum_prod_type]; simp_rw [sum_mul,mul_sum]
  rw [he,hu,card_union_of_disjoint hd,pow_add,div_mul_div_comm]

theorem inputSupport_union (F : CA) (S T : Finset Lattice) :
    inputSupport F (S∪T)=inputSupport F S∪inputSupport F T := by
  simp only [inputSupport,union_biUnion]

theorem disjoint_outputs_of_inputs (F : CA) (S T : Finset Lattice)
    (hd : Disjoint (inputSupport F S) (inputSupport F T)) : Disjoint S T := by
  obtain ⟨n,hn⟩ := F.neighborhood_nonempty
  apply disjoint_left.mpr
  intro i hs ht
  exact disjoint_left.mp hd
    (mem_biUnion.mpr ⟨i,hs,mem_image.mpr ⟨n,hn,rfl⟩⟩ : i+n∈inputSupport F S)
    (mem_biUnion.mpr ⟨i,ht,mem_image.mpr ⟨n,hn,rfl⟩⟩)

theorem outputLaw_independent (F : CA) (S T : Finset Lattice)
    (hd : Disjoint (inputSupport F S) (inputSupport F T))
    (f : (S → Fin F.q) → ℚ) (g : (T → Fin F.q) → ℚ) :
    (∑ b, outputLaw F (S∪T) b *
      (f (fun i => b ⟨i.val,mem_union_left T i.property⟩) *
       g (fun i => b ⟨i.val,mem_union_right S i.property⟩))) =
      (∑ a, outputLaw F S a*f a) * (∑ b, outputLaw F T b*g b) := by
  rw [outputLaw_expect,outputLaw_expect,outputLaw_expect]
  simp_rw [blockMap_restrict F S (S∪T) (subset_union_left),
    blockMap_restrict F T (S∪T) (subset_union_right)]
  exact average_cover_mul F.q (by have := F.two_le; omega) _ _ _
    (inputSupport_mono F subset_union_left) (inputSupport_mono F subset_union_right)
    hd (inputSupport_union F S T) (fun x => f (blockMap F S x)) (fun y => g (blockMap F T y))

theorem outputLaw_factorization (F : CA) (S T : Finset Lattice)
    (hd : Disjoint (inputSupport F S) (inputSupport F T)) (a : ↥(S∪T) → Fin F.q) :
    outputLaw F (S∪T) a =
      outputLaw F S (fun i => a ⟨i.val,mem_union_left T i.property⟩) *
      outputLaw F T (fun i => a ⟨i.val,mem_union_right S i.property⟩) := by
  have hi := outputLaw_independent F S T hd
    (fun x => if x=(fun i : S => a ⟨i.val,mem_union_left T i.property⟩) then 1 else 0)
    (fun y => if y=(fun i : T => a ⟨i.val,mem_union_right S i.property⟩) then 1 else 0)
  have he (b : ↥(S∪T) → Fin F.q) :
      ((if (fun i : S => b ⟨i.val,mem_union_left T i.property⟩)=
          (fun i : S => a ⟨i.val,mem_union_left T i.property⟩) then (1 : ℚ) else 0) *
       (if (fun i : T => b ⟨i.val,mem_union_right S i.property⟩)=
          (fun i : T => a ⟨i.val,mem_union_right S i.property⟩) then (1 : ℚ) else 0)) =
        if b=a then 1 else 0 := by
    have hh : b=a ↔
        (fun i : S => b ⟨i.val,mem_union_left T i.property⟩)=
          (fun i : S => a ⟨i.val,mem_union_left T i.property⟩) ∧
        (fun i : T => b ⟨i.val,mem_union_right S i.property⟩)=
          (fun i : T => a ⟨i.val,mem_union_right S i.property⟩) := by
      constructor
      · intro h; subst b; exact ⟨rfl,rfl⟩
      · rintro ⟨hs,ht⟩
        funext i
        rcases mem_union.mp i.property with h|h
        · exact congrFun hs ⟨i.val,h⟩
        · exact congrFun ht ⟨i.val,h⟩
    simp_rw [hh]
    split_ifs <;> simp_all
  simp_rw [he] at hi
  simpa using hi

theorem sum_two_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → B → ℚ) :
    (∑ x, ∑ y, f (e x) (e y)) = ∑ x, ∑ y, f x y := by
  calc
    _ = ∑ x, ∑ y, f (e x) y := by
      apply sum_congr rfl
      intro x _
      exact e.sum_comp (f (e x))
    _ = _ := e.sum_comp (fun x => ∑ y, f x y)

/-- Collision factorization over disjoint padded input supports. -/
theorem coefficient_factorization (F : CA) (S T : Finset Lattice)
    (hd : Disjoint (inputSupport F S) (inputSupport F T)) :
    c F (S∪T)=c F S*c F T := by
  let e := splitCoverPatterns S T (S∪T) subset_union_left subset_union_right
    (disjoint_outputs_of_inputs F S T hd) rfl (A := Fin F.q)
  have hp (x y : ↥(S∪T) → Fin F.q) :
      (∏ i : ↥(S∪T), h F.q (x i) (y i)) =
        (∏ i : S, h F.q ((e x).1 i) ((e y).1 i)) *
        (∏ i : T, h F.q ((e x).2 i) ((e y).2 i)) := by
    let H := fun i => h F.q (extendPattern F (S∪T) x i) (extendPattern F (S∪T) y i)
    have hx : (∏ i : ↥(S∪T), h F.q (x i) (y i)) = ∏ i ∈ S∪T, H i := by
      calc
        _ = ∏ i : ↥(S∪T), H i.val := by simp only [H,extendPattern_on]
        _ = _ := prod_coe_sort (S∪T) H
    rw [hx,prod_union (disjoint_outputs_of_inputs F S T hd)]
    congr 1
    · rw [← prod_coe_sort S H]
      apply prod_congr rfl
      intro i _
      simp [H,extendPattern,subset_union_left i.property,e,splitCoverPatterns]
    · rw [← prod_coe_sort T H]
      apply prod_congr rfl
      intro i _
      simp [H,extendPattern,subset_union_right i.property,e,splitCoverPatterns]
  unfold c collision
  simp_rw [hp,outputLaw_factorization F S T hd]
  have he (x : ↥(S∪T) → Fin F.q) :
      outputLaw F S (fun i => x ⟨i.val,mem_union_left T i.property⟩)=outputLaw F S (e x).1 := rfl
  have he' (x : ↥(S∪T) → Fin F.q) :
      outputLaw F T (fun i => x ⟨i.val,mem_union_right S i.property⟩)=outputLaw F T (e x).2 := rfl
  simp_rw [he,he']
  rw [sum_two_equiv e (fun x y =>
    outputLaw F S x.1 * outputLaw F T x.2 * (outputLaw F S y.1 * outputLaw F T y.2) *
      ((∏i,h F.q (x.1 i) (y.1 i)) * ∏i,h F.q (x.2 i) (y.2 i)))]
  simp_rw [Fintype.sum_prod_type]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  -- Separate the two independent replica pairs.
  simp_rw [sum_mul,mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring

end
end Thermal
