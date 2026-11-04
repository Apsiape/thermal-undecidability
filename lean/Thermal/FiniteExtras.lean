import Thermal.WitnessSearch
import Thermal.TableProof
import Thermal.TableEnumeration
import Thermal.TableCoding
import Thermal.PositiveExpansion
namespace Thermal
open Finset
noncomputable section
def D (F : CA) (P : Finset Lattice) : Finset Lattice :=
  P.biUnion (fun i => F.N.biUnion (fun n => F.N.image (fun n' => i+n-n')))
theorem coefficient_empty (F : CA) : c F ∅=1 := coefficient_empty_closed F

theorem coefficient_upper (F : CA) (T : Finset Lattice) : c F T ≤ ((F.q : ℚ)-1)^T.card := coefficient_upper_closed F T

/-- Stronger complete finite table enumeration, not just one sample per index. -/
theorem overlap_card (F : CA) (P : Finset Lattice) : (D F P).card ≤ F.N.card^2*P.card := by
  unfold D
  calc
    _ ≤ P.card*(F.N.card*F.N.card) := by
      apply card_biUnion_le_card_mul
      intro i hi
      exact card_biUnion_le_card_mul _ _ _ (fun _ _ => card_image_le)
    _ = _ := by ring

theorem positive_model (F : CA) (Q : ℕ) (M : Model F Q)
    (he : 0≤M.ε ∧ M.ε<1) (ho : ∀ r, 0≤M.openWeight r)
    (hc : ∀ r, 0<M.closedScale r) : ∀ ξ e, 0<localWeight M ξ e := local_weight_positive M he ho hc

end
end Thermal
