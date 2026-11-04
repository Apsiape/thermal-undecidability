import Thermal.RuleCoding
import Thermal.DigitCoding

namespace Thermal
noncomputable section

theorem table_coding_complete (F : CA) (Q : ℕ) (hQ : 0<Q) (r : Bool) (ξ : Config F.q Q) :
    ∃ n, ∀ i∈support F r, codedConfig F Q hQ n i=ξ i := by
  have hq : 0<F.q := by have := F.two_le; omega
  obtain ⟨n,hn⟩ := finite_digit_coding_complete F.q Q hq hQ (support F r) ξ
  refine ⟨n,fun i hi => ?_⟩
  simpa only [codedConfig,decodeSite] using hn i hi

end
end Thermal
