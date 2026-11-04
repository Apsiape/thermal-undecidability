import Thermal.Definitions
namespace Thermal
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Explicit input coding; a leading origin permits every finite rule to be padded. -/
abbrev RuleCode := ℕ × (List Lattice × List ℕ)
def decodeRule (a : RuleCode) : CA where
  q := a.1+2
  two_le := by omega
  N := (0 :: a.2.1).toFinset
  neighborhood_nonempty := by simp
  rule := fun x => Fin.ofNat (a.1+2) ((a.2.2[(0 :: a.2.1).attach.foldl
    (fun acc n => acc*(a.1+2)+(x ⟨n.val,List.mem_toFinset.mpr n.property⟩).val) 0]?).getD 0)

def enumerateCA (n : ℕ) : CA := decodeRule ((Encodable.decode (α := RuleCode) n).getD (0,[],[]))
def codedConfig (F : CA) (Q : ℕ) (hq : 0<Q) (n : ℕ) : Config F.q Q := by
  letI : NeZero Q := ⟨by omega⟩
  letI : NeZero F.q := ⟨by have := F.two_le; omega⟩
  exact fun i =>
    let digit := n / (Q*F.q^4)^(Encodable.encode i)
    (Fin.ofNat Q digit, fun r => Fin.ofNat F.q (digit/Q/F.q^r.val))

def tableValue (code : RuleCode) (tag : Fin 3) (n : ℕ) : ℚ :=
  let F := decodeRule code
  let r := decide (n%2=1)
  if tag=0 then localWeight (ising F) (codedConfig F 2 (by omega) (n/2)) (0,r)
  else if tag=1 then localWeight (magnetic F) (codedConfig F 9 (by omega) (n/2)) (0,r)
  else localWeight (uniqueModel F) (codedConfig F 66049 (by omega) (n/2)) (0,r)


end
end Thermal
