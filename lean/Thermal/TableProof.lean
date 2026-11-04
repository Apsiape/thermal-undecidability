import Thermal.TableCorrect
namespace Thermal
open Algorithm
noncomputable section
attribute [local instance] Classical.propDecidable

theorem fraction_localWeight (a : RuleCode) (Q : ℕ) (hQ : 0<Q)
    (n : ℕ) (r : Bool) (D v k : ℕ) (hD : 0<D) (hk : 0<k) :
    ratDecode (fraction ((qValue a,D),(v,(k,
      (decide (visibleDigit ((qValue a,Q),(n,0)) =
        visibleDigit ((qValue a,Q),(n,direction r))),
       decide (ruleDigit (a,(Q,(n,layer r))) =
        ruleDigit (a,(Q,(n,layer r+1))))))))) =
    localWeight (⟨1/(D : ℚ),fun _ => (v : ℚ)/k,fun _ => 1/(k : ℚ)⟩ : Model (decodeRule a) Q)
      (codedConfig (decodeRule a) Q hQ n) (0,r) := by
  rw [fraction_correct _ _ _ _ hD hk]
  cases r
  · simp only [layer,Bool.false_eq_true,ite_false,zero_add]
    rw [ruleDigit_correct a Q hQ n ⟨0,by decide⟩,ruleDigit_correct a Q hQ n ⟨1,by decide⟩]
    simp [localWeight,hiddenWeight,w,h,CA.global,replica,step,direction,
      visibleDigit,codedConfig,qValue,decodeRule,Fin.ext_iff]
  · simp only [layer,ite_true]
    rw [ruleDigit_correct a Q hQ n ⟨2,by decide⟩,ruleDigit_correct a Q hQ n ⟨3,by decide⟩]
    simp [localWeight,hiddenWeight,w,h,CA.global,replica,step,direction,
      visibleDigit,codedConfig,qValue,decodeRule,Fin.ext_iff]

theorem tableProgram_correct (a : RuleCode) (tag : Fin 3) (n : ℕ) :
    ratDecode (tableProgram (a,(tag,n))) = tableValue a tag n := by
  have hDu : 0 < uniqueDenominator a :=
    lt_of_lt_of_le (denominator_pos a) (Nat.le_max_left _ _)
  fin_cases tag
  all_goals
    simp [tableValue,tableProgram,tableDenom,tagQ,tagV,tagK,tableSame,tableRuleSame,phase]
    rw [fraction_localWeight a _ (by omega) (n/2) _ _ _ _
      (by first | exact denominator_pos a | exact hDu) (by first | omega | (split_ifs <;> omega))]
    simp [localWeight,hiddenWeight,ising,magnetic,uniqueModel,potts,algorithm_epsilon,algorithm_epsilonU]
    all_goals split_ifs <;> norm_num

theorem weight_table_computable : ∃ A : RuleCode × (Fin 3 × ℕ) → RatCode, Computable A ∧
  ∀ code tag n, ratDecode (A (code,tag,n))=tableValue code tag n := by
  exact ⟨Algorithm.tableProgram,Algorithm.prim_tableProgram.to_comp,tableProgram_correct⟩

end
end Thermal



