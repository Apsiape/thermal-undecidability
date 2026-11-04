import Thermal.TableAlgorithm
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Basic
namespace Thermal.Algorithm
open Primrec

theorem prim_intSign : Primrec (fun z : ℤ => decide (z<0)) := by
  have hf := (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.encode (α := ℤ))
    (Primrec.const 2)) (Primrec.const 1)).decide
  refine hf.of_eq (fun z => ?_)
  apply decide_eq_decide.mpr
  cases z with
  | ofNat n => change (2*n%2=1) ↔ (n : ℤ)<0; omega
  | negSucc n => change ((2*n+1)%2=1) ↔ Int.negSucc n<0; omega

theorem prim_intPositive : Primrec (fun z : ℤ => decide (0<z)) := by
  have hf := ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.encode (α := ℤ))
    (Primrec.const 2)) (Primrec.const 0)).and
    (Primrec.nat_lt.comp (Primrec.const 0) Primrec.encode)).decide
  refine hf.of_eq (fun z => ?_)
  apply decide_eq_decide.mpr
  cases z with
  | ofNat n => change (2*n%2=0 ∧ 0<2*n) ↔ 0<(n : ℤ); omega
  | negSucc n => change ((2*n+1)%2=0 ∧ 0<2*n+1) ↔ 0<Int.negSucc n; omega
theorem prim_intMul : Primrec₂ (fun a b : ℤ => a*b) := by
  have hm : Primrec (fun p : ℤ × ℤ => ((p.1.natAbs*p.2.natAbs : ℕ) : ℤ)) :=
    prim_natCast.comp (Primrec.nat_mul.comp (prim_natAbs.comp Primrec.fst)
      (prim_natAbs.comp Primrec.snd))
  have hs := (Primrec.eq.comp (prim_intSign.comp (Primrec.fst (α := ℤ) (β := ℤ)))
    (prim_intSign.comp Primrec.snd)).decide
  refine (Primrec.cond hs hm (prim_neg.comp hm)).of_eq ?_
  rintro ⟨a,b⟩
  have hp (n : ℕ) : ¬Int.ofNat n<0 := by change ¬(n : ℤ)<0; omega
  have hn (n : ℕ) : Int.negSucc n<0 := by omega
  cases a <;> cases b <;> simp only [hp,hn,decide_true,decide_false]
  all_goals simp only [Bool.cond_true,Bool.cond_false,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,decide_true,decide_false,Int.natAbs_negSucc]
  all_goals simp [Int.negSucc_eq,Nat.cast_mul] <;> ring
theorem prim_pointAdd : Primrec₂ (fun a b : Point => a+b) :=
  (Primrec.pair (prim_intAdd.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (prim_intAdd.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

/-- Base-q input assignment digit on a finite, deduplicated support list. -/
def assignmentDigit (p : (ℕ × List Point) × (ℕ × Point)) : ℕ :=
  (p.2.1 / p.1.1^(p.1.2.idxOf p.2.2)) % p.1.1

theorem prim_assignmentDigit : Primrec assignmentDigit :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
      (prim_pow.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))))
    (Primrec.fst.comp Primrec.fst)

abbrev AtInput := Code × (List Point × (ℕ × Point))

def evalAt (p : AtInput) : ℕ :=
  evalLocal (qValue p.1) p.1.2.2 ((neighborhood p.1).map (fun j =>
    assignmentDigit ((qValue p.1,p.2.1),(p.2.2.1,p.2.2.2+j))))

theorem prim_evalAt : Primrec evalAt := by
  have hs : Primrec (fun p : AtInput => (neighborhood p.1).map (fun j =>
      assignmentDigit ((qValue p.1,p.2.1),(p.2.2.1,p.2.2.2+j)))) := by
    refine Primrec.list_map (prim_neighborhood.comp Primrec.fst) ?_
    change Primrec (fun p : AtInput × Point => assignmentDigit
      ((qValue p.1.1,p.1.2.1),(p.1.2.2.1,p.1.2.2.2+p.2)))
    exact prim_assignmentDigit.comp
      (((prim_qValue.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          (prim_pointAdd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)))
  exact prim_evalLocal.comp (((prim_qValue.comp Primrec.fst)).pair
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair hs))

abbrev FiniteInput := Code × List Point

def inputList (p : FiniteInput) : List Point :=
  (p.2.flatMap (fun i => (neighborhood p.1).map (fun j => i+j))).dedup

theorem prim_inputList : Primrec inputList := by
  apply prim_dedup.comp
  refine Primrec.list_flatMap Primrec.snd ?_
  change Primrec (fun p : FiniteInput × Point => (neighborhood p.1.1).map (fun j => p.2+j))
  exact Primrec.list_map (prim_neighborhood.comp (Primrec.fst.comp Primrec.fst))
    (prim_pointAdd.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

def intKernel (q a b : ℕ) : ℤ := if a=b then ((q : ℤ)-1) else -1

theorem prim_intKernel : Primrec (fun p : ℕ × (ℕ × ℕ) => intKernel p.1 p.2.1 p.2.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (prim_intSub.comp (prim_natCast.comp Primrec.fst) (Primrec.const 1)) (Primrec.const (-1))

abbrev PairInput := FiniteInput × (ℕ × ℕ)

def pairTerm (p : PairInput) : ℤ :=
  (p.1.2.map (fun i => intKernel (qValue p.1.1)
    (evalAt (p.1.1,(inputList p.1,(p.2.1,i))))
    (evalAt (p.1.1,(inputList p.1,(p.2.2,i)))))).foldr (·*·) 1

theorem prim_pairTerm : Primrec pairTerm := by
  have ht : Primrec (fun p : PairInput => p.1.2.map (fun i => intKernel (qValue p.1.1)
      (evalAt (p.1.1,(inputList p.1,(p.2.1,i))))
      (evalAt (p.1.1,(inputList p.1,(p.2.2,i)))))) := by
    refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
    change Primrec (fun p : PairInput × Point => intKernel (qValue p.1.1.1)
      (evalAt (p.1.1.1,(inputList p.1.1,(p.1.2.1,p.2))))
      (evalAt (p.1.1.1,(inputList p.1.1,(p.1.2.2,p.2)))))
    exact prim_intKernel.comp
      ((prim_qValue.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        ((prim_evalAt.comp
          ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
            ((prim_inputList.comp (Primrec.fst.comp Primrec.fst)).pair
              ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)))).pair
          (prim_evalAt.comp
            ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
              ((prim_inputList.comp (Primrec.fst.comp Primrec.fst)).pair
                ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))))))
  exact Primrec.list_foldr ht (Primrec.const 1)
    (prim_intMul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

def assignmentCount (p : FiniteInput) : ℕ := qValue p.1^(inputList p).length

theorem prim_assignmentCount : Primrec assignmentCount :=
  prim_pow.comp (prim_qValue.comp Primrec.fst) (Primrec.list_length.comp prim_inputList)

/-- Exact integer numerator from exhaustive pairs of finite input assignments. -/
def finiteNumerator (p : FiniteInput) : ℤ :=
  ((List.range (assignmentCount p)).map (fun n =>
    ((List.range (assignmentCount p)).map (fun m => pairTerm (p,(n,m)))).foldr (·+·) 0)).foldr (·+·) 0

theorem prim_finiteNumerator : Primrec finiteNumerator := by
  have hsum : Primrec (fun p : FiniteInput × ℕ =>
      ((List.range (assignmentCount p.1)).map (fun m => pairTerm (p.1,(p.2,m)))).foldr (·+·) 0) := by
    refine Primrec.list_foldr (Primrec.list_map
      (Primrec.list_range.comp (prim_assignmentCount.comp Primrec.fst)) ?_)
      (Primrec.const 0) (prim_intAdd.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
    exact (prim_pairTerm.comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact Primrec.list_foldr (Primrec.list_map (Primrec.list_range.comp prim_assignmentCount) hsum.to₂)
    (Primrec.const 0) (prim_intAdd.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

end Thermal.Algorithm






