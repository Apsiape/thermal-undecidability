import Thermal.CoefficientAlgorithm
namespace Thermal.Algorithm
open Primrec

def shiftList (p : ℕ × List ℕ) : List ℕ := p.2.map (fun n => p.1+n+1)

theorem prim_shiftList : Primrec shiftList :=
  Primrec.list_map Primrec.snd
    (Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

def raiseBase (l : List ℕ) : List ℕ :=
  l.foldr (fun m xs => m :: shiftList (m,xs)) []

theorem prim_raiseBase : Primrec raiseBase :=
  Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (prim_shiftList.comp Primrec.snd)).to₂

/-- The canonical finite-set enumeration, in increasing encoding order. -/
def candidateList (n : ℕ) : List Point :=
  (raiseBase (Denumerable.ofNat (List ℕ) n)).map (Denumerable.ofNat Point)

theorem prim_candidateList : Primrec candidateList :=
  Primrec.list_map (prim_raiseBase.comp (Primrec.ofNat (List ℕ)))
    ((Primrec.ofNat Point).comp Primrec.snd).to₂

/-- Binary masks enumerate all subsets of a duplicate-free candidate list. -/
def maskSubset (p : List Point × ℕ) : List Point :=
  p.1.filter (fun i => p.2/2^(p.1.idxOf i)%2=1)

theorem prim_maskSubset : Primrec maskSubset := by
  have hp : PrimrecRel (fun (i : Point) (p : List Point × ℕ) => p.2/2^(p.1.idxOf i)%2=1) :=
    Primrec.eq.comp (Primrec.nat_mod.comp
      (Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd)
        (prim_pow.comp (Primrec.const 2)
          (Primrec.list_idxOf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))))
      (Primrec.const 2)) (Primrec.const 1)
  exact hp.listFilter.comp Primrec.fst Primrec.id

def smallerPositive (m : ℕ) (p : FiniteInput) : Prop :=
  0<(maskSubset (p.2,m)).length ∧ (maskSubset (p.2,m)).length<p.2.length ∧
    0<finiteNumerator (p.1,maskSubset (p.2,m))

theorem prim_smallerPositive : PrimrecRel smallerPositive := by
  have hsub : Primrec (fun p : ℕ × FiniteInput => maskSubset (p.2.2,p.1)) :=
    prim_maskSubset.comp ((Primrec.snd.comp Primrec.snd).pair Primrec.fst)
  have hl := Primrec.list_length.comp hsub
  exact (Primrec.nat_lt.comp (Primrec.const 0) hl).and
    ((Primrec.nat_lt.comp hl (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))).and
      ((prim_intPositive.comp (prim_finiteNumerator.comp
        ((Primrec.fst.comp Primrec.snd).pair hsub))).primrecPred))

def MinimalPositive (p : FiniteInput) : Prop :=
  0<p.2.length ∧ 0<finiteNumerator p ∧
    ∀ m∈List.range (2^p.2.length),¬smallerPositive m p

instance (p : FiniteInput) : Decidable (MinimalPositive p) := by
  unfold MinimalPositive smallerPositive
  infer_instance

theorem prim_minimalPositive : PrimrecPred MinimalPositive :=
  (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp Primrec.snd)).and
    (((prim_intPositive.comp prim_finiteNumerator).primrecPred).and
      (prim_smallerPositive.not.forall_mem_list.comp
        (Primrec.list_range.comp (prim_pow.comp (Primrec.const 2)
          (Primrec.list_length.comp Primrec.snd))) Primrec.id))

/-- A stage is total: test one finite candidate exhaustively, then return it or none. -/
def searchProgram (p : Code × ℕ) : Option (Finset Point) :=
  if MinimalPositive (p.1,candidateList p.2)
    then some (Denumerable.ofNat (Finset Point) p.2) else none

theorem prim_searchProgram : Primrec searchProgram :=
  Primrec.ite (prim_minimalPositive.comp
    (Primrec.fst.pair (prim_candidateList.comp Primrec.snd)))
    (Primrec.option_some.comp ((Primrec.ofNat (Finset Point)).comp Primrec.snd))
    (Primrec.const none)

end Thermal.Algorithm

