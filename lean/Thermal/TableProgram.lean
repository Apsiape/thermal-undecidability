import Thermal.TableAlgorithm
import Mathlib.Data.Fintype.Prod
namespace Thermal.Algorithm
open Primrec

def visibleDigit (p : (ℕ × ℕ) × (ℕ × Point)) : ℕ :=
  (p.2.1 / (p.1.2*p.1.1^4)^(Encodable.encode p.2.2)) % p.1.2

theorem prim_visibleDigit : Primrec visibleDigit :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
      (prim_pow.comp
        (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
          (prim_pow.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4)))
        (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp Primrec.fst)

def tagQ (t : Fin 3) : ℕ := if t=0 then 2 else if t=1 then 9 else 66049
def tagV (t : Fin 3) (r : Bool) : ℕ := if t=0 then (if r then 1 else 2)
  else if t=1 then 3 else 257
def tagK (t : Fin 3) (r : Bool) : ℕ := if t=0 then (if r then 2 else 3) else 1

def direction (r : Bool) : Point := if r then (0,1) else (1,0)
def layer (r : Bool) : ℕ := if r then 2 else 0
abbrev TableInput := Code × (Fin 3 × ℕ)

def phase (p : TableInput) : Bool := decide (p.2.2%2=1)

theorem prim_phase : Primrec phase :=
  (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.const 2)) (Primrec.const 1)).decide

def tableDenom (p : TableInput) : ℕ :=
  if p.2.1=2 then uniqueDenominator p.1 else denominator p.1

theorem prim_tableDenom : Primrec tableDenom :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
    (prim_uniqueDenominator.comp Primrec.fst) (prim_denominator.comp Primrec.fst)

def tableSame (p : TableInput) : Bool := decide
  (visibleDigit ((qValue p.1,tagQ p.2.1),(p.2.2/2,0)) =
   visibleDigit ((qValue p.1,tagQ p.2.1),(p.2.2/2,direction (phase p))))

theorem prim_tableSame : Primrec tableSame := by
  have hq : Primrec (fun p : TableInput => qValue p.1) := prim_qValue.comp Primrec.fst
  have hQ : Primrec (fun p : TableInput => tagQ p.2.1) :=
    (Primrec.dom_finite tagQ).comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : TableInput => p.2.2/2) :=
    Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
  exact (Primrec.eq.comp
    (prim_visibleDigit.comp ((hq.pair hQ).pair (hn.pair (Primrec.const 0))))
    (prim_visibleDigit.comp ((hq.pair hQ).pair
      (hn.pair ((Primrec.dom_finite direction).comp prim_phase))))).decide

def tableRuleSame (p : TableInput) : Bool := decide
  (ruleDigit (p.1,(tagQ p.2.1,(p.2.2/2,layer (phase p)))) =
    ruleDigit (p.1,(tagQ p.2.1,(p.2.2/2,layer (phase p)+1))))

theorem prim_tableRuleSame : Primrec tableRuleSame := by
  have hQ : Primrec (fun p : TableInput => tagQ p.2.1) :=
    (Primrec.dom_finite tagQ).comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : TableInput => p.2.2/2) :=
    Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
  have hl : Primrec (fun p : TableInput => layer (phase p)) :=
    (Primrec.dom_finite layer).comp prim_phase
  exact (Primrec.eq.comp
    (prim_ruleDigit.comp (Primrec.fst.pair (hQ.pair (hn.pair hl))))
    (prim_ruleDigit.comp (Primrec.fst.pair
      (hQ.pair (hn.pair (Primrec.succ.comp hl)))))).decide

/-- Uniform total rational table program, including all tags and indices. -/
def tableProgram (p : TableInput) : ℤ × ℕ :=
  fraction ((qValue p.1,tableDenom p),
    (tagV p.2.1 (phase p),(tagK p.2.1 (phase p),(tableSame p,tableRuleSame p))))

theorem prim_tableProgram : Primrec tableProgram := by
  have hv : Primrec (fun p : TableInput => tagV p.2.1 (phase p)) :=
    (Primrec.dom_finite (fun p : Fin 3 × Bool => tagV p.1 p.2)).comp
      ((Primrec.fst.comp Primrec.snd).pair prim_phase)
  have hk : Primrec (fun p : TableInput => tagK p.2.1 (phase p)) :=
    (Primrec.dom_finite (fun p : Fin 3 × Bool => tagK p.1 p.2)).comp
      ((Primrec.fst.comp Primrec.snd).pair prim_phase)
  exact prim_fraction.comp
    (((prim_qValue.comp Primrec.fst).pair prim_tableDenom).pair
      (hv.pair (hk.pair (prim_tableSame.pair prim_tableRuleSame))))

end Thermal.Algorithm


