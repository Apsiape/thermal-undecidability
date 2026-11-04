import Thermal.RuleEvaluator

namespace Thermal.Algorithm
open Primrec
variable {α β : Type} [Primcodable α] [Primcodable β]

theorem prim_mem [DecidableEq α] : PrimrecRel (fun (a : α) (l : List α) => a∈l) := by
  exact ((PrimrecRel.exists_mem_list (Primrec.eq (α := α))).of_eq
    (fun l a => by simp)).swap

theorem prim_dedup [DecidableEq α] : Primrec (@List.dedup α _) := by
  have hp : Primrec (fun l : List α => l.foldr
      (fun x xs => if x∈xs then xs else x::xs) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.ite (prim_mem.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂
  refine hp.of_eq (fun l => ?_)
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons,ih,List.dedup_cons',List.mem_dedup]

/-- The maximum of a finite list, with zero as the empty maximum. -/
def maximum (l : List ℕ) : ℕ := l.foldr max 0

theorem prim_maximum : Primrec maximum :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

def distance (i j : Point) : ℕ :=
  (i.1-j.1).natAbs+(i.2-j.2).natAbs

theorem prim_distance : Primrec₂ distance :=
  (Primrec.nat_add.comp
    (prim_natAbs.comp (prim_intSub.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)))
    (prim_natAbs.comp (prim_intSub.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)))).to₂

def diameter (l : List Point) : ℕ :=
  maximum (l.map (fun i => maximum (l.map (distance i))))

theorem prim_diameter : Primrec diameter := by
  apply prim_maximum.comp
  refine Primrec.list_map Primrec.id ?_
  change Primrec (fun p : List Point × Point => maximum (p.1.map (distance p.2)))
  apply prim_maximum.comp
  exact Primrec.list_map Primrec.fst
    (prim_distance.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

def neighborhood (a : Code) : List Point := 0::a.2.1

theorem prim_neighborhood : Primrec neighborhood :=
  Primrec.list_cons.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)

def qValue (a : Code) : ℕ := a.1+2

theorem prim_qValue : Primrec qValue :=
  Primrec.nat_add.comp Primrec.fst (Primrec.const 2)

/-- A digit in the four replicas, at an encoded lattice site. -/
def inputDigit (p : (ℕ × ℕ) × (ℕ × (Point × ℕ))) : ℕ :=
  (p.2.1 / (p.1.2*p.1.1^4)^(Encodable.encode p.2.2.1) /
    p.1.2 / p.1.1^p.2.2.2) % p.1.1

theorem prim_inputDigit : Primrec inputDigit := by
  unfold inputDigit
  apply Primrec.nat_mod.comp _ (Primrec.fst.comp Primrec.fst)
  apply Primrec.nat_div.comp _ (prim_pow.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  apply Primrec.nat_div.comp _ (Primrec.snd.comp Primrec.fst)
  exact Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
    (prim_pow.comp
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
        (prim_pow.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4)))
      (Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))

/-- One shared local-rule evaluation; symbols are in the original neighborhood-list order. -/
def ruleDigit (p : Code × (ℕ × (ℕ × ℕ))) : ℕ :=
  evalLocal (qValue p.1) p.1.2.2
    ((neighborhood p.1).map (fun i => inputDigit
      ((qValue p.1,p.2.1),(p.2.2.1,(i,p.2.2.2)))))

theorem prim_ruleDigit : Primrec ruleDigit := by
  unfold ruleDigit
  refine prim_evalLocal.comp (g := fun p : Code × (ℕ × (ℕ × ℕ)) =>
    (qValue p.1,(p.1.2.2,(neighborhood p.1).map (fun i => inputDigit
      ((qValue p.1,p.2.1),(p.2.2.1,(i,p.2.2.2))))))) ?_
  apply Primrec.pair (prim_qValue.comp Primrec.fst)
  apply Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  refine Primrec.list_map (prim_neighborhood.comp Primrec.fst) ?_
  change Primrec (fun p : (Code × (ℕ × (ℕ × ℕ))) × Point =>
    inputDigit ((qValue p.1.1,p.1.2.1),(p.1.2.2.1,(p.2,p.1.2.2.2))))
  apply prim_inputDigit.comp
  exact Primrec.pair
    (Primrec.pair (prim_qValue.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))

/-- Cardinality uses deduplication, while rule evaluation retains repeated input positions. -/
def ncard (a : Code) : ℕ := (neighborhood a).dedup.length

theorem prim_ncard : Primrec ncard :=
  Primrec.list_length.comp (prim_dedup.comp prim_neighborhood)

def ruleRadius (a : Code) : ℕ := max
  (diameter (neighborhood a ++ [0,(1,0)]))
  (diameter (neighborhood a ++ [0,(0,1)]))

theorem prim_ruleRadius : Primrec ruleRadius :=
  Primrec.nat_max.comp
    (prim_diameter.comp (Primrec.list_append.comp prim_neighborhood (Primrec.const _)))
    (prim_diameter.comp (Primrec.list_append.comp prim_neighborhood (Primrec.const _)))

def denominator (a : Code) : ℕ := 100*qValue a*(ncard a+1)^2

theorem prim_denominator : Primrec denominator :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 100) prim_qValue)
    (prim_pow.comp (Primrec.succ.comp prim_ncard) (Primrec.const 2))

def uniqueDenominator (a : Code) : ℕ := max (denominator a)
  (16*qValue a*(ncard a+2)*2^(ruleRadius a))

theorem prim_uniqueDenominator : Primrec uniqueDenominator :=
  Primrec.nat_max.comp prim_denominator
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 16) prim_qValue)
        (Primrec.nat_add.comp prim_ncard (Primrec.const 2)))
      (prim_pow.comp (Primrec.const 2) prim_ruleRadius))

/-- Unreduced positive-denominator rational arithmetic, with no normalization algorithm hidden. -/
def fraction (p : (ℕ × ℕ) × (ℕ × (ℕ × (Bool × Bool)))) : ℤ × ℕ :=
  (((p.2.1*(bif p.2.2.2.1 then 1 else 0)*p.1.2^2 +
    (p.1.2^2-1+(bif p.2.2.2.2 then p.1.1 else 0)) : ℕ) : ℤ),p.2.2.1*p.1.2^2-1)

theorem prim_fraction : Primrec fraction := by
  unfold fraction
  apply Primrec.pair
  · apply prim_natCast.comp
    apply Primrec.nat_add.comp
    · exact Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.const 1) (Primrec.const 0)))
        (prim_pow.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2))
    · exact Primrec.nat_add.comp
        (Primrec.nat_sub.comp (prim_pow.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2))
          (Primrec.const 1))
        (Primrec.cond (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
  · exact Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (prim_pow.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2))) (Primrec.const 1)

end Thermal.Algorithm


