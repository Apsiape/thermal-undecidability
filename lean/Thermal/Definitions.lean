import Thermal.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.RecursiveIn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Thermal
open Finset MeasureTheory Filter
noncomputable section
variable {q Q : ℕ} {F : CA}

/-- Exactly T+N, using iid inputs on this padded set, never a periodic torus. -/
def inputSupport (F : CA) (T : Finset Lattice) : Finset Lattice :=
  T.biUnion (fun i => F.N.image (fun n => i+n))

def blockMap (F : CA) (T : Finset Lattice)
    (x : inputSupport F T → Fin F.q) : T → Fin F.q := fun i =>
  F.rule (fun n => x ⟨i.val+n.val, by
    simp only [inputSupport, mem_biUnion, mem_image]
    exact ⟨i.val, i.property, n.val, n.property, rfl⟩⟩)

def outputLaw (F : CA) (T : Finset Lattice) (a : T → Fin F.q) : ℚ :=
  (∑ x : inputSupport F T → Fin F.q, if blockMap F T x = a then 1 else 0) /
    (F.q : ℚ)^(inputSupport F T).card

def c (F : CA) (T : Finset Lattice) : ℚ := collision F.q (outputLaw F T)

def W (F : CA) (ε : ℚ) (C : Finset Lattice) : ℚ :=
  ∑ x, ∑ y, outputLaw F C x * outputLaw F C y * ∏ i : C, w F.q ε (x i) (y i)

def Balanced (F : CA) : Prop := ∀ T a, outputLaw F T a = 1/(F.q : ℚ)^T.card

def overlapGraph (F : CA) : SimpleGraph Lattice where
  Adj i j := i ≠ j ∧ ∃ n ∈ F.N, ∃ n' ∈ F.N, i+n = j+n'
  symm := ⟨by
    rintro i j ⟨hij,n,hn,n',hn',he⟩
    exact ⟨Ne.symm hij,n',hn',n,hn,he.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def ConnectedWitness (F : CA) (P : Finset Lattice) : Prop :=
  P.Nonempty ∧ 0 < c F P ∧ ((overlapGraph F).induce (P : Set Lattice)).Connected

abbrev Site (q Q : ℕ) := Fin Q × (Fin 4 → Fin q)
abbrev Config (q Q : ℕ) := Lattice → Site q Q
instance siteMeasurable (q Q : ℕ) : MeasurableSpace (Site q Q) := ⊤

abbrev State (q Q : ℕ) := Measure (Config q Q)
def step (r : Bool) : Lattice := if r then (0,1) else (1,0)
abbrev Edge := Lattice × Bool
abbrev Bonds := Edge → Bool

def support (F : CA) (r : Bool) : Finset Lattice := F.N ∪ {0,step r}

def replica (ξ : Config q Q) (r second : Bool) (i : Lattice) : Fin q :=
  (ξ i).2 (if r then (if second then 3 else 2) else (if second then 1 else 0))

def hiddenWeight (F : CA) (Q : ℕ) (ε : ℚ) (ξ : Config F.q Q) (e : Edge) : ℚ :=
  w F.q ε (F.global (replica ξ e.2 false) e.1) (F.global (replica ξ e.2 true) e.1)

/-- A concrete finite-range interaction: the same table at every translate. -/
structure Model (F : CA) (Q : ℕ) where
  ε : ℚ
  openWeight : Bool → ℚ
  closedScale : Bool → ℚ

def ising (F : CA) : Model F 2 :=
  ⟨epsilon F.q F.N.card, (fun r => if r then 1/2 else 2/3),
    (fun r => if r then 1/2 else 1/3)⟩

def potts (F : CA) (v : ℕ) (ε : ℚ) : Model F (v*v) := ⟨ε, fun _ => v, fun _ => 1⟩

def supportDiameter (S : Finset Lattice) : ℕ :=
  S.sup (fun i => S.sup (fun j => (i.1-j.1).natAbs + (i.2-j.2).natAbs))

def radius (F : CA) : ℕ := max (supportDiameter (support F false)) (supportDiameter (support F true))

def epsilonU (F : CA) : ℚ := min (epsilon F.q F.N.card)
  (1/(16*(F.q : ℚ)*(F.N.card+2)*2^(radius F)))

def magnetic (F : CA) : Model F 9 := potts F 3 (epsilon F.q F.N.card)
def uniqueModel (F : CA) : Model F 66049 := potts F 257 (epsilonU F)

def localWeight (M : Model F Q) (ξ : Config F.q Q) (e : Edge) : ℚ :=
  M.openWeight e.2 * (if (ξ e.1).1 = (ξ (e.1+step e.2)).1 then 1 else 0) +
    M.closedScale e.2 * hiddenWeight F Q M.ε ξ e

def affected (F : CA) (Λ : Finset Lattice) : Finset Edge :=
  (Λ.biUnion (fun j => (support F false).image (fun n => (j-n,false)))) ∪
  (Λ.biUnion (fun j => (support F true).image (fun n => (j-n,true))))

def paste (Λ : Finset Lattice) (a : Λ → Site q Q) (b : Config q Q) : Config q Q :=
  fun i => if hi : i ∈ Λ then a ⟨i,hi⟩ else b i

def volumeWeight (M : Model F Q) (Λ : Finset Lattice) (a : Λ → Site F.q Q)
    (b : Config F.q Q) : ℚ := ∏ e ∈ affected F Λ, localWeight M (paste Λ a b) e

def gamma (M : Model F Q) (Λ : Finset Lattice) (b : Config F.q Q)
    (f : Config F.q Q → ℝ) : ℝ :=
  (∑ a : Λ → Site F.q Q, (volumeWeight M Λ a b : ℝ)*f (paste Λ a b)) /
    ∑ a : Λ → Site F.q Q, (volumeWeight M Λ a b : ℝ)

def cylinder {α : Type} [DecidableEq α] (K : Finset Lattice) (a : K → α)
    (x : Lattice → α) : ℝ := if (fun i : K => x i.val) = a then 1 else 0

/-- DLR on every finite volume and every cylinder test, with counting prior. -/
def Gibbs (M : Model F Q) (μ : State F.q Q) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ Λ K a,
    (∫ ξ, cylinder K a ξ ∂μ) = ∫ ξ, gamma M Λ ξ (cylinder K a) ∂μ

def TI (μ : State q Q) : Prop := ∀ t : Lattice,
  Measure.map (fun ξ : Config q Q => fun i => ξ (i+t)) μ = μ

def spin (ξ : Config q 2) (i : Lattice) : ℝ := if (ξ i).1 = 0 then -1 else 1

def magnetization (ξ : Config q 9) (i : Lattice) : ℝ :=
  (9*(if (ξ i).1 = 0 then 1 else 0)-1)/8

def expectation (μ : State q Q) (f : Config q Q → ℝ) : ℝ := ∫ ξ, f ξ ∂μ

def covariance (μ : State q Q) (f g : Config q Q → ℝ) : ℝ :=
  expectation μ (fun ξ => f ξ*g ξ) - expectation μ f*expectation μ g

def d1 (i j : Lattice) : ℕ := (i.1-j.1).natAbs + (i.2-j.2).natAbs

def setDistance (A B : Finset Lattice) : ℕ :=
  if hab : (A.product B).Nonempty then (A.product B).inf' hab (fun ij => d1 ij.1 ij.2) else 0

structure Observable (q Q : ℕ) where
  sites : Finset Lattice
  nonempty : sites.Nonempty
  values : (sites → Site q Q) → ℝ

def Observable.eval (f : Observable q Q) (ξ : Config q Q) : ℝ := f.values (fun i => ξ i.val)
def Observable.bound (f : Observable q Q) : ℝ :=
  sSup (Set.range (fun a => |f.values a|))

def ClusterBound (μ : State q Q) : Prop := ∀ f g : Observable q Q,
  |covariance μ f.eval g.eval| ≤ 3*min (f.sites.card : ℝ) g.sites.card * f.bound*g.bound *
    (2 : ℝ)^(-(setDistance f.sites g.sites : ℤ))

def UniformSpinDecay (M : Model F 2) : Prop := ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
  ∀ μ, Gibbs M μ → ∀ x y,
    0 ≤ expectation μ (fun ξ => spin ξ x*spin ξ y) ∧
    expectation μ (fun ξ => spin ξ x*spin ξ y) ≤ C*Real.exp (-a*d1 x y)

def SpecifiedDecay (M : Model F 2) : Prop := ∀ μ, Gibbs M μ → ∃ C a : ℝ,
  0 < C ∧ 0 < a ∧ ∀ x,
    |expectation μ (fun ξ => spin ξ 0*spin ξ x)| ≤ C*Real.exp (-a*d1 0 x)

/-- Connectivity is a finite path in the full lattice. -/
def bondGraph (ω : Bonds) : SimpleGraph Lattice where
  Adj i j := i ≠ j ∧ ∃ r : Bool, (j=i+step r ∧ ω (i,r)=true) ∨ (i=j+step r ∧ ω (j,r)=true)
  symm := ⟨by
    rintro i j ⟨hne,r,hr⟩
    exact ⟨Ne.symm hne,r,hr.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def Connected (ω : Bonds) (x y : Lattice) : Prop := (bondGraph ω).Reachable x y

def InfiniteCluster (ω : Bonds) (x : Lattice) : Prop := Set.Infinite {y | Connected ω x y}

def box (n : ℕ) : Finset Lattice :=
  (Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n)

def internalEdges (V : Finset Lattice) : Finset Edge :=
  (V.product (Finset.univ : Finset Bool)).filter (fun e => e.1+step e.2 ∈ V)

def boundary (V : Finset Lattice) (x : Lattice) : Prop :=
  x ∈ V ∧ ∃ r : Bool, x+step r ∉ V ∨ x-step r ∉ V

def componentSetoid (V : Finset Lattice) (wired : Bool) (ω : Bonds) : Setoid V :=
  Relation.EqvGen.setoid (fun x y : V => (bondGraph ω).Adj x.val y.val ∨
    (wired = true ∧ boundary V x.val ∧ boundary V y.val))

def clusters (V : Finset Lattice) (wired : Bool) (ω : Bonds) : ℕ :=
  Nat.card (Quotient (componentSetoid V wired ω))

def extendBonds (E : Finset Edge) (ω : E → Bool) : Bonds :=
  fun e => if he : e ∈ E then ω ⟨e,he⟩ else false

def fkWeight (Q : ℕ) (v : Bool → ℝ) (V : Finset Lattice) (wired : Bool)
    (ω : internalEdges V → Bool) : ℝ :=
  (Q : ℝ)^(clusters V wired (extendBonds (internalEdges V) ω)) *
    ∏ e : internalEdges V, if ω e then v e.val.2 else 1

def fkEval (Q : ℕ) (v : Bool → ℝ) (V : Finset Lattice) (wired : Bool)
    (f : Bonds → ℝ) : ℝ :=
  (∑ ω, fkWeight Q v V wired ω * f (extendBonds (internalEdges V) ω)) /
    ∑ ω, fkWeight Q v V wired ω

instance bondMeasurable : MeasurableSpace Bool := ⊤
abbrev BondState := Measure Bonds

def bondCylinder (K : Finset Edge) (a : K → Bool) (ω : Bonds) : ℝ :=
  if (fun e : K => ω e.val) = a then 1 else 0

def FKLimit (Q : ℕ) (v : Bool → ℝ) (wired : Bool) (φ : BondState) : Prop :=
  IsProbabilityMeasure φ ∧ ∀ K a,
    Tendsto (fun n => fkEval Q v (box n) wired (bondCylinder K a)) atTop
      (nhds (∫ ω, bondCylinder K a ω ∂φ))

def bondExpectation (φ : BondState) (f : Bonds → ℝ) : ℝ := ∫ ω, f ω ∂φ

def theta (φ : BondState) : ℝ := (φ {ω | InfiniteCluster ω 0}).toReal

def stochasticLE (μ ν : BondState) : Prop := ∀ f : Bonds → ℝ,
  Measurable f → (∀ ω, |f ω| ≤ 1) → Monotone f → bondExpectation μ f ≤ bondExpectation ν f

/-- A canonical bond extension, tested on products of site and bond cylinders. -/
def bondKernelEval (M : Model F Q) (ξ : Config F.q Q) (K : Finset Edge) (a : K → Bool) : ℝ :=
  ∏ e : K, if a e then
    ((M.openWeight e.val.2 : ℝ)*(if (ξ e.val.1).1 = (ξ (e.val.1+step e.val.2)).1 then 1 else 0)) /
      (localWeight M ξ e.val : ℝ)
    else (M.closedScale e.val.2 * hiddenWeight F Q M.ε ξ e.val : ℚ) / (localWeight M ξ e.val : ℝ)

def CanonicalExtension (M : Model F Q) (μ : State F.q Q)
    (ν : Measure (Config F.q Q × Bonds)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ J b K a,
    (∫ z, cylinder J b z.1 * bondCylinder K a z.2 ∂ν) =
      ∫ ξ, cylinder J b ξ * bondKernelEval M ξ K a ∂μ

def square (n : ℕ) : Finset Lattice :=
  (Finset.Ico (0 : ℤ) n).product (Finset.Ico (0 : ℤ) n)

def freePartition (M : Model F 9) (n : ℕ) (field : ℝ) : ℝ :=
  ∑ a : square n → Site F.q 9,
    let ξ := paste (square n) a (fun _ => (0, fun _ => ⟨0, by have := F.two_le; omega⟩))
    (∏ e ∈ (affected F (square n)).filter (fun e => ∀ j ∈ support F e.2, e.1+j ∈ square n),
      (localWeight M ξ e : ℝ)) * Real.exp (field * ∑ i ∈ square n, magnetization ξ i)

def Pressure (M : Model F 9) (P : ℝ → ℝ) : Prop := ∀ field,
  Tendsto (fun n => Real.log (freePartition M n field)/(n : ℝ)^2) atTop (nhds (P field))

def RightDerivative (P : ℝ → ℝ) (d : ℝ) : Prop :=
  Tendsto (fun h => (P h-P 0)/h) (nhdsWithin 0 (Set.Ioi 0)) (nhds d)
def LeftDerivative (P : ℝ → ℝ) (d : ℝ) : Prop :=
  Tendsto (fun h => (P h-P 0)/h) (nhdsWithin 0 (Set.Iio 0)) (nhds d)

/-- A computable name for each rational field, plus the proved 1-Lipschitz modulus,
    gives uniform Type-2 evaluation on arbitrary real Cauchy names. -/
abbrev RatCode := ℤ × ℕ
def ratDecode (a : RatCode) : ℚ := a.1 / (a.2+1)
def RationalPressureComputable (P : ℝ → ℝ) : Prop := ∃ A : RatCode × ℕ → RatCode,
  Computable A ∧ ∀ h n, |(ratDecode (A (h,n)) : ℝ)-P (ratDecode h)| ≤ (2 : ℝ)^(-(n : ℤ))

def Undecidable (p : ℕ → Prop) : Prop := ¬ ∃ d : ℕ → Bool,
  Computable d ∧ ∀ n, d n = true ↔ p n

end
end Thermal


