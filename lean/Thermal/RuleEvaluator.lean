import Mathlib.Computability.Partrec
import Lean.Elab.Tactic.Omega

namespace Thermal.Algorithm
open Primrec
abbrev Point := ℤ × ℤ
abbrev Code := ℕ × (List Point × List ℕ)

theorem prim_pow : Primrec₂ (fun a b : ℕ => a^b) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem prim_natCast : Primrec (fun n : ℕ => (n : ℤ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun n => rfl)

theorem prim_negSucc : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun n => rfl)

theorem prim_intSplit : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq (fun n => by cases n <;> rfl)

theorem prim_intCases {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) := by
  exact (Primrec.sumCasesOn (prim_intSplit.comp hf) hg hh).of_eq
    (fun a => by cases f a <;> rfl)

theorem prim_natAbs : Primrec Int.natAbs := by
  exact (prim_intCases Primrec.id Primrec₂.right
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (fun n => by cases n <;> rfl)

theorem prim_neg : Primrec (fun n : ℤ => -n) := by
  have hn : Primrec (fun n : ℕ => -(n : ℤ)) := by
    exact (Primrec.nat_casesOn Primrec.id (Primrec.const 0)
      (prim_negSucc.comp Primrec.snd).to₂).of_eq (fun n => by cases n <;> rfl)
  exact (prim_intCases Primrec.id (hn.comp Primrec.snd).to₂
    (prim_natCast.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
    (fun n => by cases n <;> rfl)

theorem prim_subNatNat : Primrec₂ Int.subNatNat := by
  have ht : Primrec (fun p : ℕ × ℕ =>
      if p.2 ≤ p.1 then ((p.1-p.2 : ℕ) : ℤ) else Int.negSucc (p.2-p.1-1)) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (prim_natCast.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (prim_negSucc.comp (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))
  refine ht.of_eq (fun p => ?_)
  split <;> rename_i hp
  · rw [Int.subNatNat_of_le hp]
  · rw [Int.subNatNat_of_lt (Nat.lt_of_not_ge hp), Nat.pred_eq_sub_one]

theorem prim_intAdd : Primrec₂ (fun a b : ℤ => a+b) := by
  have hn : Primrec₂ (fun a : ℤ => fun b : ℕ => a+(b : ℤ)) := by
    apply (prim_intCases Primrec.fst
      (prim_natCast.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
      (prim_subNatNat.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.succ.comp Primrec.snd)).to₂).of_eq
    rintro ⟨a,b⟩
    cases a <;> simp [Int.subNatNat_eq_coe, Int.negSucc_eq] <;> omega
  have hm : Primrec₂ (fun a : ℤ => fun b : ℕ => a+Int.negSucc b) := by
    apply (prim_intCases Primrec.fst
      (prim_subNatNat.comp Primrec.snd
        (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).to₂
      (prim_negSucc.comp (Primrec.succ.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂).of_eq
    rintro ⟨a,b⟩
    cases a <;> simp [Int.subNatNat_eq_coe, Int.negSucc_eq] <;> omega
  exact (prim_intCases Primrec.snd
    (hn.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (hm.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
    (fun p => by cases p.2 <;> rfl)

theorem prim_intSub : Primrec₂ (fun a b : ℤ => a-b) :=
  (prim_intAdd.comp Primrec.fst (prim_neg.comp Primrec.snd)).to₂.of_eq
    (fun a b => (sub_eq_add_neg a b).symm)

def evalLocal (q : ℕ) (table symbols : List ℕ) : ℕ :=
  ((table[symbols.foldl (fun acc digit => acc*q+digit) 0]?).getD 0)%q

theorem prim_evalLocal : Primrec (fun p : ℕ × (List ℕ × List ℕ) =>
    evalLocal p.1 p.2.1 p.2.2) := by
  unfold evalLocal
  apply Primrec.nat_mod.comp _ Primrec.fst
  apply Primrec.option_getD.comp _ (Primrec.const 0)
  apply Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
  refine Primrec.list_foldl (h := fun (a : ℕ × (List ℕ × List ℕ)) (st : ℕ × ℕ) => st.1*a.1+st.2)
    (Primrec.snd.comp Primrec.snd) (Primrec.const 0) ?_
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂

end Thermal.Algorithm



