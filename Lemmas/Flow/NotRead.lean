-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Reads come from load instructions

A proof tool. A read event (`.rd`) is fired by a load instruction (`fires_read_op`): every other
instruction's template fires no read. -/

namespace PTX.Flow

open PTX.Proof

/-- A template that fires no read. -/
def NotRead : Tmpl → Prop
  | .read .. => False
  | _ => True

theorem widen_notRead {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotRead m) :
    NotRead (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notRead {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotRead r) :
    NotRead (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction reads shared memory: a load, or a `movmatrix` that loads (a move that
stores reads only registers). -/
def readOp : Op → Bool
  | .mem a => match a.kind with
    | .load => true
    | _ => false
  | .matrix m => match m.op with
    | .move mv => !mv.store
    | _ => false
  | _ => false

/-- An atomic instruction's template performs a read-modify-write, not a read. -/
theorem atomTmpl_notRead {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} : NotRead (atomTmpl A L g t a) := by
  unfold atomTmpl
  dsimp only
  repeat' split <;> simp only [NotRead]

/-- The event of a local rule of an integer, move or conversion instruction is no read. -/
theorem localSregTmpl_notRead {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotRead (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotRead]

/-- The template of an instruction's rule, or its `noRule` fault, is no read. -/
theorem ruleTmpl_notRead {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotRead (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notRead
  · simp only [NotRead]

/-- An `if` of two templates that fire no read fires none. -/
theorem ite_notRead {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotRead a) (hb : NotRead b) :
    NotRead (if c then a else b) := by
  split <;> assumption

/-- An instruction that does not load reads nothing. -/
theorem eventTmpl_notRead {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : readOp op = false) : NotRead (eventTmpl A L g t op) := by
  cases op
  case mem a =>
    simp only [readOp] at hop
    split at hop
    · contradiction
    · rename_i hk
      simp only [eventTmpl, memTmpl]
      split
      · split
        all_goals first
          | exact absurd ‹a.kind = .load› hk
          | (simp only [releaseStoreTmpl, storeTmpl]; repeat' first | trivial | split)
          | (rcases accessTmpl_write (A := A) (L := L) (g := g) (t := t) (a := a)
              (fun h => hk h) with ⟨f, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> trivial)
      · exact atomTmpl_notRead
      · split
        · rcases accessTmpl_write (A := A) (L := L) (g := g) (t := t) (a := a)
            (fun h => hk h) with ⟨f, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> trivial
        · trivial
  case int i => exact ruleTmpl_notRead (op := .int i)
  case move m => exact ruleTmpl_notRead (op := .move m)
  case cvt c => exact ruleTmpl_notRead (op := .cvt c)
  case matrix m =>
    simp only [readOp] at hop
    simp only [eventTmpl, matrixTmpl, matrixMoveTmpl]
    repeat' first
      | trivial
      | split
      | (exfalso; simp_all)
  all_goals simp only [readOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notRead
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notRead)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [warpTmpl, barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        warpBarTmpl, electTmpl, shflTmpl,
        voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl, activemaskTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl, tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notRead)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notRead)
         | split)
    | trivial

/-- A read is fired by a load instruction. -/
theorem fires_read_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) : readOp op = true := by
  cases hq : readOp op
  · exfalso
    have hm := eventTmpl_notRead (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotRead] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
