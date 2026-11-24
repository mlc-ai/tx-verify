-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Hooks
public import Lemmas.Flow.NotClc
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # An instruction's warp collective, and its static part

A proof tool, generic over the kernel: an instruction that is no warp instruction fires no warp
collective (`eventTmpl_notColl`), and when the operands of the static part are immediates, the
static part is a function of the instruction (`opShape`, `tmpl_opShape`, `fires_opShape`). -/

namespace PTX.Flow

open PTX PTX.Sched

/-- A template of no warp collective. -/
def NotColl : Tmpl → Prop
  | .shfl .. | .elect .. | .warpBar .. | .vote .. => False
  | _ => True

/-- A warp instruction. -/
def isWarpOp : Op → Bool
  | .warp _ => true
  | _ => false

theorem widen_notColl {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotColl m) :
    NotColl (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notColl {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotColl r) :
    NotColl (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notColl {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotColl (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotColl]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notColl {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotColl (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notColl
  · simp only [NotColl]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notColl {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotColl a) (hb : NotColl b) :
    NotColl (if c then a else b) := by
  split <;> assumption

/-- An instruction that is no warp instruction fires no warp collective. -/
theorem eventTmpl_notColl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : isWarpOp op = false) : NotColl (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notColl (op := .int i)
  case move m => exact ruleTmpl_notColl (op := .move m)
  case cvt c => exact ruleTmpl_notColl (op := .cvt c)
  all_goals simp only [isWarpOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (apply tcStTmpl_pres (P := NotColl) (fun _ => trivial) trivial; intro u)
  all_goals first
    | (apply widen_notColl
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notColl)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, tensorStoreTmpl,
        reduxTmpl, matchTmpl, activemaskTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notColl)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notColl)
         | split)
    | trivial

/-- The value of an immediate 32-bit operand. -/
def immNat : Opnd → Option Nat
  | .imm v => some (truncBits 32 (BitVec.ofInt 64 v)).toNat
  | _ => none

/-- The static part of a warp instruction with immediate operands. -/
def opShape : Op → Option CollShape
  | .warp w => match w.kind, w.srcs, w.mask with
    | .shfl m, [_, b, c], _ => match immNat b, immNat c with
      | some b', some c' => some (.shfl m b' c')
      | _, _ => none
    | .elect, _, some mask => (immNat mask).map .elect
    | .barWarp, _, some mask => (immNat mask).map .warpBar
    | .vote .ballot _, _, some mask => (immNat mask).map .vote
    | _, _, _ => none
  | _ => none

/-- A warp instruction that fires a warp collective has an immediate static part, with a full
mask. -/
def opShapeOk : Op → Bool
  | .warp w => match opShape (.warp w) with
    | some (.shfl ..) => true
    | some (.elect m) | some (.warpBar m) | some (.vote m) => m == 4294967295
    | none => match w.kind with
      | .shfl _ | .elect | .barWarp | .vote .ballot _ => false
      | _ => true
  | _ => true

theorem readBits_imm {L : Launch} {g : Nat} {t : TState} {o : Opnd} {x : BitVec 64} {n : Nat}
    (h : readBits L g t 32 o = .ok x) (hi : immNat o = some n) : x.toNat = n := by
  cases o <;> simp [immNat] at hi
  simp only [readBits, pure, Except.pure, Except.ok.injEq] at h
  rw [← hi, ← h]


/-- **The static part of a warp instruction's template** is the instruction's. -/
theorem warpTmpl_shape {L : Launch} {g : Nat} {t : TState} {w : WarpInstr} {s s' : CollShape}
    (hs : opShape (.warp w) = some s) (hm : tmplShape (warpTmpl L g t w) = some s') : s' = s := by
  unfold warpTmpl at hm
  split at hm
  · rename_i m d p a b c mask hr hk hd hsr hmk
    simp only [opShape, hk, hsr] at hs
    unfold shflTmpl at hm
    split at hm
    · rename_i x1 x2 x3 x4 e1 e2 e3 e4
      split at hm
      · split at hm
        · simp only [tmplShape, Option.some.injEq] at hm
          cases hb : immNat b <;> cases hc : immNat c <;> simp [hb, hc] at hs
          rw [← hm, ← hs, readBits_imm e3 hb, readBits_imm e4 hc]
        · cases hm
      · cases hm
    all_goals cases hm
  · rename_i neg d a mask hr hk hd hsr hmk
    simp only [opShape, hk, hmk] at hs
    unfold voteTmpl at hm
    split at hm
    · rename_i x1 x2 e1 e2
      split at hm
      · simp only [tmplShape, Option.some.injEq] at hm
        cases hb : immNat mask <;> simp [hb] at hs
        rw [← hm, ← hs, readBits_imm e1 hb]
      · cases hm
    all_goals cases hm
  · unfold voteModeTmpl at hm
    split at hm
    · split at hm
      · split at hm <;> cases hm
      · cases hm
    all_goals cases hm
  · unfold reduxTmpl at hm
    repeat' split at hm
    all_goals cases hm
  · unfold matchTmpl at hm
    repeat' split at hm
    all_goals cases hm
  · simp [activemaskTmpl, tmplShape] at hm
  · rename_i d p mask hr hk hd hsr hmk
    simp only [opShape, hk, hmk] at hs
    unfold electTmpl at hm
    split at hm
    · cases hm
    · rename_i x1 e1
      split at hm
      · simp only [tmplShape, Option.some.injEq] at hm
        cases hb : immNat mask <;> simp [hb] at hs
        rw [← hm, ← hs, readBits_imm e1 hb]
      · cases hm
  · rename_i mask hr hk hd hsr hmk
    simp only [opShape, hk, hmk] at hs
    unfold warpBarTmpl at hm
    split at hm
    · cases hm
    · rename_i x1 e1
      split at hm
      · simp only [tmplShape, Option.some.injEq] at hm
        cases hb : immNat mask <;> simp [hb] at hs
        rw [← hm, ← hs, readBits_imm e1 hb]
      · cases hm
  · cases hm

/-- A template of a static part is a warp instruction's. -/
theorem tmplShape_warpOp {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {s : CollShape} (h : tmplShape (eventTmpl A L g t op) = some s) : ∃ w, op = .warp w := by
  by_cases hop : isWarpOp op = false
  · have hm := eventTmpl_notColl (A := A) (L := L) (g := g) (t := t) hop
    cases he : eventTmpl A L g t op <;> rw [he] at h hm <;> simp [tmplShape, NotColl] at h hm
  · cases op <;> simp [isWarpOp] at hop
    exact ⟨_, rfl⟩

/-- **The static part of an instruction's template** is a function of the instruction, full. -/
theorem tmpl_opShape {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {s : CollShape} (hok : opShapeOk op = true)
    (h : tmplShape (eventTmpl A L g t op) = some s) : opShape op = some s ∧ s.Full := by
  obtain ⟨w, rfl⟩ := tmplShape_warpOp h
  have h' : tmplShape (warpTmpl L g t w) = some s := h
  cases hs0 : opShape (.warp w) with
  | some s0 =>
    obtain rfl := warpTmpl_shape hs0 h'
    refine ⟨rfl, ?_⟩
    simp only [opShapeOk, hs0] at hok
    cases s <;> simp_all [CollShape.Full]
  | none =>
    exfalso
    simp only [opShapeOk, hs0] at hok
    unfold warpTmpl at h'
    split at h'
    all_goals try (rename_i hk _ _ _; rw [hk] at hok; cases hok; done)
    · unfold voteModeTmpl at h'
      split at h'
      · split at h'
        · split at h' <;> cases h'
        · cases h'
      all_goals cases h'
    · unfold reduxTmpl at h'
      repeat' split at h'
      all_goals cases h'
    · unfold matchTmpl at h'
      repeat' split at h'
      all_goals cases h'
    · simp [activemaskTmpl, tmplShape] at h'
    · cases h'

end PTX.Flow
