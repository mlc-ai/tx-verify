-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Code
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.NotObject

@[expose] public section

/-! Tensor copies target the shared memory of the issuing CTA. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- A tensor copy to the CTA's own shared memory without multicast. -/
def localCopyOp : Op → Bool
  | .cpTensor false _ _ _ _ _ _ _ none _ _ => true
  | _ => false

/-- **Every tensor copy of the code is a local copy.** -/
theorem kernel_copy_local :
    OpPcsFast kernel.code (fun op => tensorOp op && !localCopyOp op) [] = true := by
  decide +kernel

/-- The destination of a tensor copy without cluster addressing is in the thread's own CTA. -/
theorem tensorLoadCopy_base {L : Launch} {g : Nat} {t : TState} {grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t false grp dst off map cs mb moff lm = .ok (a, s)) :
    s.sharedBase.cta = g / L.block := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Bool.false_eq_true, ↓reduceIte] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)
  all_goals exact (sharedEffAddr_local ‹sharedEffAddr L g t false dst off = .ok _›).2

/-- **The shared base of a local copy's issue is in its issuer's CTA.** -/
theorem fires_copy_base {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hl : localCopyOp op = true)
    (hf : Fires pc (eventTmpl A L g t op) e o) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) : s.sharedBase.cta = g / L.block := by
  cases op with
  | cpTensor cl grp dst off map cs mb moff mc mode pol =>
    cases cl
    · cases mc
      · simp only [eventTmpl, tensorTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at hf
        cases hp : cachePolicyRead L g t pol with
        | error f =>
          simp only [hp, ofExec, Fires] at hf
          rw [hf.1] at hk
          cases hk
        | ok u =>
          simp only [hp] at hf
          cases hc : tensorLoadCopy L g t false grp dst off map cs mb moff mode with
          | error f =>
            simp only [hc, ofExec, Fires] at hf
            rw [hf.1] at hk
            cases hk
          | ok p =>
            obtain ⟨a', s'⟩ := p
            simp only [hc] at hf
            split at hf
            · simp only [ofExec, Fires] at hf
              rw [hf.1] at hk
              cases hk
              exact tensorLoadCopy_base hc
            · simp only [ofExec, Fires] at hf
              rw [hf.1] at hk
              cases hk
      · simp [localCopyOp] at hl
    · simp [localCopyOp] at hl
  | _ => simp [localCopyOp] at hl

end PTX.Kernels.InklingRelDecode.Proof.Lib
