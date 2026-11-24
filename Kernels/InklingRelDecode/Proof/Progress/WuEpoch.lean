-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuCap

@[expose] public section

/-!
# The epoch bound of an execution's states

At every state a thread's machine is at, the virtual time is capped by the counts of the thread's
earlier register requests and barrier-1 events (`WuCap.lean`): `tbl_at`. From it, the time of the
thread's current state, or of the state before its last event when its machine stopped there
(`Sched.threadTime`), is capped by the counts of the whole trace (`threadTime_tbl`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The default partition's states. -/
def isD : TSt → Bool
  | .d _ => true
  | .w _ => false

theorem time_d (g : Nat) (s : DComp.St) : time g (.d s) = dcompT s := rfl
theorem time_w (g : Nat) (s : WComp.WSt) : time g (.w s) = wcompT s := rfl

/-- **The tables at a state of an execution**: the time of the state is capped by the counts of
requests and of barrier-1 events before it. -/
theorem tbl_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k : Nat} {s : TSt}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some s))
    (hinv : (threadCode L g Q).inv s) :
    Tbl (isD s) (time g s) (rqN X g k) (b1N X g k) (tReq s).isSome (tB1 s) := by
  obtain ⟨hto, t, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR k s hk hσ
  have hl := late_inv hpre hX hS hR k s hk hσ
  cases s with
  | d s0 =>
    have ht := h3 rfl
    subst ht
    have := dcomp_tbl hinv.2
    simp only [tPh] at h1 h2
    rw [h1, h2]
    exact this
  | w s0 =>
    have hw : wTo s0 = false := hto
    have := wcomp_tbl (t := t) hinv.2 hw h6 h4 h5 (fun P hs => by
      have h7 := hl.2 P
      have hr : rqN X g k = (wPh s0).1 + 3 * t := h1
      have hlt : ∀ r : Nat, r = 0 + 3 * t ∨ r = 1 + 3 * t → (3 ≤ r ↔ t = 1) := by
        intro r hr'
        omega
      rcases hs with hs | hs | hs <;> subst hs
      · have h8 := h7 .loop (.inl rfl) rfl
        exact h8.trans (hlt _ (.inl (by simpa [wPh] using hr)))
      · have h8 := h7 .bar2 (.inr (.inl rfl)) rfl
        exact h8.trans (hlt _ (.inr (by simpa [wPh] using hr)))
      · have h8 := h7 .ldRole (.inr (.inr rfl)) rfl
        exact h8.trans (hlt _ (.inr (by simpa [wPh] using hr))))
    have hr : rqN X g k = (wPh s0).1 + 3 * t := h1
    have hb : b1N X g k = (wPh s0).2 + 3 * t := h2
    rw [hr, hb]
    exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
