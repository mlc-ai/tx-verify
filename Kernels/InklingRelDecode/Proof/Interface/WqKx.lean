-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxWComp
public import Kernels.InklingRelDecode.Proof.Interface.LkMachine
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0

@[expose] public section

/-!
# The key time of a thread's state

`kx L g s` is the virtual time (`Wt.time`) of the synchronizing state that the stretch of states
from `s` ends at: `Lk.kxD` (read off the key) for the default partition, `Lk.kxW` (read off the
state's fields) for the worker warps. What the layers above use:

* `kx_sy`: at a synchronizing state it is the state's time;
* `kx_lt`: a state that is not synchronizing, with its invariant, is timed below it, when its key
  is the key of a synchronizing state of the same kind of thread;
* `kx_silent`: a step from a state that is not synchronizing keeps it;
* `kx_step_w`: two worker lanes' synchronizing states with one key and one key time, which agree
  and are valid (`WValid`), have successors of one key time.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch}

/-- **The key time of a state.** -/
def kx (L : Launch) (g : Nat) : TSt → Nat
  | .d s => PTX.Kernels.InklingRelDecode.Proof.Lk.kxD L g s
  | .w s => PTX.Kernels.InklingRelDecode.Proof.Lk.kxW s

/-- **At a synchronizing state the key time is the state's time.** -/
theorem kx_sy {g : Nat} {s : TSt} (h : tSy s) : kx L g s = Wt.time g s := by
  cases s with
  | d s => exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxD_sy L g h
  | w s => exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxW_sy h

theorem syPc_of_dSy {s : DComp.St} (h : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s = true) :
    PTX.Kernels.InklingRelDecode.Proof.Lk.syPc (DComp.pc s) = true := by
  cases s with
  | dstart d =>
    simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
      PTX.Kernels.InklingRelDecode.Proof.Lk.dsSy, PTX.Kernels.InklingRelDecode.Proof.Lk.syAt,
      Bool.and_eq_true] at h
    exact h.1.1
  | pro d =>
    simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
      PTX.Kernels.InklingRelDecode.Proof.Lk.proSy, PTX.Kernels.InklingRelDecode.Proof.Lk.syAt,
      Bool.and_eq_true] at h
    exact h.1
  | sm d =>
    simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
      PTX.Kernels.InklingRelDecode.Proof.Lk.smSy, PTX.Kernels.InklingRelDecode.Proof.Lk.syAt,
      Bool.and_eq_true] at h
    exact h.1
  | epi d =>
    simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
      PTX.Kernels.InklingRelDecode.Proof.Lk.epSy, PTX.Kernels.InklingRelDecode.Proof.Lk.syAt,
      Bool.and_eq_true] at h
    exact h.1

/-- **A state that is not synchronizing is timed below its key time**, given a synchronizing
state of the same kind of thread with the same key. -/
theorem kx_lt {g h : Nat} {s s' : TSt} (hns : ¬ tSy s) (hI : (threadCode L g Q).inv s)
    (hs' : tSy s') (hcls : s.isD ↔ s'.isD) (hk : tKey L g s = tKey L h s') :
    Wt.time g s < kx L g s := by
  cases s with
  | d s =>
    cases s' with
    | w s' => exact absurd (hcls.mp trivial) id
    | d s' =>
      have hpc := PTX.Kernels.InklingRelDecode.Proof.Lk.d_sy_key L h hs'
      have hk1 : (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s).1 = DComp.pc s' := by
        have := congrArg Prod.fst hk
        simp only [tKey] at this
        rw [this, hpc]
      have hsy : PTX.Kernels.InklingRelDecode.Proof.Lk.syPc
          (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s).1 = true := by
        rw [hk1]; exact syPc_of_dSy hs'
      have hns' : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s = false := by
        cases hd : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s
        · rfl
        · exact absurd hd hns
      exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxD_lt hns' hI.2 hsy
  | w s =>
    have hns' : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s = false := by
      cases hd : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s
      · rfl
      · exact absurd hd hns
    exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxW_lt hns' hI.2

/-- **A step from a state that is not synchronizing keeps the key time.** -/
theorem kx_silent {g : Nat} {s t : TSt} {e : Event} (hns : ¬ tSy s)
    (hn : (threadCode L g Q).next s e = some (some t)) : kx L g t = kx L g s := by
  cases s with
  | d s =>
    obtain ⟨a, ha, rfl⟩ := next_d_inv hn
    have hns' : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s = false := by
      cases hd : PTX.Kernels.InklingRelDecode.Proof.Lk.dSy s
      · rfl
      · exact absurd hd hns
    show PTX.Kernels.InklingRelDecode.Proof.Lk.ktD
        (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g a) =
      PTX.Kernels.InklingRelDecode.Proof.Lk.ktD (PTX.Kernels.InklingRelDecode.Proof.Lk.dKey L g s)
    rw [PTX.Kernels.InklingRelDecode.Proof.Lk.d_silent ha hns']
  | w s =>
    obtain ⟨a, ha, rfl⟩ := next_w_inv hn
    have hns' : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s = false := by
      cases hd : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s
      · rfl
      · exact absurd hd hns
    exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxW_silent ha hns'

/-- **Two worker lanes' synchronizing states with one key and one key time, which agree and are
valid, have successors of one key time.** -/
theorem kx_step_w {g h c : Nat} {s s' : WComp.WSt} {t t' : TSt} {e e' : Event}
    (hs : tSy (.w s)) (hs' : tSy (.w s')) (hk : tKey L g (.w s) = tKey L h (.w s'))
    (hx : kx L g (.w s) = kx L h (.w s'))
    (hv : PTX.Kernels.InklingRelDecode.Proof.Lk.WValid c s)
    (hv' : PTX.Kernels.InklingRelDecode.Proof.Lk.WValid c s')
    (ha : tAgree L g h (.w s) (.w s') e e')
    (hn : (threadCode L g Q).next (.w s) e = some (some t))
    (hn' : (threadCode L h Q).next (.w s') e' = some (some t')) : kx L g t = kx L h t' := by
  obtain ⟨a, ha1, rfl⟩ := next_w_inv hn
  obtain ⟨b, hb1, rfl⟩ := next_w_inv hn'
  have hk' : PTX.Kernels.InklingRelDecode.Proof.Lk.wKey L g s =
      PTX.Kernels.InklingRelDecode.Proof.Lk.wKey L h s' := by
    have := congrArg Prod.fst hk
    simpa [tKey, PTX.Kernels.InklingRelDecode.Proof.Lk.kOf] using this
  exact PTX.Kernels.InklingRelDecode.Proof.Lk.kxW_step hs hs' hk' hx hv hv' ha ha1 hb1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
