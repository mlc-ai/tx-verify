-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuEpoch
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts

@[expose] public section

/-!
# `RegWaitFacts.before`

A lane `h` of the warp of a thread `g` blocked at its register request of ordinal `K` that has made
no request of that ordinal has made at most `K` requests. Its state is timed at most `capR K`
(`WuEpoch.lean`), which is the time of `g`'s state before the request. A lane with at most `K`
requests has not exited (an exit of a default-partition thread follows three requests, of a worker
four), so its machine is at a state or stopped at its last event (`end_cases`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state's kind is its thread's. -/
theorem isD_iff {g : Nat} {s : TSt} (h : (threadCode L g Q).inv s) :
    isD s = true ↔ IsDefault L g := by
  cases s with
  | d s0 => simp [isD, h.1]
  | w s0 => simp [isD, h.1]

/-- The lanes of a warp are of one kind. -/
theorem isDefault_sameWarp {g h : Nat} (hw : SameWarp L g h) : IsDefault L g ↔ IsDefault L h := by
  obtain ⟨-, hd⟩ := hw
  unfold IsDefault
  omega

/-- States of two lanes of a warp are of one kind. -/
theorem isD_sameWarp {g h : Nat} {s s' : TSt} (hw : SameWarp L g h)
    (hs : (threadCode L g Q).inv s) (hs' : (threadCode L h Q).inv s') : isD s = isD s' := by
  have h1 := isD_iff hs
  have h2 := isD_iff hs'
  have h3 := isDefault_sameWarp hw
  cases hb : isD s <;> cases hb' : isD s' <;> simp_all

/-- **A request's ordinal is below its count of earlier requests**: the time of the state of a
request is its cap, and no state is later than `epi0 + 300`, so a default partition's request is
of ordinal at most 2 and a worker's of ordinal at most 3. -/
theorem req_ordinal_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k pc : Nat}
    {inc : Bool} {n inst : Nat} {d : TSt}
    (hget : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (hσ : St Q L X g k = some (some d)) :
    (isD d = true → rqN X g k ≤ 2) ∧ (isD d = false → rqN X g k ≤ 3) ∧
      capR (isD d) (rqN X g k) ≤ time g d := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX hget hσ
  have hreq := (event_req hX hS hget hσ).1.mp (by simp [SetMaxNReg.isRequest])
  have htb := tbl_at hpre hX hS hR (event_le hget) hσ hinv
  obtain ⟨-, -, h3, -, -, -, h7⟩ := htb
  have hc := h3 hreq
  refine ⟨fun hd => ?_, fun hd => ?_, hc⟩
  · rw [hd] at hc
    by_contra hlt
    have := capR_true_ge (r := rqN X g k) (by omega)
    wt_omega
  · rw [hd] at hc
    by_contra hlt
    have := capR_false_ge (r := rqN X g k) (by omega)
    wt_omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
include hpre hX hS htr

/-- **A lane with at most as many requests as a request's ordinal has not exited.** -/
theorem no_exit_of_few (hR : RoleReads L X) {g h k pc n inst : Nat} {inc : Bool} {d : TSt}
    (hw : SameWarp L g h) (hget : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩)
    (hσ : St Q L X g k = some (some d)) (hcnt : (X.tr h).countP SetMaxNReg.isRequest ≤ rqN X g k) :
    ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
  intro j pc' hx
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX hget hσ
  obtain ⟨hdd, hdw, -⟩ := req_ordinal_le hpre hX hS hR hget hσ
  have hmono : rqN X h j ≤ (X.tr h).countP SetMaxNReg.isRequest := by
    unfold rqN
    exact List.Sublist.countP_le (List.take_sublist _ _)
  rcases exit_event_state hX hS htr hx with ⟨e, hσh, hs⟩ | ⟨x, hσh, hs⟩
  · obtain ⟨t', ins', o', -, hinv', -, -⟩ := Frame.fired_site hS hX hx hσh
    obtain ⟨-, t1, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le hx) hσh
    have hp := d_exit_phase e hs
    have ht0 := h3 rfl
    simp only [tPh] at h1
    rw [hp] at h1
    have hD := (isD_sameWarp hw hinv hinv')
    have : isD d = true := by
      rw [hD]
      rfl
    have := hdd this
    omega
  · obtain ⟨t', ins', o', -, hinv', -, -⟩ := Frame.fired_site hS hX hx hσh
    obtain ⟨-, t1, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le hx) hσh
    have h6' := h5 rfl
    have hp : wPh (.exit x) = (1, 1) := rfl
    simp only [tPh] at h1
    rw [hp] at h1
    have hD := (isD_sameWarp hw hinv hinv')
    have : isD d = false := by
      rw [hD]
      rfl
    have := hdw this
    omega

/-- **A thread with few register requests is timed at most the cap of their count.** -/
theorem threadTime_rq_le (hR : RoleReads L X) (hub : ¬ HasUb X) {y : Nat} (hy : y < L.threads)
    (hnx : ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) {K : Nat} (dflt : Bool)
    (hdf : IsDefault L y ↔ dflt = true) (hcnt : (X.tr y).countP SetMaxNReg.isRequest ≤ K) :
    Sched.threadTime (timed Wt.time Q L) X y ≤ capR dflt K := by
  have hkind : ∀ s, (threadCode L y Q).inv s → isD s = dflt := by
    intro s hs
    have := isD_iff hs
    cases hb : isD s <;> cases dflt <;> simp_all
  rw [threadTime_unfold]
  rcases end_cases hX hS htr hub hy hnx with ⟨d, hσ, hinv⟩ | ⟨d, e, hlen, hσ, hσn, hinv, he⟩
  · rw [hσ]
    simp only
    have := tbl_at hpre hX hS hR le_rfl hσ hinv
    obtain ⟨h1, -⟩ := this
    rw [hkind d hinv] at h1
    have hr : rqN X y (X.tr y).length = (X.tr y).countP SetMaxNReg.isRequest := by
      simp [rqN]
    rw [hr] at h1
    exact h1.trans (capR_le dflt hcnt)
  · rw [hσn]
    simp only
    rw [hσ]
    simp only
    have hk : (X.tr y).length - 1 ≤ (X.tr y).length := by omega
    obtain ⟨h1, h2, h3, -⟩ := tbl_at hpre hX hS hR hk hσ hinv
    rw [hkind d hinv] at h1 h2 h3
    have he' : (X.tr y)[(X.tr y).length - 1]? = some e := he
    have hrq := rqN_succ hX hS he' hσ
    have hreq := (event_req hX hS he hσ).1
    have hr : rqN X y ((X.tr y).length - 1 + 1) = (X.tr y).countP SetMaxNReg.isRequest := by
      rw [Nat.sub_add_cancel hlen]
      simp [rqN]
    rw [hr] at hrq
    by_cases hq : (tReq d).isSome = true
    · have hq1 : rInc (tReq d) = 1 := by simp [rInc, hq]
      have h4 := capR_lt dflt (show rqN X y ((X.tr y).length - 1) < K by omega)
      have h5 := capR_le dflt (show rqN X y ((X.tr y).length - 1) + 1 ≤ K by omega)
      have h6 := capR_lt dflt
        (show rqN X y ((X.tr y).length - 1) < rqN X y ((X.tr y).length - 1) + 1 by omega)
      omega
    · have hq0 : (tReq d).isSome = false := by simpa using hq
      have hq1 : rInc (tReq d) = 0 := by simp [rInc, hq0]
      have h4 := h2 hq0
      have h5 := capR_le dflt (show rqN X y ((X.tr y).length - 1) ≤ K by omega)
      omega

/-- **A thread with few barrier-1 events is timed at most the cap of their count.** -/
theorem threadTime_b1_le (hR : RoleReads L X) (hub : ¬ HasUb X) {y : Nat} (hy : y < L.threads)
    (hnx : ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩) {n : Nat}
    (hcnt : (X.tr y).countP (Execution.isBarId 1) ≤ n) :
    Sched.threadTime (timed Wt.time Q L) X y ≤ capB n := by
  rw [threadTime_unfold]
  rcases end_cases hX hS htr hub hy hnx with ⟨d, hσ, hinv⟩ | ⟨d, e, hlen, hσ, hσn, hinv, he⟩
  · rw [hσ]
    simp only
    obtain ⟨-, -, -, h1, -⟩ := tbl_at hpre hX hS hR le_rfl hσ hinv
    have hr : b1N X y (X.tr y).length = (X.tr y).countP (Execution.isBarId 1) := by
      simp [b1N]
    rw [hr] at h1
    exact h1.trans (capB_le hcnt)
  · rw [hσn]
    simp only
    rw [hσ]
    simp only
    have hk : (X.tr y).length - 1 ≤ (X.tr y).length := by omega
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := tbl_at hpre hX hS hR hk hσ hinv
    have he' : (X.tr y)[(X.tr y).length - 1]? = some e := he
    have hb := event_b1 hpre hX hS he hσ
    have hrq : b1N X y ((X.tr y).length - 1 + 1) =
        b1N X y ((X.tr y).length - 1) + bInc (tB1 d) := by
      unfold b1N
      rw [countP_take_succ _ he', hb]
      rfl
    have hr : b1N X y ((X.tr y).length - 1 + 1) = (X.tr y).countP (Execution.isBarId 1) := by
      rw [Nat.sub_add_cancel hlen]
      simp [b1N]
    rw [hr] at hrq
    by_cases hq : tB1 d = true
    · have hq1 : bInc (tB1 d) = 1 := by simp [bInc, hq]
      have h4 := capB_lt (show b1N X y ((X.tr y).length - 1) < n by omega)
      have h5 := capB_le (show b1N X y ((X.tr y).length - 1) + 1 ≤ n by omega)
      have h6 := capB_lt
        (show b1N X y ((X.tr y).length - 1) < b1N X y ((X.tr y).length - 1) + 1 by omega)
      omega
    · have hq0 : tB1 d = false := by simpa using hq
      have hq1 : bInc (tB1 d) = 0 := by simp [bInc, hq0]
      have h4 := h2 hq0
      have h5 := capB_le (show b1N X y ((X.tr y).length - 1) ≤ n by omega)
      omega

/-- **`RegWaitFacts.before` for `Wt.time`.** -/
theorem reg_before (hR : RoleReads L X) (hub : ¬ HasUb X) {g h k pc n inst : Nat} {inc : Bool}
    {d : TSt} (_hg : g < L.threads) (hh : h < L.threads) (hw : SameWarp L g h)
    (hno : ∀ j pc' inc' n' inst', SetMaxNReg.Request X (h, j) pc' inc' n' inst' →
      SetMaxNReg.ordinal X (h, j) ≠ SetMaxNReg.ordinal X (g, k))
    (hget : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (hσ : St Q L X g k = some (some d)) :
    Sched.threadTime (timed Wt.time Q L) X h ≤ Wt.time g d := by
  have hcnt : (X.tr h).countP SetMaxNReg.isRequest ≤ rqN X g k := by
    by_contra hlt
    obtain ⟨j, ev, hj, hev, hjo⟩ := NamedBar.exists_ordinal SetMaxNReg.isRequest (X.tr h)
      (Nat.lt_of_not_le hlt)
    obtain ⟨pcx, kd⟩ := ev
    cases kd <;> simp [SetMaxNReg.isRequest] at hev
    rename_i inc' n' inst'
    exact hno j pcx inc' n' inst' hj hjo
  have hnx := no_exit_of_few hpre hX hS htr hR hw hget hσ hcnt
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX hget hσ
  obtain ⟨-, -, hc⟩ := req_ordinal_le hpre hX hS hR hget hσ
  have := threadTime_rq_le hpre hX hS htr hR hub hh hnx (isD d)
    ((isDefault_sameWarp hw).symm.trans (isD_iff hinv).symm) hcnt
  exact this.trans hc

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
