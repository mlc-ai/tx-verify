-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Common.Requests
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.RegState
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.Export.RegLedger
public import Lemmas.Kernel.Progress.RegO
import Kernels.InklingRelDecode.Proof.Common.RequestPrefix
import Kernels.InklingRelDecode.Proof.Prologue.Export.RegBand
import Kernels.InklingRelDecode.Proof.Softmax.Export.RegBand
import Kernels.InklingRelDecode.Proof.Epilogue.Export.RegBand
import Kernels.InklingRelDecode.Proof.Loader.Export.RegBand
import Kernels.InklingRelDecode.Proof.Mma.Export.RegBand
import all Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.Time

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

private theorem dispatch_band (d : Dispatch.D) (ok : DispatchClean d) :
    (Dispatch.requestPhase d = 0 → dispatchClock d = 30) ∧
    (Dispatch.requestPhase d = 1 → 30 < dispatchClock d ∧ dispatchClock d ≤ 285) ∧
    (Dispatch.requestPhase d = 2 → 285 < dispatchClock d ∧
      dispatchClock d ≤ Lib.Slots.finish + 280) ∧
    (Dispatch.requestPhase d = 3 → dispatchClock d = Lib.Slots.finish + 284) ∧
    (Dispatch.requestPhase d = 4 → Lib.Slots.finish + 284 < dispatchClock d) ∧
    (Dispatch.requestPhase d ≤ 3 → d.site.pc ∈ Lib.requestPcs → dispatchClock d =
      [30, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD
        (Dispatch.requestPhase d) 0) ∧
    (Dispatch.requestPhase d ≤ 3 → d.site.pc ∉ Lib.requestPcs → dispatchClock d <
      [30, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD
        (Dispatch.requestPhase d) 0) := by
  obtain ⟨s,r⟩ := d
  obtain ⟨g1,g2,early,late⟩ := ok
  simp only [Dispatch.requestPhase, Dispatch.requestOffset, dispatchClock, Lib.Slots.publish,
    Lib.Slots.enter, Lib.Slots.reuse, Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride] at *
  rcases (by omega : r = 0 ∨ r = 1 ∨ 2 ≤ r) with rfl | rfl | h <;> cases s <;>
    simp_all [Dispatch.Site.pc, Lib.requestPcs] <;> omega

/-- The clock of a data request site, by the number of requests before it. -/
def dataClock (r : Nat) : Nat := [100, 285, Epilogue.startTime + 280].getD r 0

private theorem startup_clock {Q L g} (st : Startup.D) (n : Cls → Nat) :
    (schedule Q L).time g (.inl st, n) ≤ 26 := by
  obtain ⟨s,t,x,w⟩ := st; change startupClock _ ≤ 26
  cases s <;> first | (rename_i r; cases r <;> simp [startupClock]) | simp [startupClock]

private theorem dc0 : dataClock 0 = 100 := rfl
private theorem dc1 : dataClock 1 = 285 := rfl
private theorem dc2 : dataClock 2 = Epilogue.startTime + 280 := rfl

/-- The clock of a state of the startup or the data partition is bounded by its request count. -/
theorem data_upper {Q L g} (s : (thread Q L g).D) (tab : tableInv Q L g s)
    (ok : requestClean s) (ds : DataState s) (le : requests s ≤ 2) :
    (schedule Q L).time g s ≤ dataClock (requests s) ∧
    ((thread Q L g).pc s ∈ Lib.requestPcs →
      (schedule Q L).time g s = dataClock (requests s)) ∧
    ((thread Q L g).pc s ∉ Lib.requestPcs →
      (schedule Q L).time g s < dataClock (requests s)) := by
  obtain ⟨s0,n⟩ := s
  rcases s0 with st | ⟨r, d⟩
  · have := startup_clock (Q := Q) (L := L) (g := g) st n
    have pc := startup_pc st n tab
    have r0 : requests ((.inl st, n) : (thread Q L g).D) = 0 := rfl
    exact ⟨by rw [r0, dc0]; omega, fun h => (pc h).elim, fun _ => by rw [r0, dc0]; omega⟩
  rcases r with r | r
  swap
  · exact ok.elim
  cases r with
  | dispatch => exact ds.elim
  | prologue w =>
    rcases d with p | ⟨ent, sm | ⟨u, e⟩⟩
    · obtain ⟨b1, b2, -⟩ := Prologue.Export.regBand p
      have ne := pro_not_exit tab
      change Prologue.time p ≤ dataClock (Prologue.requestPhase p.site) ∧
        (p.site.pc ∈ Lib.requestPcs → Prologue.time p = dataClock (Prologue.requestPhase p.site)) ∧
        (p.site.pc ∉ Lib.requestPcs → Prologue.time p < dataClock (Prologue.requestPhase p.site))
      by_cases h : p.site = .sMax
      · have : Prologue.requestPhase p.site = 0 := by simp [Prologue.requestPhase, h]
        rw [this, dc0]
        exact ⟨(b2 this).le, fun _ => b2 this, fun hp => (hp ((pro_hit _).mpr (.inl h))).elim⟩
      · have : Prologue.requestPhase p.site = 1 := by simp [Prologue.requestPhase, h]
        rw [this, dc1]
        exact ⟨by omega, fun hp => ((pro_hit _).mp hp |>.elim h ne).elim, fun _ => by omega⟩
    · have inv : Softmax.Control.Inv ent (g % L.block) sm := tab.1.1
      obtain ⟨b1, b2⟩ := Softmax.Export.regBand inv
      change Softmax.time sm ≤ dataClock (Softmax.requestPhase sm.site) ∧
        (sm.site.pc ∈ Lib.requestPcs → Softmax.time sm = dataClock (Softmax.requestPhase sm.site)) ∧
        (sm.site.pc ∉ Lib.requestPcs → Softmax.time sm < dataClock (Softmax.requestPhase sm.site))
      by_cases h : sm.site = .setMaxReg
      · have : Softmax.requestPhase sm.site = 1 := by simp [Softmax.requestPhase, h]
        rw [this, dc1]
        exact ⟨(b1 this).le, fun _ => b1 this, fun hp => (hp ((soft_hit _).mpr h)).elim⟩
      · have : Softmax.requestPhase sm.site = 2 := by simp [Softmax.requestPhase]
        rw [this, dc2]
        have up := (b2 this).2
        refine ⟨Nat.le_trans up (Nat.le_add_right _ _), fun hp => (h ((soft_hit _).mp hp)).elim,
          fun _ => Nat.lt_of_le_of_lt up (by decide +kernel)⟩
    · obtain ⟨b1, -, b3⟩ := Epilogue.Export.regBand e
      change Epilogue.time e ≤ dataClock (Epilogue.requestPhase e.site) ∧
        (e.site.pc ∈ Lib.requestPcs → Epilogue.time e = dataClock (Epilogue.requestPhase e.site)) ∧
        (e.site.pc ∉ Lib.requestPcs → Epilogue.time e < dataClock (Epilogue.requestPhase e.site))
      have p2 : Epilogue.requestPhase e.site = 2 := by
        simp only [requests, dataRequests, softRequests] at le
        have lo : 2 ≤ Epilogue.requestPhase e.site := by
          unfold Epilogue.requestPhase; split <;> omega
        omega
      rw [p2, dc2]
      refine ⟨b1 p2, fun hp => ?_, fun hp => b3 p2 (fun h => hp ((epi_hit _).mpr h))⟩
      have : e.site = .setMax := (epi_hit _).mp hp
      simp [Epilogue.time, this, Epilogue.Site.position, Epilogue.startTime]
private theorem start_big : 285 < Epilogue.startTime := by decide +kernel

/-- A state of the startup or the data partition after `k + 1` requests is later than the
`(k+1)`-th request's site. -/
theorem data_lower {Q L g} (s : (thread Q L g).D) (tab : tableInv Q L g s)
    (ok : requestClean s) (ds : DataState s) {k : Nat} (hk : requests s = k + 1) :
    dataClock k < (schedule Q L).time g s := by
  obtain ⟨s0,n⟩ := s
  rcases s0 with st | ⟨r, d⟩
  · exact absurd hk (by change 0 ≠ _; omega)
  rcases r with r | r
  swap
  · exact ok.elim
  cases r with
  | dispatch => exact ds.elim
  | prologue w =>
    rcases d with p | ⟨ent, sm | ⟨u, e⟩⟩
    · obtain ⟨-, -, b3⟩ := Prologue.Export.regBand p
      change Prologue.requestPhase p.site = k + 1 at hk
      by_cases h : p.site = .sMax
      · simp [Prologue.requestPhase, h] at hk
      have : Prologue.requestPhase p.site = 1 := by simp [Prologue.requestPhase, h]
      have k0 : k = 0 := by omega
      subst k0
      exact b3 this
    · have inv : Softmax.Control.Inv ent (g % L.block) sm := tab.1.1
      obtain ⟨b1, b2⟩ := Softmax.Export.regBand inv
      change Softmax.requestPhase sm.site = k + 1 at hk
      change dataClock k < Softmax.time sm
      by_cases h : sm.site = .setMaxReg
      · have ph : Softmax.requestPhase sm.site = 1 := by simp [Softmax.requestPhase, h]
        have k0 : k = 0 := by omega
        subst k0
        rw [b1 ph]
        decide
      · have ph : Softmax.requestPhase sm.site = 2 := by simp [Softmax.requestPhase]
        have k1 : k = 1 := by omega
        subst k1
        rw [dc1]
        exact (b2 ph).1
    · obtain ⟨b1, b2, -⟩ := Epilogue.Export.regBand e
      change Epilogue.requestPhase e.site = k + 1 at hk
      change dataClock k < Epilogue.time e
      have two : Epilogue.requestPhase e.site = 2 ∨ Epilogue.requestPhase e.site = 3 := by
        unfold Epilogue.requestPhase; split <;> omega
      rcases two with h | h
      · have k1 : k = 1 := by omega
        subst k1
        have : Epilogue.startTime ≤ Epilogue.time e := Nat.le_add_right _ _
        have := start_big
        rw [dc1]; omega
      · have k2 : k = 2 := by omega
        subst k2
        rw [dc2]
        exact b2 h
variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The clock of a state of the startup or of a worker is bounded by its request count. -/
theorem worker_upper {Q L g} (s : (thread Q L g).D) (tab : tableInv Q L g s)
    (ok : requestClean s) (ws : WorkerState s) (le : requests s ≤ 3) :
    (schedule Q L).time g s ≤ workClock (requests s) ∧
    ((thread Q L g).pc s ∈ Lib.requestPcs →
      (schedule Q L).time g s = workClock (requests s)) ∧
    ((thread Q L g).pc s ∉ Lib.requestPcs →
      (schedule Q L).time g s < workClock (requests s)) := by
  obtain ⟨s0,n⟩ := s
  rcases s0 with st | ⟨r, d⟩
  · have := startup_clock (Q := Q) (L := L) (g := g) st n
    have pc := startup_pc st n tab
    have r0 : requests ((.inl st, n) : (thread Q L g).D) = 0 := rfl
    exact ⟨by rw [r0, wc0]; omega, fun h => (pc h).elim, fun _ => by rw [r0, wc0]; omega⟩
  rcases r with r | r
  swap
  · exact ok.elim
  cases r with
  | prologue => exact ws.elim
  | dispatch w x =>
    rcases d with dd | ⟨i, ld⟩
    · obtain ⟨b0, b1, b2, b3, -, b5, b6⟩ := dispatch_band dd ok
      change dispatchClock dd ≤ workClock (Dispatch.requestPhase dd) ∧
        (dd.site.pc ∈ Lib.requestPcs → dispatchClock dd = workClock (Dispatch.requestPhase dd)) ∧
        (dd.site.pc ∉ Lib.requestPcs → dispatchClock dd < workClock (Dispatch.requestPhase dd))
      change Dispatch.requestPhase dd ≤ 3 at le
      refine ⟨?_, b5 le, b6 le⟩
      rcases (by omega : Dispatch.requestPhase dd = 0 ∨ Dispatch.requestPhase dd = 1 ∨
        Dispatch.requestPhase dd = 2 ∨ Dispatch.requestPhase dd = 3) with h | h | h | h
      · rw [h, wc0, b0 h]
      · rw [h, wc1]; exact (b1 h).2
      · rw [h, wc2]; exact (b2 h).2
      · rw [h, wc3, b3 h]
    · cases i with
      | loader k =>
        have z : k = 0 := ok
        subst z
        obtain ⟨b1, b2, b3, b4⟩ := Loader.Export.regBand ld
        obtain ⟨p1, p3⟩ := loader_phase ld
        change Loader.time ld ≤ workClock (3 * 0 + Loader.requestPhase ld.site) ∧
          (ld.site.pc ∈ Lib.requestPcs →
            Loader.time ld = workClock (3 * 0 + Loader.requestPhase ld.site)) ∧
          (ld.site.pc ∉ Lib.requestPcs →
            Loader.time ld < workClock (3 * 0 + Loader.requestPhase ld.site))
        rw [Nat.mul_zero, Nat.zero_add]
        refine ⟨(worker_pick b1 b2 b3 p1 p3).1, fun hp => worker_eq p3 p1 (b4.1 hp), fun hn => ?_⟩
        have h2 : Loader.requestPhase ld.site = 2 := by
          by_contra ne
          exact hn (b4.2.2 ne)
        rw [h2, wc2]
        exact b4.2.1 h2 hn
      | mma k =>
        have z : k = 0 := ok
        subst z
        have inv : Mma.Inv ld := by
          have h := tab.1
          simp only at h
          exact h.1
        obtain ⟨b1, b2, b3, b4⟩ := Mma.Export.regBand ld inv
        obtain ⟨p1, p3⟩ := mma_phase ld
        change Mma.time ld ≤ workClock (3 * 0 + Mma.requestPhase ld.site) ∧
          (ld.site.pc ∈ Lib.requestPcs →
            Mma.time ld = workClock (3 * 0 + Mma.requestPhase ld.site)) ∧
          (ld.site.pc ∉ Lib.requestPcs →
            Mma.time ld < workClock (3 * 0 + Mma.requestPhase ld.site))
        rw [Nat.mul_zero, Nat.zero_add]
        refine ⟨(worker_pick b1 b2 b3 p1 p3).1, fun hp => worker_eq p3 p1 (b4.1 hp), fun hn => ?_⟩
        have h2 : Mma.requestPhase ld.site = 2 := by
          by_contra ne
          exact hn (b4.2.2 ne)
        rw [h2, wc2]
        exact b4.2.1 h2 hn
/-- A state of a worker after `k + 1` requests is later than the `(k+1)`-th request's site. -/
theorem worker_lower {Q L g} (s : (thread Q L g).D) (tab : tableInv Q L g s)
    (ok : requestClean s) (ws : WorkerState s) {k : Nat} (hk : requests s = k + 1)
    (le : k ≤ 3) : workClock k < (schedule Q L).time g s := by
  obtain ⟨s0,n⟩ := s
  rcases s0 with st | ⟨r, d⟩
  · exact absurd hk (by change 0 ≠ _; omega)
  rcases r with r | r
  swap
  · exact ok.elim
  cases r with
  | prologue => exact ws.elim
  | dispatch w x =>
    rcases d with dd | ⟨i, ld⟩
    · obtain ⟨-, b1, b2, b3, b4, -, -⟩ := dispatch_band dd ok
      change Dispatch.requestPhase dd = k + 1 at hk
      change workClock k < dispatchClock dd
      have big : 285 < Lib.Slots.finish := by decide +kernel
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · rw [wc0]; exact (b1 hk).1
      · rw [wc1]; exact (b2 hk).1
      · rw [wc2, b3 hk]; generalize Lib.Slots.finish = F at *; omega
      · rw [wc3]; exact b4 hk
    · cases i with
      | loader j =>
        have z : j = 0 := ok
        subst z
        obtain ⟨b1, b2, b3, -⟩ := Loader.Export.regBand ld
        obtain ⟨p1, p3⟩ := loader_phase ld
        change 3 * 0 + Loader.requestPhase ld.site = k + 1 at hk
        change workClock k < Loader.time ld
        have := (worker_pick b1 b2 b3 p1 p3).2
        rw [Nat.mul_zero, Nat.zero_add] at hk
        rw [show k = Loader.requestPhase ld.site - 1 by omega]
        exact this
      | mma j =>
        have z : j = 0 := ok
        subst z
        have inv : Mma.Inv ld := by
          have h := tab.1
          simp only at h
          exact h.1
        obtain ⟨b1, b2, b3, -⟩ := Mma.Export.regBand ld inv
        obtain ⟨p1, p3⟩ := mma_phase ld
        change 3 * 0 + Mma.requestPhase ld.site = k + 1 at hk
        change workClock k < Mma.time ld
        have := (worker_pick b1 b2 b3 p1 p3).2
        rw [Nat.mul_zero, Nat.zero_add] at hk
        rw [show k = Mma.requestPhase ld.site - 1 by omega]
        exact this

def regClk (data : Bool) (r : Nat) : Nat := if data then dataClock r else workClock r

theorem regClk_lt {data : Bool} {a b : Nat} (h : a < b)
    (hb : b ≤ if data then 2 else 3) : regClk data a < regClk data b := by
  have big : 285 < Lib.Slots.finish := by decide +kernel
  cases data
  · simp only [regClk, Bool.false_eq_true, ↓reduceIte] at *
    obtain rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
    · omega
    all_goals obtain rfl | rfl | rfl := (by omega : a = 0 ∨ a = 1 ∨ a = 2)
    all_goals simp only [wc0, wc1, wc2, wc3]
    all_goals generalize Lib.Slots.finish = F at *
    all_goals omega
  · simp only [regClk, ↓reduceIte] at *
    obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    · omega
    all_goals obtain rfl | rfl := (by omega : a = 0 ∨ a = 1)
    all_goals simp only [dc0, dc1, dc2, Epilogue.startTime]
    all_goals generalize Lib.Slots.finish = F at *
    all_goals omega

theorem band_state (data : Bool) {s : (thread Q L g).D} (tab : tableInv Q L g s)
    (ok : requestClean s) (role : if data then DataState s else WorkerState s)
    (le : requests s ≤ if data then 2 else 3) :
    (schedule Q L).time g s ≤ regClk data (requests s) ∧
    ((thread Q L g).pc s ∈ Lib.requestPcs → (schedule Q L).time g s = regClk data (requests s)) ∧
    ((thread Q L g).pc s ∉ Lib.requestPcs →
      (schedule Q L).time g s < regClk data (requests s)) := by
  cases data
  · exact worker_upper s tab ok role le
  · exact data_upper s tab ok role le

/-- **After a register request the lane is at a later clock**, or its machine has stopped. -/
private theorem reg_after (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {pc inc n inst}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (nu : Frame.NoUbBefore X g k)
    {d : ((schedule Q L).code g).D} (hd : Frame.stateAt (schedule Q L).code X g k = some (some d)) :
    (∃ d', Frame.stateAt (schedule Q L).code X g (k + 1) = some (some d') ∧
      (schedule Q L).time g d < (schedule Q L).time g d') ∨
      Frame.stateAt (schedule Q L).code X g (k + 1) = none := by
  have hg := Frame.lt_of_get hX he
  have hs : Frame.stateAt (thread Q L) X g k = some (some d) := hd
  obtain ⟨tab, ok, mem, le, ds, ws⟩ := request_at hp hX hf words he nu hs
  have ev : (X.tr g)[k]? = some ⟨pc, .setMaxReg inc n inst⟩ := he
  have next : Frame.stateAt (thread Q L) X g (k + 1) =
      (thread Q L g).next d ⟨pc, .setMaxReg inc n inst⟩ := by
    rw [Frame.stateAt_succ ev, hs]; rfl
  show _ ∨ Frame.stateAt (thread Q L) X g (k + 1) = none
  rcases hn : (thread Q L g).next d ⟨pc, .setMaxReg inc n inst⟩ with _ | _ | d'
  · exact .inr (next.trans hn)
  · exact ((hf g hg (k + 1)).1 (next.trans hn)).elim
  refine .inl ⟨d', next.trans hn, ?_⟩
  have hk1 : k + 1 ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp ev).1
  have hs' : Frame.stateAt (thread Q L) X g (k + 1) = some (some d') := next.trans hn
  have nu' := noub_succ nu he (fun _ => nofun)
  obtain ⟨tab', ok', -⟩ := live_state hp hX hf words hg hk1 nu' hs'
  have step := request_step ok hn
  simp only [mem, ↓reduceIte] at step
  obtain ⟨-, lo⟩ := lane_state hp hX hk1 hs'
  obtain ⟨dlo, -⟩ := lane_state hp hX hk1 hs'
  by_cases low : g % L.block < 128
  · have a := (data_upper d tab ok (ds low) (by simpa [low] using le)).2.1 mem
    have b := data_lower d' tab' ok' (dlo low) step
    rw [a]; exact b
  · have high : 128 ≤ g % L.block := by omega
    have a := (worker_upper d tab ok (ws high) (by simpa [low] using le)).2.1 mem
    have b := worker_lower d' tab' ok' (lo high) step (by simp [low] at le; omega)
    rw [a]; exact b
/-- **A warp-mate with no request of the ordinal is no later than the request's site.** -/
private theorem reg_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {h pc inc n inst}
    (hh : h < L.threads) (hw : SameWarp L g h)
    (noord : ∀ j pc' inc' n' inst', X.get (h, j) = some ⟨pc', .setMaxReg inc' n' inst'⟩ →
      SetMaxNReg.ordinal X (h, j) ≠ SetMaxNReg.ordinal X (g, k))
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (nu : Frame.NoUbBefore X g k)
    (nuh : Frame.NoUbBefore X h (X.tr h).length)
    {d : ((schedule Q L).code g).D} (hd : Frame.stateAt (schedule Q L).code X g k = some (some d)) :
    Sched.threadTime (schedule Q L) X h ≤ (schedule Q L).time g d := by
  have hg := Frame.lt_of_get hX he
  have hs : Frame.stateAt (thread Q L) X g k = some (some d) := hd
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨tab, ok, mem, le, ds, ws⟩ := request_at hp hX hf words he nu hs
  obtain ⟨-, -, cnt⟩ := live_state hp hX hf words hg hk nu hs
  have warp : g % L.block / 32 = h % L.block / 32 := hw.2
  let data : Bool := decide (g % L.block < 128)
  have roleOf : ∀ {j} {t : (thread Q L h).D}, j ≤ (X.tr h).length →
      Frame.stateAt (thread Q L) X h j = some (some t) →
      if data then DataState t else WorkerState t := by
    intro j t hj hts
    obtain ⟨a, b⟩ := lane_state hp hX hj hts
    by_cases low : g % L.block < 128
    · simp only [data, low, decide_true, ↓reduceIte]; exact a (by omega)
    · simp only [data, low, decide_false, Bool.false_eq_true, ↓reduceIte]; exact b (by omega)
  have role : if data then DataState d else WorkerState d := by
    by_cases low : g % L.block < 128
    · simp only [data, low, decide_true, ↓reduceIte]; exact ds low
    · simp only [data, low, decide_false, Bool.false_eq_true, ↓reduceIte]; exact ws (by omega)
  have le' : requests d ≤ if data then 2 else 3 := by
    by_cases low : g % L.block < 128 <;> simpa [data, low] using le
  obtain ⟨-, eqd, -⟩ := band_state data tab ok role le'
  have hdt : (schedule Q L).time g d = regClk data (requests d) := eqd mem
  have hcle : (X.tr h).countP SetMaxNReg.isRequest ≤ requests d := by
    by_contra big
    obtain ⟨j, pc', inc', n', inst', hj, ho⟩ := request_ordinal (X := X) (h := h) (r := requests d)
      (by omega)
    exact noord j pc' inc' n' inst' hj (by rw [ho]; exact cnt.symm)
  have mono : ∀ a, a ≤ requests d → regClk data a ≤ regClk data (requests d) := by
    intro a ha
    rcases Nat.lt_or_ge a (requests d) with lt | ge
    · exact (regClk_lt lt le').le
    · rw [show a = requests d by omega]
  rw [← hdt] at mono
  unfold Sched.threadTime
  rcases hend : Frame.stateAt (schedule Q L).code X h (X.tr h).length with _ | _ | t
  · rcases hprev : Frame.stateAt (schedule Q L).code X h ((X.tr h).length - 1) with _ | _ | t
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    have hts : Frame.stateAt (thread Q L) X h ((X.tr h).length - 1) = some (some t) := hprev
    have hlen : 0 < (X.tr h).length := by
      by_contra z
      have z0 : (X.tr h).length = 0 := by omega
      rw [z0, Frame.stateAt_zero] at hend
      cases hend
    have hl1 : (X.tr h).length - 1 < (X.tr h).length := by omega
    have ev := List.getElem?_eq_getElem (l := X.tr h) (i := (X.tr h).length - 1) hl1
    have clear := nuh _ hl1 _ ev
    have nu1 : Frame.NoUbBefore X h ((X.tr h).length - 1) := fun j hj => nuh j (by omega)
    obtain ⟨tab', ok', cnt'⟩ := live_state hp hX hf words hh (by omega) nu1 hts
    obtain ⟨_, ins, _, _, _, hc, fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX ev
      hts clear
    have hq := (Lib.request_fires hc fire).1
    have whole : ((X.tr h).take ((X.tr h).length - 1)).countP SetMaxNReg.isRequest ≤
        (X.tr h).countP SetMaxNReg.isRequest := (List.take_sublist _ _).countP_le
    have role' := roleOf (j := (X.tr h).length - 1) (by omega) hts
    have bs := band_state data tab' ok' role' (by omega)
    show (schedule Q L).time h t + 1 ≤ (schedule Q L).time g d
    by_cases hit : (thread Q L h).pc t ∈ Lib.requestPcs
    · have hreq : SetMaxNReg.isRequest ((X.tr h)[(X.tr h).length - 1]) = true := by
        rw [hq]; exact decide_eq_true hit
      have step : (X.tr h).countP SetMaxNReg.isRequest =
          ((X.tr h).take ((X.tr h).length - 1)).countP SetMaxNReg.isRequest + 1 := by
        have tk := List.take_add_one (l := X.tr h) (i := (X.tr h).length - 1)
        rw [show (X.tr h).length - 1 + 1 = (X.tr h).length by omega, List.take_length, ev] at tk
        have := congrArg (List.countP SetMaxNReg.isRequest) tk
        rw [List.countP_append] at this
        simpa [hreq] using this
      have lt : requests t < requests d := by omega
      have := bs.1
      have := regClk_lt (data := data) lt le'
      omega
    · have := bs.2.2 hit
      have := mono (requests t) (by omega)
      omega
  · exact Nat.zero_le _
  · have hts : Frame.stateAt (thread Q L) X h (X.tr h).length = some (some t) := hend
    obtain ⟨tab', ok', cnt'⟩ := live_state hp hX hf words hh le_rfl nuh hts
    simp only [List.take_length] at cnt'
    have b := (band_state data tab' ok' (roleOf le_rfl hts) (by omega)).1
    exact b.trans (mono _ (by omega))

/-- An exit of a lane follows a request of every ordinal a warp-mate made. -/
private theorem reg_exit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {pc inc n inst} {h j pc' : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (hw : SameWarp L g h)
    (hx : X.get (h, j) = some ⟨pc', .exit⟩) :
    ∃ j' pc'' inc' n' inst', X.get (h, j') = some ⟨pc'', .setMaxReg inc' n' inst'⟩ ∧
      SetMaxNReg.ordinal X (h, j') = SetMaxNReg.ordinal X (g, k) := by
  obtain ⟨-, low, high⟩ := Export.request_pc hp hX hf words he
  obtain ⟨xlow, xhigh⟩ := Export.exit_requests hp hX hf words hx
  have warp : g % L.block / 32 = h % L.block / 32 := hw.2
  have whole : ((X.tr h).take j).countP SetMaxNReg.isRequest ≤
      (X.tr h).countP SetMaxNReg.isRequest := (List.take_sublist _ _).countP_le
  have bound : SetMaxNReg.ordinal X (g, k) < (X.tr h).countP SetMaxNReg.isRequest := by
    change ((X.tr g).take k).countP SetMaxNReg.isRequest < _
    by_cases d : g % L.block < 128
    · have := low d
      have := xlow (by omega)
      omega
    · have := high (by omega)
      have := xhigh (by omega)
      omega
  exact request_ordinal bound

/-- **A pending lane blocked at a register request steps.** -/
public theorem reg_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hw : Sched.RegWait L X g) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hnu := Sched.safe_noUb (hs.2 X hX)
  have nub : ∀ g k, Frame.NoUbBefore X g k := fun g k j _ e he f hf' => hnu ⟨(g, j), e.pc, f, by
    rw [he]; cases e; simp only at hf'; rw [hf']⟩
  have hb : L.block % 32 = 0 := by rw [hp.block]
  refine Sched.reg_stepsO (M := schedule Q L) (fun g hg => thread_sound hp hg) hs
    (fun h k hh => (hf h hh k).1) hb ?_ ?_ ?_ hmax hpd hrel hw
  · intro e pc n inst inc _ req h j pc' hw' hx
    exact reg_exit hp hX hf words (k := e.2) (g := e.1) req hw' hx
  · intro g h k pc n inst inc d hg hh hw' noord he hd
    exact reg_before hp hX hf words hh hw' noord he (nub g k) (nub h _) hd
  · intro g k pc n inst inc d hg he hd
    exact reg_after hp hX hf words he (nub g k) hd
end PTX.Kernels.InklingRelDecode.Proof
