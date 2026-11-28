-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.Requests
public import Kernels.InklingRelDecode.Proof.Common.RequestPrefix
public import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Common.Export.RegLedger
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.RequestCount
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Lemmas.Step.CtaBarNamed
public import Kernels.InklingRelDecode.Proof.Lib.Slots

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- The states of the startup and of the data partition. -/
def DataState {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dispatch _ _),_⟩,_) => False
  | _ => True

/-- The states of the startup and of a worker. -/
def WorkerState {Q L g} : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue _),_⟩,_) => False
  | _ => True

def workClock (r : Nat) : Nat :=
  [30, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD r 0

theorem wc0 : workClock 0 = 30 := rfl
theorem wc1 : workClock 1 = 285 := rfl
theorem wc2 : workClock 2 = Lib.Slots.finish + 280 := rfl
theorem wc3 : workClock 3 = Lib.Slots.finish + 284 := rfl

theorem startup_site_pc (s : Startup.Site) (h : ∀ r, s ≠ .enter r) :
    s.pc ∉ Lib.requestPcs := by
  cases s <;> first | decide | exact absurd rfl (h _)

theorem startup_pc {Q L g} (st : Startup.D) (n : Cls → Nat)
    (tab : tableInv Q L g (.inl st, n)) : st.site.pc ∉ Lib.requestPcs := by
  have none := Code.gatedExit_none.mp tab.1.2
  apply startup_site_pc
  intro r hr
  simp [Startup.enterOf, hr] at none

theorem pro_not_exit {Q L g w} {d : Prologue.Control.D}
    (tab : tableInv Q L g (.inr ⟨.inl (.prologue w), .inl d⟩, n)) : d.site ≠ .exit := by
  intro e
  have h := tab.1.2
  simp [dataExit, e] at h

theorem pro_hit (s : Prologue.Site) : s.pc ∈ Lib.requestPcs ↔ s = .sMax ∨ s = .exit := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem soft_hit (s : Softmax.Site) : s.pc ∈ Lib.requestPcs ↔ s = .setMaxReg := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

theorem epi_hit (s : Epilogue.Site) : s.pc ∈ Lib.requestPcs ↔ s = .setMax := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

theorem loader_phase (d : Loader.D) :
    1 ≤ Loader.requestPhase d.site ∧ Loader.requestPhase d.site ≤ 3 := by
  unfold Loader.requestPhase; split <;> omega

theorem mma_phase (d : Mma.D) :
    1 ≤ Mma.requestPhase d.site ∧ Mma.requestPhase d.site ≤ 3 := by
  unfold Mma.requestPhase; split <;> omega

theorem worker_pick {t p : Nat}
    (b1 : p = 1 → t = 285) (b2 : p = 2 → 285 < t ∧ t ≤ Lib.Slots.finish + 280)
    (b3 : p = 3 → t = Lib.Slots.finish + 284) (h : 1 ≤ p) (h3 : p ≤ 3) :
    t ≤ workClock p ∧ workClock (p - 1) < t := by
  have big : 285 < Lib.Slots.finish := by decide +kernel
  obtain rfl | rfl | rfl : p = 1 ∨ p = 2 ∨ p = 3 := by omega
  · have := b1 rfl
    rw [Nat.sub_self, wc1, wc0]
    omega
  · obtain ⟨l, u⟩ := b2 rfl
    rw [wc2, show 2 - 1 = 1 from rfl, wc1]
    exact ⟨u, l⟩
  · have := b3 rfl
    rw [wc3, show 3 - 1 = 2 from rfl, wc2]
    generalize Lib.Slots.finish = F at *
    omega

theorem worker_eq {t p : Nat} (h3 : p ≤ 3) (h : 1 ≤ p)
    (e : t = [0, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD p 0) :
    t = workClock p := by
  obtain rfl | rfl | rfl : p = 1 ∨ p = 2 ∨ p = 3 := by omega
  all_goals exact e
variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem live_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (nu : Frame.NoUbBefore X g k) {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g k = some (some s)) :
    tableInv Q L g s ∧ requestClean s ∧
      ((X.tr g).take k).countP SetMaxNReg.isRequest = requests s := by
  obtain ⟨count, ok⟩ := request_prefix hp hX words hk nu hs
  exact ⟨reached_table hf hg nu hs, ok, count⟩

theorem lane_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hk : k ≤ (X.tr g).length) {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g k = some (some s)) :
    (g % L.block < 128 → DataState s) ∧ (128 ≤ g % L.block → WorkerState s) := by
  obtain ⟨s0, n⟩ := s
  rcases s0 with st | ⟨r, d⟩
  · exact ⟨fun _ => trivial, fun _ => trivial⟩
  rcases r with r | r
  · cases r with
    | prologue w =>
      have := data_warp hp hX hk hs
      exact ⟨fun _ => trivial, fun h => by omega⟩
    | dispatch w x =>
      have := (worker_warp hp hX hk hs).1
      exact ⟨fun h => by omega, fun _ => trivial⟩
  · exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem request_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {pc inc n inst}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) (nu : Frame.NoUbBefore X g k)
    {d : (thread Q L g).D} (hs : Frame.stateAt (thread Q L) X g k = some (some d)) :
    tableInv Q L g d ∧ requestClean d ∧ (thread Q L g).pc d ∈ Lib.requestPcs ∧
      requests d ≤ (if g % L.block < 128 then 2 else 3) ∧
      (g % L.block < 128 → DataState d) ∧ (128 ≤ g % L.block → WorkerState d) := by
  have hg := Frame.lt_of_get hX he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨tab, ok, cnt⟩ := live_state hp hX hf words hg hk nu hs
  have pcs := Frame.event_pcU (fun g h => thread_sound hp h) hX he hs (by simp)
  obtain ⟨-, low, high⟩ := Export.request_pc hp hX hf words he
  have mem : pc ∈ Lib.requestPcs := by
    rcases Export.request_group hp hX hf words he with ⟨-, d⟩ | ⟨-, d⟩
    exacts [Lib.dataReq_mem d, Lib.workerReq_mem d]
  refine ⟨tab, ok, by rw [← pcs]; exact mem, ?_, (lane_state hp hX hk hs).1,
    (lane_state hp hX hk hs).2⟩
  rw [← cnt]
  split
  · exact low (by assumption)
  · exact high (by omega)
theorem noub_succ {e : Event} (nu : Frame.NoUbBefore X g k) (he : X.get (g, k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) : Frame.NoUbBefore X g (k + 1) := by
  intro j hj ev hev f hf
  by_cases h : j = k
  · subst h
    rw [he] at hev
    cases hev
    exact hu f hf
  · exact nu j (by omega) ev hev f hf

theorem request_ordinal {h : Nat} {r : Nat} (hr : r < (X.tr h).countP SetMaxNReg.isRequest) :
    ∃ j pc inc n inst, X.get (h, j) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
      SetMaxNReg.ordinal X (h, j) = r := by
  obtain ⟨j, ⟨pc, kd⟩, hj, hq, hc⟩ := NamedBar.exists_ordinal SetMaxNReg.isRequest (X.tr h) hr
  obtain ⟨inc, n, inst, rfl⟩ := isRequest_kind hq
  exact ⟨j, pc, inc, n, inst, hj, hc⟩

end PTX.Kernels.InklingRelDecode.Proof
