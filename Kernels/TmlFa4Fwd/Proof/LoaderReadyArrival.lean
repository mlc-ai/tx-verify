-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyBarriers
public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem recurringReadyFrame (i : Fin 4) :
    let lower := (recurringEmptyWait i).pc + 3
    let stop := copyCommitPc (recurringPacketSite i) + 2
    ((kernel.code.drop lower).take (stop - lower)).all
      (fun ins => loaderPipelineCutOp lower stop (stop - 1)
        [(copyArrivalAddress (recurringPacketSite i)).1] ins.op) = true := by
  fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- An observed arrival in the recurring packet following a successful empty
acquire names that same slot's initialized ready mbarrier. The audited slice
includes the pointer retries, the 32 copies, the commit and the arrival. -/
theorem recurringReadyArrivalFromBase {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g scope : Nat} (i : Fin 4) (stage : Fin 3) {t : TState}
    {events : List Event} {visits : List Visit} {loc : Loc}
    (hScope : scope ≤ (recurringEmptyWait i).pc + 3)
    (ht : At t ((recurringEmptyWait i).pc + 3)
      [((copyArrivalAddress (recurringPacketSite i)).1, b32 (l.sharedBase + 8 * stage.val))])
    (hw : Walk kernel Assumptions.all l g t events visits)
    (hSeen : ⟨copyCommitPc (recurringPacketSite i) + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents scope
        (copyCommitPc (recurringPacketSite i) + 2) visits) :
    loc = Prologue.initObject l (g / l.block) (readySlot stage) := by
  let site := recurringPacketSite i
  let reg := (copyArrivalAddress site).1
  let base := l.sharedBase + 8 * stage.val
  let lower := (recurringEmptyWait i).pc + 3
  let stop := copyCommitPc site + 2
  let e : Event := ⟨copyCommitPc site + 1, .asyncArrive loc true⟩
  have hLo : 174 ≤ lower := by fin_cases i <;> decide
  have hStop : stop ≤ 1901 := by fin_cases i <;> decide
  have hAt : lower ≤ t.pc := by rw [ht.1]
  have hShape : RingShape t := by simp [RingShape, loaderSubShape, ht.2.1, ht.2.2.1]
  have hFrame : Holds t.regs [(reg, b32 base)] := ht.2.2.2.2
  obtain ⟨s, _, hPc, hReg, hStep⟩ :=
    loaderEventWithRegisters (e := e) (lower := lower) (stop := stop)
      (F := [(reg, b32 base)]) hScope hLo hStop
      (recurringReadyFrame i) hw hAt hShape hFrame hSeen (by simp [Ends, e])
  have hOff : (copyArrivalAddress site).2 = 32 := by fin_cases i <;> decide
  have hBound : base + (copyArrivalAddress site).2 < 2 ^ 32 := by
    have := hp.shared.2.1
    have := stage.isLt
    rw [hOff]
    dsimp [base]
    omega
  have hAlign : (base + (copyArrivalAddress site).2) % 8 = 0 := by
    have := hp.shared.1
    rw [hOff]
    dsimp [base]
    omega
  let ready : Loc := Prologue.initObject l (g / l.block) (readySlot stage)
  have hEff : mbarLoc l g s (copyArrivalAddress site).1 (copyArrivalAddress site).2 =
      .ok ready := by
    have hr := holds_mem hReg (by simp : (reg, b32 base) ∈ [(reg, b32 base)])
    unfold mbarLoc
    rw [effAddr_b32_off hr hBound]
    rw [hOff] at hAlign ⊢
    simp [ready, readySlot_address, base, hAlign, bind, Except.bind, pure, Except.pure]
  obtain ⟨tmpl, hout, hFire⟩ := hStep
  have hf : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp only [out, h, Out.ev.injEq] at hout
      subst tmpl
      simp [Fires, e] at hFire
  have hc : kernel.code[s.pc]? = some
      ⟨none, .cpAsyncArrive true (copyArrivalAddress site).1
        (copyArrivalAddress site).2 false⟩ := by
    rw [hPc]
    exact (copyCommitCode site).2
  have hHere : e.pc < 1901 := by dsimp [e, stop] at *; omega
  have hStart : 174 ≤ copyCommitPc site + 1 := by fin_cases i <;> decide
  change s.pc = copyCommitPc site + 1 at hPc
  rw [loaderOutCore (by omega) (by omega), out_event hf hc rfl rfl] at hout
  change Out.ev (cpAsyncTmpl l g s
    (.cpAsyncArrive true (copyArrivalAddress site).1 (copyArrivalAddress site).2 false)) =
    .ev tmpl at hout
  rw [cpAsyncTmpl_arrive_noinc hEff] at hout
  obtain rfl := Out.ev.inj hout
  exact (Kind.asyncArrive.inj (Event.mk.inj hFire.1).2).1

/-- An observed arrival in the recurring packet following a successful empty
acquire names that same slot's initialized ready mbarrier. The audited slice
includes the pointer retries, the 32 copies, the commit and the arrival. -/
theorem recurringReadyArrivalInSlice {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g phase scope : Nat} (i : Fin 4) (stage : Fin 3) {t : TState}
    {events : List Event} {visits : List Visit} {loc : Loc}
    (hScope : scope ≤ (recurringEmptyWait i).pc + 3)
    (ht : At t ((recurringEmptyWait i).pc + 3) (recurringBarrierFacts l i stage phase))
    (hw : Walk kernel Assumptions.all l g t events visits)
    (hSeen : ⟨copyCommitPc (recurringPacketSite i) + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents scope
        (copyCommitPc (recurringPacketSite i) + 2) visits) :
    loc = Prologue.initObject l (g / l.block) (readySlot stage) := by
  exact recurringReadyArrivalFromBase hp i stage hScope
    (ht.mono ⟨ht.2.2.2.2.2.2.1, trivial⟩) hw hSeen

end
end PTX.Kernels.TmlFa4Fwd.Loader
