-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxStartup
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
public import Kernels.TmlFa4Fwd.Flow.Code.Part055
public import Kernels.TmlFa4Fwd.Flow.Code.Part056
public import Kernels.TmlFa4Fwd.Flow.Code.Part068
public import Kernels.TmlFa4Fwd.Flow.Code.Part075
public import Kernels.TmlFa4Fwd.Flow.Code.Part076
public import Kernels.TmlFa4Fwd.Flow.Code.Part082
public import Kernels.TmlFa4Fwd.Flow.Code.Part088
public import Kernels.TmlFa4Fwd.Flow.Code.Part102
public import Kernels.TmlFa4Fwd.Flow.Code.Part107
public import Kernels.TmlFa4Fwd.Flow.Code.Part116
public import Kernels.TmlFa4Fwd.Flow.Code.Part119
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.BarArrival
import Lemmas.Step.DrainInOrder
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

structure SignalSite where
  pc : Nat
  base : Nat
  count : Nat
  state : Nat
  offset : Nat

/-- Bias-empty, first P publication and P-tail publication, in decoded instruction order. -/
def signalSite (i : Fin 8) : SignalSite := (#v[
  ⟨3590, 3077, 3078, 7894, 336⟩, ⟨4847, 3217, 3927, 8186, 96⟩,
  ⟨4867, 3946, 3947, 8187, 112⟩, ⟨5278, 4237, 4238, 8315, 336⟩,
  ⟨6532, 5097, 5098, 8603, 96⟩, ⟨6552, 5117, 5118, 8604, 112⟩,
  ⟨7437, 5187, 5781, 8850, 96⟩, ⟨7457, 5800, 5801, 8851, 112⟩] : Vector SignalSite 8)[i]

private theorem signalCode (i : Fin 8) : kernel.code[(signalSite i).pc]? =
    some ⟨none, .mbarArrive (signalSite i).base (signalSite i).offset (.imm 0)
      (.reg (signalSite i).count) false true .cta (some (signalSite i).state)⟩ := by
  fin_cases i
  · exact Flow.code_3590
  · exact Flow.code_4847
  · exact Flow.code_4867
  · exact Flow.code_5278
  · exact Flow.code_6532
  · exact Flow.code_6552
  · exact Flow.code_7437
  · exact Flow.code_7457

def signalLoc (l : Launch) (g : Nat) (stage : Fin 2) (i : Fin 8) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + 8 * stage.val + (signalSite i).offset⟩

variable {p : Params} {l : Launch} {m : Mem0}

private theorem signalLoc_ok (hp : Pre p l m) {g : Nat} {t : TState} (stage : Fin 2) (i : Fin 8)
    (hr : t.regs (signalSite i).base = some (b32 (l.sharedBase + 8 * stage.val))) :
    mbarLoc l g t (signalSite i).base (signalSite i).offset = .ok (signalLoc l g stage i) := by
  let a := l.sharedBase + 8 * stage.val
  let off := (signalSite i).offset
  have hOff : off ≤ 336 ∧ off % 8 = 0 := by fin_cases i <;> decide
  have hBase := hp.shared.2.1
  have hStage := stage.isLt
  change t.regs (signalSite i).base = some (b32 a) at hr
  have ha : a < 2 ^ 32 := by dsimp [a]; omega
  have hSum : a + off < 2 ^ 32 := by dsimp [a]; omega
  have hAl := hp.shared.1
  have hAlign : (a + off) % 8 = 0 := by dsimp [a]; omega
  have hEff : sharedEffAddr l g t false (signalSite i).base off =
      .ok ⟨.shared, g / l.block, a + off⟩ := by
    simp only [sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat ha (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      truncBits_ofNat hSum (by decide), BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show a + off < 2 ^ 64 by omega)]
  change mbarLoc l g t (signalSite i).base off = .ok (signalLoc l g stage i)
  simp [mbarLoc, effAddr, hEff, hAlign, bind, Except.bind, pure, Except.pure, signalLoc, a, off]

/-- A decoded Bias or probability arrival requests one unit on its stage object. -/
theorem signalTemplate (hp : Pre p l m) (stage : Fin 2) (i : Fin 8) {g : Nat} {t : TState}
    (hpc : t.pc = (signalSite i).pc) (hf : t.fault = none)
    (hr : t.regs (signalSite i).base = some (b32 (l.sharedBase + 8 * stage.val)))
    (hc : t.regs (signalSite i).count = some (b32 1)) :
    out kernel Assumptions.all l g t =
      .ev (.arrive (signalLoc l g stage i) 0 (next (mbarStateDest t (some (signalSite i).state)))
        1 true .cta) := by
  let u := next (mbarStateDest t (some (signalSite i).state))
  have hCode := signalCode i
  rw [← hpc] at hCode
  have hLoc := signalLoc_ok hp (g := g) stage i hr
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  have hZero : readBits l g t 32 (.imm 0) = .ok 0#64 := rfl
  change out kernel Assumptions.all l g t = .ev (.arrive (signalLoc l g stage i) 0 u 1 true .cta)
  rw [out_event hf hCode rfl rfl]
  simp [eventTmpl, widenMbarScope, hScope, tmaTmpl, hLoc, readBits_b32 hc (by decide),
    hZero, bind, Except.bind, pure, Except.pure, ofExec, u]

/-- The softmax lane's notification of the Bias or P ring is the actual CTA release on the
corresponding stage's shared object. Its instruction clears the unused arrival state destination. -/
theorem signalTrace {X : Execution} (hp : Pre p l m) (stage : Fin 2) (i : Fin 8) {g j : Nat}
    {t : TState} (hpc : t.pc = (signalSite i).pc) (hf : t.fault = none)
    (hr : t.regs (signalSite i).base = some (b32 (l.sharedBase + 8 * stage.val)))
    (hc : t.regs (signalSite i).count = some (b32 1))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    X.get (g, j) = some ⟨(signalSite i).pc, .arrive (signalLoc l g stage i) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g (next (mbarStateDest t (some (signalSite i).state)))
        ((X.tr g).drop (j + 1)) none := by
  let u := next (mbarStateDest t (some (signalSite i).state))
  have ho := signalTemplate hp stage i (g := g) hpc hf hr hc
  have hn : Next kernel Assumptions.all l g t t
      (.arrive (signalLoc l g stage i) 0 u 1 true .cta) := ⟨.refl, ho⟩
  obtain ⟨e, v, he, ⟨rfl, hV⟩, hTail⟩ := hn.continuing_at (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hRun
  obtain rfl := Option.some.inj hV
  exact ⟨by simpa only [hpc] using he, hTail⟩

/-- The actual signal is determined even if the observed lane is still active. -/
theorem signalTraceInPrefix {X : Execution} (hp : Pre p l m) (stage : Fin 2) (i : Fin 8) {g j : Nat}
    {t : TState} {ending : Option TState} (hpc : t.pc = (signalSite i).pc) (hf : t.fault = none)
    (hr : t.regs (signalSite i).base = some (b32 (l.sharedBase + 8 * stage.val)))
    (hc : t.regs (signalSite i).count = some (b32 1))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending) (hj : j < (X.tr g).length) :
    X.get (g,j) = some ⟨(signalSite i).pc,.arrive (signalLoc l g stage i) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g (next (mbarStateDest t (some (signalSite i).state)))
        ((X.tr g).drop (j+1)) ending := by
  let u := next (mbarStateDest t (some (signalSite i).state))
  have hn : Next kernel Assumptions.all l g t t (.arrive (signalLoc l g stage i) 0 u 1 true .cta) :=
    ⟨.refl,signalTemplate hp stage i (g := g) hpc hf hr hc⟩
  rw [List.drop_eq_getElem_cons hj] at hRun
  obtain ⟨_,⟨he,hReturned⟩,hTail⟩ := hn.continuing_event
    (by rintro ⟨_,hBad⟩; cases hBad) hRun
  obtain rfl := Option.some.inj hReturned
  refine ⟨?_,hTail⟩
  change (X.tr g)[j]? = _
  rw [List.getElem?_eq_getElem hj,he,hpc]

/-- The per-warp statistics handoff has one notification per computation plus the final sum/max. -/
def statsPc (iteration : Option Round) : Nat :=
  match iteration with
  | some .first => 4397
  | some .biased => 5683
  | some .unbiased => 6891
  | none => 7616

private theorem statsCode (iteration : Option Round) :
    kernel.code[statsPc iteration]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases iteration with
  | none => exact Flow.code_7616
  | some round =>
    cases round
    · exact Flow.code_4397
    · exact Flow.code_5683
    · exact Flow.code_6891

private theorem takeBarPrefix {l : Launch} {X : Execution} {g j id n : Nat} {t : TState}
    {mode : BarMode} {o : Option TState}
    (ho : out kernel Assumptions.all l g t = .ev (.bar id (next t) (some n) mode))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o) (hMore : (X.tr g).drop j ≠ []) :
    X.get (g, j) = some ⟨t.pc, .bar id (some n) mode⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) o := by
  have hn : Next kernel Assumptions.all l g t t (.bar id (next t) (some n) mode) := ⟨.refl, ho⟩
  obtain ⟨e, v, he, ⟨rfl, hV⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hRun hMore
  obtain rfl := Option.some.inj hV
  exact ⟨he, hTail⟩

theorem statsTemplate {l : Launch} (hb : l.block = 512)
    (round : Option Round) (warp : Fin 8) {g : Nat} {t : TState}
    (hpc : t.pc = statsPc round) (hf : t.fault = none)
    (hr : t.regs 5127 = some (b32 (3 + warp.val))) :
    out kernel Assumptions.all l g t =
      .ev (.bar (3 + warp.val) (next t) (some 64) .arrive) := by
  have hCode := statsCode round
  rw [← hpc] at hCode
  have hw := warp.isLt
  have hid : 3 + warp.val < 16 := by omega
  have hId32 : 3 + warp.val < 2 ^ 32 := by omega
  have hId64 : 3 + warp.val < 18446744073709551616 := by omega
  have hImm : readBits l g t 32 (.imm 64) = .ok 64#64 := rfl
  rw [out_event hf hCode rfl rfl]
  simp [eventTmpl, barTmpl, readBits_b32 hr hId32, hImm, hb, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hId64, Nat.not_le_of_lt hid]

/-- An actual softmax statistics notification rendezvouses with the matching correction warp. -/
theorem statsTracePrefix {l : Launch} {X : Execution} (hb : l.block = 512)
    (round : Option Round) (warp : Fin 8) {g j : Nat} {t : TState}
    (hpc : t.pc = statsPc round) (hf : t.fault = none)
    (hr : t.regs 5127 = some (b32 (3 + warp.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o) (hMore : (X.tr g).drop j ≠ []) :
    X.get (g, j) = some ⟨statsPc round, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) o := by
  have ho := statsTemplate (g := g) hb round warp hpc hf hr
  simpa only [hpc] using takeBarPrefix ho hRun hMore

/-- A lane with a runnable statistics publication records its named arrival in a maximal trace. -/
theorem statsArrivalOfMaximal {X : Execution} (hp : Pre p l m) (round : Option Round) (warp : Fin 8)
    {g j : Nat} {t v : TState} {o : Option TState} (hg : g < l.threads) (hPos : 0 < j)
    (hBound : j ≤ (X.tr g).length) (hAt : At v (statsPc round) [(5127,b32 (3+warp.val))])
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hRelease : j = (X.tr g).length → ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ Step.Released l Y g) :
    X.get (g,j) = some ⟨statsPc round,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some (next v)) ∧
      Run kernel Assumptions.all l g (next v) ((X.tr g).drop (j+1)) o := by
  have hOut := statsTemplate (g := g) hp.block round warp hAt.1 hAt.2.2.2.1 hAt.2.2.2.2.1
  let e := Event.mk v.pc (.bar (3+warp.val) (some 64) .arrive)
  have hStep : EStep kernel Assumptions.all l g v e (some (next v)) := ⟨_,hOut,rfl,rfl⟩
  have hLt : j < (X.tr g).length := by
    by_contra! hShort
    obtain ⟨Y,hY,hTr,hRel⟩ := hRelease (Nat.le_antisymm hBound hShort)
    have hStarted : Y.tr g ≠ [] := by
      intro hNil
      have hLen : (X.tr g).length = 0 := by rw [← hTr,hNil,List.length_nil]
      omega
    have hBefore : Run kernel Assumptions.all l g {} (Y.tr g) (some t) := by
      rw [hTr]
      simpa only [List.take_of_length_le hShort] using hPast
    exact hY.not_grows (Step.barArrival_counted_extension hY.1 hg (.inl hStarted) hRel
      (Assumptions.wfStep.quiet hY.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hBefore hLocal hStep)
  have hMore : (X.tr g).drop j ≠ [] :=
    fun hn => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hn)
  obtain ⟨he,hTail⟩ := takeBarPrefix hOut (hRun.after_local_nonempty hLocal hMore) hMore
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some (next v)) := by
    rw [List.take_add_one,show (X.tr g)[j]? = some e from he]
    exact hPast.snoc hLocal hStep
  exact ⟨hAt.1 ▸ he,hPrefix,hTail⟩

/-- An actual softmax statistics notification rendezvouses with the matching correction warp. -/
theorem statsTrace {l : Launch} {X : Execution} (hb : l.block = 512)
    (round : Option Round) (warp : Fin 8) {g j : Nat} {t : TState}
    (hpc : t.pc = statsPc round) (hf : t.fault = none)
    (hr : t.regs 5127 = some (b32 (3 + warp.val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    X.get (g, j) = some ⟨statsPc round, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (j + 1)) none :=
  statsTracePrefix hb round warp hpc hf hr hRun (by intro h; rw [h] at hRun; cases hRun)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
