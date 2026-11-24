-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
public import Lemmas.Flow.LoadShared
import Lemmas.Flow.Next
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

inductive StatsKind where
  | alpha | sum | maximum

/-- The rescale and final passes read the same per-row statistics buffers. -/
def statsPc (stage : Fin 2) : StatsKind → Nat
  | .alpha => if stage.val = 0 then 8007 else 8226
  | .sum => if stage.val = 0 then 8466 else 8762
  | .maximum => if stage.val = 0 then 8467 else 8763

def statsReg (stage : Fin 2) : StatsKind → Nat
  | .alpha => if stage.val = 0 then 1651 else 1652
  | .sum => if stage.val = 0 then 6512 else 1653
  | .maximum => if stage.val = 0 then 6513 else 1654

def statsOff (stage : Fin 2) : StatsKind → Nat
  | .alpha | .sum => 368 + 512 * stage.val
  | .maximum => 1392 + 512 * stage.val

def statsLoc (l : Launch) (g : Nat) (stage : Fin 2) (kind : StatsKind) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + 4 * rowOf l g + statsOff stage kind⟩

private def statsInstr (stage : Fin 2) (kind : StatsKind) : Instr :=
  { guard := none
    op := .mem {
      kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32
      addr := ⟨.reg 1627 32, statsOff stage kind⟩
      dsts := [some (statsReg stage kind)] } }

private theorem statsCode (stage : Fin 2) (kind : StatsKind) :
    kernel.code[statsPc stage kind]? = some (statsInstr stage kind) := by
  cases kind <;> fin_cases stage
  · exact Flow.code_8007
  · exact Flow.code_8226
  · exact Flow.code_8466
  · exact Flow.code_8762
  · exact Flow.code_8467
  · exact Flow.code_8763

private theorem statsModel {l : Launch} {g : Nat} {t : TState}
    (stage : Fin 2) (kind : StatsKind) (hPc : t.pc = statsPc stage kind) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hPc.symm ▸ statsCode stage kind) rfl
  all_goals
    rw [hPc]
    cases kind <;> fin_cases stage <;> decide

/-- A fired statistics load uses the correction lane's computed row address and word offset. -/
theorem statsReadAtRegister {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (stage : Fin 2) (kind : StatsKind) {g : Nat} {t : TState}
    (hPc : t.pc = statsPc stage kind)
    (hReg : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    {access : Acc} {bytes : List (Option Byte)} {o : Option TState}
    (he : EStep kernel Assumptions.all l g t ⟨statsPc stage kind, .rd access bytes⟩ o) :
    access = { loc := (statsLoc l g stage kind).at (4 * t.sub), size := 4, elem := t.sub } := by
  obtain ⟨tmpl, hOut, hFire⟩ := he
  rw [statsModel stage kind hPc] at hOut
  rw [hPc] at hFire
  rcases out_ev hOut with ⟨_, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rw [hPc, statsCode] at hc
  obtain rfl := Option.some.inj hc
  change Fires (statsPc stage kind)
    (loadTmpl [] l g t .shared false 32 [statsReg stage kind] 1627 (statsOff stage kind))
    ⟨statsPc stage kind, .rd access bytes⟩ o at hFire
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hOff : statsOff stage kind ≤ 1904 ∧ statsOff stage kind % 4 = 0 := by
    cases kind <;> fin_cases stage <;> decide
  have hSpan : l.sharedBase + 4 * rowOf l g + statsOff stage kind < 2 ^ 32 := by
    have := hp.shared.2.1
    omega
  have hAlign : (l.sharedBase + 4 * rowOf l g + statsOff stage kind) % 4 = 0 := by
    have := hp.shared.1
    omega
  simp only [loadTmpl, effAddr_b32_off hReg hSpan, bind, Except.bind, elemAcc,
    List.length_singleton, Nat.reduceDiv, hAlign, pure, Except.pure, Bool.false_eq_true,
    ite_false, Fires] at hFire
  obtain ⟨_, _, eq, _⟩ := hFire
  exact (Kind.rd.inj (congrArg Event.kind eq)).1

/-- A scalar statistics read can stay at its instruction only if reconstruction faults. -/
theorem statsStepSamePcFault {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (kind : StatsKind) (hs : s.pc = statsPc stage kind)
    (he : EStep kernel Assumptions.all l g s e (some u)) (hSame : u.pc = s.pc) :
    u.fault ≠ none := by
  obtain ⟨i,hCode,_,hFire⟩ := PTX.EventFrame.estep_event_source he
  rw [hs,statsCode] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨_,bs,_,rfl⟩ := fires_load rfl rfl hFire rfl
  cases hr : rebuild 3 bs with
  | error f => simp [afterLoad,hr]
  | ok v =>
    simp only [afterLoad, hr, MemAccess.regs] at hSame
    have hStop : ¬ s.sub + 1 < 1 := by omega
    simp [hStop] at hSame

/-- A returning scalar statistics read installs its actual bytes through the decoded load. -/
theorem statisticsReadStep {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (kind : StatsKind) (hs : s.pc = statsPc stage kind)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ access bytes, e = ⟨statsPc stage kind,.rd access bytes⟩ ∧
      u = afterLoad s [statsReg stage kind] bytes := by
  obtain ⟨i,hCode,_,hFire⟩ := PTX.EventFrame.estep_event_source he
  rw [hs,statsCode] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨access,bytes,hRead,hNext⟩ := fires_load rfl rfl hFire rfl
  exact ⟨access,bytes,hs ▸ hRead,hNext⟩

/-- Each correction statistics instruction at a live cursor reads exactly one FP32 word for
that thread's correction row. The returned bytes are the bytes carried by the actual event. -/
theorem observeStatsPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {o : Option TState}
    (hp : Pre p l m) (stage : Fin 2) (kind : StatsKind)
    (ht : At t (statsPc stage kind) [(1627, b32 (l.sharedBase + 4 * rowOf l g))])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    ∃ bs, X.get (g, pos) = some ⟨statsPc stage kind,
        .rd { loc := statsLoc l g stage kind, size := 4 } bs⟩ ∧
      Run kernel Assumptions.all l g (afterLoad t [statsReg stage kind] bs)
        ((X.tr g).drop (pos + 1)) o := by
  let address := l.sharedBase + 4 * rowOf l g
  let a : Acc := { loc := statsLoc l g stage kind, size := 4 }
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hOff : statsOff stage kind ≤ 1904 ∧ statsOff stage kind % 4 = 0 := by
    cases kind <;> fin_cases stage <;> decide
  have hRange : address + statsOff stage kind < 2 ^ 32 := by
    have hLim := hp.shared.2.1
    dsimp [address]
    omega
  have hAlign : (l.sharedBase + 4 * rowOf l g + statsOff stage kind) % 4 = 0 := by
    have hBase := hp.shared.1
    omega
  have hOut : out kernel Assumptions.all l g t =
      .ev (.read a (afterLoad t [statsReg stage kind])) := by
    rw [statsModel stage kind ht.1]
    unfold out
    rw [ht.1, ht.2.2.2.1, statsCode]
    change Out.ev (eventTmpl [] l g t (statsInstr stage kind).op) = _
    change Out.ev (loadTmpl [] l g t .shared false 32 [statsReg stage kind]
      1627 (statsOff stage kind)) = _
    simp [loadTmpl, effAddr_b32_off ht.2.2.2.2.1 hRange, bind, Except.bind, elemAcc, hAlign,
      ht.2.1, pure, Except.pure, a, statsLoc, Loc.at]
  have hn : Next kernel Assumptions.all l g t t (.read a (afterLoad t [statsReg stage kind])) :=
    ⟨.refl, hOut⟩
  obtain ⟨e, u, he, hFire, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  obtain ⟨bs, _, rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  exact ⟨bs, ht.1 ▸ he, hTail⟩

/-- Each correction statistics instruction at a live cursor reads exactly one FP32 word for
that thread's correction row. The returned bytes are the bytes carried by the actual event. -/
theorem observeStats {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} (hp : Pre p l m) (stage : Fin 2) (kind : StatsKind)
    (ht : At t (statsPc stage kind) [(1627, b32 (l.sharedBase + 4 * rowOf l g))])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ bs, X.get (g, pos) = some ⟨statsPc stage kind,
        .rd { loc := statsLoc l g stage kind, size := 4 } bs⟩ ∧
      Run kernel Assumptions.all l g (afterLoad t [statsReg stage kind] bs)
        ((X.tr g).drop (pos + 1)) none :=
  observeStatsPrefix hp stage kind ht hr (by intro h; rw [h] at hr; cases hr)

end
end PTX.Kernels.TmlFa4Fwd.Correction
