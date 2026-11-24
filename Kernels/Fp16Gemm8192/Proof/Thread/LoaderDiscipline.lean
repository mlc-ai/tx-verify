-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueOps
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderEvents
public import Lemmas.Flow.Polls
public import Lemmas.Flow.TraceInduction

@[expose] public section

/-! # The loader's polls of the empty barriers

A loader thread polls slot `s`'s empty barrier in its CTA twice per trip (blocks `s` and
`s + 4`) and once in the drain. Along its run, the number of its successful polls on that
barrier, modulo 2, is a function of its abstract state (`polled`); so every poll is made
with the parity `(successful polls so far + 1) % 2`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Loader

def drainBase : Fin 4 → Nat
  | 0 => 827 | 1 => 830 | 2 => 831 | 3 => 832

theorem code_drain_ops : ∀ i : Fin 4, kernel.code[(Site.drain i).pc]? =
    some ⟨none, .mbarWait (taskPred (.drain i)) (drainBase i) 0 (.reg 828) true .cta⟩
  | 0 => Flow.code_mbarWait_9 | 1 => Flow.code_mbarWait_10 | 2 => Flow.code_mbarWait_11
  | 3 => Flow.code_mbarWait_12

theorem drainBase_live : ∀ i : Fin 4, drainBase i ∈ Flow.live (Site.drain i).pc := by
  intro i
  fin_cases i <;> table_decide

theorem drainPar_live : ∀ i : Fin 4, 828 ∈ Flow.live (Site.drain i).pc := by
  intro i
  fin_cases i <;> table_decide

theorem drainBase_value (L : Launch) (g : Nat) (d : D) (i : Fin 4) :
    valueOf L g d (drainBase i) = b32 (L.sharedBase + 40 + 8 * i.val) := by
  fin_cases i <;> simp only [drainBase] <;> loader_values

/-- The drain's poll of slot `i` names slot `i`'s empty barrier in the loader's CTA with
parity 1. -/
theorem drain_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o :
    Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (i : Fin 4)
    (hs : d.site = .drain i) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (InputRing.emptyLoc L (g / L.block) i) 1 ok acq sc⟩ := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  rw [code_drain_ops i] at hc
  cases hc
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hb := (drainBase_value L g _ i) ▸ holds_mem h.2.2.2.2 (Flow.mem_factsFrom (drainBase_live i))
  have hp : t.regs 828 = some (b32 1) :=
    (show valueOf L g ⟨.drain i, m, n, q, cp, r, x⟩ 828 = b32 1 by loader_values) ▸
      holds_mem h.2.2.2.2 (Flow.mem_factsFrom (drainPar_live i))
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 828) = .ok (truncBits 32 (BitVec.ofNat 64 1)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  exact ⟨ok, acq, sc, by rw [he]; rfl⟩

/-- The task's CLC poll names the CTA's CLC barrier. -/
theorem clcWait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o :
    Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcWait)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ p ok acq sc, p % 2 = d.cp % 2 ∧
      e = ⟨d.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩ := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
  have hb : t.regs 812 = some (b32 (L.sharedBase + 104)) :=
    (show valueOf L g ⟨.clcWait, m, n, q, cp, r, x⟩ 812 = b32 (L.sharedBase + 104) by
      loader_values) ▸ holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 812 ∈ Flow.live Site.clcWait.pc by table_decide))
  have hp : t.regs 876 = some (b32 cp) :=
    (show valueOf L g ⟨.clcWait, m, n, q, cp, r, x⟩ 876 = b32 cp by loader_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 876 ∈ Flow.live Site.clcWait.pc by table_decide))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  rw [clcResp_loc] at he
  refine ⟨_, ok, acq, sc, ?_, he⟩
  rw [Nat.mod_mod, truncBits_parity]

/-- Whether the loader polls at site `s` (the K-loop polls, the CLC poll, the drain). -/
def Site.polls : Site → Bool
  | .wait _ | .clcWait | .drain _ => true
  | _ => false

/-- The instruction at every other site is not a poll. -/
theorem code_notPoll (s : Site) (hs : s.polls = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : ∀ p b off par a sc, ins.op ≠
    .mbarWait p b off par a sc := by
  intro p b off par a sc hop
  cases s with
  | wait _ | clcWait | drain _ => simp [Site.polls] at hs
  | load bb j =>
    obtain ⟨ins', hc', -, hadv, -⟩ := code_advances ⟨.load bb j, bb, j, .inl rfl⟩
    rw [hc] at hc'
    cases hc'
    rw [hop] at hadv
    exact hadv
  | arrive bb =>
    obtain ⟨ins', hc', -, hadv, -⟩ := code_advances ⟨.arrive bb, bb, 0, .inr rfl⟩
    rw [hc] at hc'
    cases hc'
    rw [hop] at hadv
    exact hadv
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_0); cases hop
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_0); cases hop
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_1); cases hop
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1); cases hop
  | ack => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8); cases hop
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); cases hop
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); cases hop
  | exit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0); cases hop

/-- Successful polls on slot `s`'s empty barrier since the start of the current trip
(or of the drain). -/
def polled (d : D) (s : Fin 4) : Nat :=
  match d.site with
  | .wait b => (if s.val < b.val then 1 else 0) + (if s.val + 4 < b.val then 1 else 0)
  | .load b _ | .arrive b =>
    (if s.val ≤ b.val then 1 else 0) + (if s.val + 4 ≤ b.val then 1 else 0)
  | .drain i => if s.val < i.val then 1 else 0
  | _ => 0

/-- The drain's successful polls on slot `s` so far: a drain at `drain i` has polled the slots below
`i`. A drain poll has no load behind it, so the exact counts (`LoaderTasks.Counts`) subtract it. -/
def drained (d : D) (s : Fin 4) : Nat :=
  match d.site with
  | .drain i => if s.val < i.val then 1 else 0
  | _ => 0

/-- Whether the loader is past its drain (or never polled: the other lanes of warp 11). -/
def Site.done : Site → Bool
  | .exitArrive | .exitWait | .exit => true
  | _ => false

/-- The empty barrier of slot `s` in thread `g`'s CTA. -/
abbrev emptyOf (L : Launch) (g : Nat) (s : Fin 4) : Loc := InputRing.emptyLoc L (g / L.block) s

theorem emptyLoc_eq {L : Launch} {c : Nat} {s s' : Fin 4} :
    InputRing.emptyLoc L c s = InputRing.emptyLoc L c s' ↔ s = s' := by
  constructor
  · intro h
    have := congrArg Loc.addr h
    simp only [InputRing.emptyLoc] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem okPoll_wait_empty {L : Launch} {g : Nat} {e : Event} {pc p : Nat} {ok acq : Bool}
    {sc : MbarScope} {s s' : Fin 4} (he : e = ⟨pc, .wait (emptyOf L g s') p ok acq sc⟩) :
    okPoll (emptyOf L g s) e = (ok && decide (s' = s)) := by
  rw [okPoll_wait he]
  simp only [emptyOf, emptyLoc_eq]

end Loader

theorem Prologue.next_loader {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {l : Loader.D}
    (hn : Prologue.next L g p e = some (some (.inr (.loader l)))) :
    l = Prologue.loaderStart L g ∨ l = Prologue.loaderIdle := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.loader.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all

end
end PTX.Kernels.Fp16Gemm8192.Proof
