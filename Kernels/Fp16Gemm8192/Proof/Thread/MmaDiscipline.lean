-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueOps
public import Lemmas.Flow.Polls
public import Lemmas.Flow.TraceInduction
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps

@[expose] public section
/-! # The MMA warps' polls: their sites, their events and the parities of their polls

An MMA thread polls at three sites: slot `s`'s full barrier at each slot of a trip (with the trip's
parity `fp`), its accumulator-empty barrier (with `ap`) and the CLC response barrier. `polledFull`
is the parity of the thread's successful polls on a slot's full barrier, which `Mma.Counts` keeps.
The events of these sites are `clcWait_event`, `accWait_event` and `MmaEvents.full_event`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


namespace Mma

/-- The CLC poll names the CTA's CLC barrier. -/
theorem clcWait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcWait)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ p ok acq sc, p % 2 = d.cp % 2 ∧
      e = ⟨d.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15)
  have hb : t.regs 849 = some (b32 (L.sharedBase + 104)) :=
    (show valueOf L g ⟨.clcWait, w, q, fp, ap, cp, r, x⟩ 849 = b32 (L.sharedBase + 104) by
      mma_values) ▸ holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 849 ∈ Flow.live Site.clcWait.pc by table_decide))
  have hp : t.regs 883 = some (b32 cp) :=
    (show valueOf L g ⟨.clcWait, w, q, fp, ap, cp, r, x⟩ 883 = b32 cp by mma_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 883 ∈ Flow.live Site.clcWait.pc by table_decide))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  rw [clcResp_loc] at he
  refine ⟨_, ok, acq, sc, ?_, he⟩
  rw [Nat.mod_mod, truncBits_parity]

/-- The accumulator poll names the thread's accumulator-empty barrier and polls with `ap`. -/
theorem accWait_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {o : Option TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .accWait)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc,
      .wait ⟨.shared, g / L.block, L.sharedBase + 8 * (d.w % 2) + 88⟩ d.ap ok acq sc⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_16)
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hap : ap < 2 := hi.ap
  have hb : t.regs 857 = some (b32 (L.sharedBase + 8 * (w % 2) + 88)) :=
    (show valueOf L g ⟨.accWait, w, q, fp, ap, cp, r, x⟩ 857 =
      b32 (L.sharedBase + 8 * (w % 2) + 88) by mma_values) ▸ holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 857 ∈ Flow.live Site.accWait.pc by table_decide))
  have hp : t.regs 882 = some (b32 ap) :=
    (show valueOf L g ⟨.accWait, w, q, fp, ap, cp, r, x⟩ 882 = b32 ap by mma_values) ▸
      holds_mem h.2.2.2.2
        (Flow.mem_factsFrom (show 882 ∈ Flow.live Site.accWait.pc by table_decide))
  have hw2 : w % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 882) = .ok (truncBits 32 (BitVec.ofNat 64 ap)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 ap)).toNat % 2 = ap := by
    rcases (by omega : ap = 0 ∨ ap = 1) with rfl | rfl <;> decide
  exact ⟨ok, acq, sc, by rw [he, hpar]⟩

/-- Whether the MMA thread polls at site `s`. -/
def Site.polls : Site → Bool
  | .full _ | .clcWait | .accWait => true
  | _ => false

/-- The instruction at every other site is not a poll. -/
theorem code_notPoll (s : Site) (hs : s.polls = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : ∀ p b off par a sc, ins.op ≠
      .mbarWait p b off par a sc := by
  intro p b off par a sc hop
  cases s with
  | full _ | clcWait | accWait => simp [Site.polls] at hs
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3); cases hop
  | clcLoad => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_loadAcquire_2); cases hop
  | clcStatus => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_4); cases hop
  | clcFirst => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcQuery_5); cases hop
  | clcFence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_3); cases hop
  | ack => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11); cases hop
  | mma s j =>
    obtain ⟨ad, bd, en, hc'⟩ := code_mma s j
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    cases hop
  | commit s =>
    rw [code_commit_ops s] at hc
    cases hc
    cases hop
  | accCommit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_4); cases hop
  | exitArrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1); cases hop
  | exitWait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1); cases hop
  | exit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0); cases hop

/-- Whether slot `s` has been polled in the current trip. -/
def past (site : Site) (s : Fin 4) : Bool :=
  match site with
  | .full s' => decide (s.val < s'.val)
  | .mma s' _ | .commit s' => decide (s.val ≤ s'.val)
  | _ => false

/-- The successful polls on slot `s`'s full barrier, modulo 2 (none before the election). -/
def polledFull (d : D) (s : Fin 4) : Nat :=
  match d.site with
  | .elect => 0
  | site => d.fp + if past site s then 1 else 0

/-- Whether the thread has left (or never entered) the task loop. -/
def Site.done : Site → Bool
  | .exitArrive | .exitWait | .exit => true
  | _ => false

/-- Slot `s`'s full barrier in thread `g`'s CTA. -/
abbrev fullOf (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩

theorem fullOf_eq {L : Launch} {g : Nat} {s s' : Fin 4} : fullOf L g s = fullOf L g s' ↔ s = s' :=
    by
  constructor
  · intro h
    have : L.sharedBase + 8 + 8 * s.val = L.sharedBase + 8 + 8 * s'.val := congrArg Loc.addr h
    exact Fin.ext (by omega)
  · rintro rfl; rfl

end Mma

theorem Prologue.next_mma {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {m : Mma.D}
    (hn : Prologue.next L g p e = some (some (.inr (.mma m)))) :
    m.site = .elect ∨ m.site = .exitArrive := by
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.mma.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [Prologue.mmaStart]

end
end PTX.Kernels.Fp16Gemm8192.Proof
