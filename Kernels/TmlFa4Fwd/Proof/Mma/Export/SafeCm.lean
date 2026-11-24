-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Flow.Step.ShapeRegs
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part037
import Kernels.TmlFa4Fwd.Flow.Code.Part038
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Safe
import Kernels.TmlFa4Fwd.Proof.Mma.Shape

@[expose] public section

/-! # The MMA warp's commits are no undefined behaviour

A `tcgen05.commit` without a mask faults when the thread is outside the launch, when its barrier
address is not an 8-aligned shared address (`mbarClusterLoc`), or when its target does not
resolve (`TcCommit.resolve`). Every commit barrier of the MMA warp's table is the shared base
plus a multiple of 8 (`cmOp`), and in a one-dimensional launch with clusters of one CTA
(`Pre.cluster`) the commit resolves to the thread's own CTA (as the old tree's
`Proof/MmaCommit.lean`, `commitResolved`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- A one-CTA commit of a thread of the launch to an 8-aligned barrier of its CTA resolves. -/
theorem commit_resolves (hp : Pre p L m) (hg : g < L.threads) (addr : Nat) :
    TcCommit.resolve L .one (g / L.block) ⟨.shared, g / L.block, addr⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) ≠ none := by
  have hBlock : 0 < L.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < L.grid * L.block from hg)
  have hOne := hp.cluster.2.2
  simp [TcCommit.resolve, hp.launch.1, hCta, Launch.oneDim_rankOfCta hOne,
    Launch.oneDim_clusterOfCta hOne, Launch.oneDim_clusterSizeOf hOne, hp.cluster.1, Nat.mod_one]

/-- A commit to an 8-aligned barrier word held in a 32-bit register is no undefined behaviour. -/
theorem commit_ok (hp : Pre p L m) (hg : g < L.threads) {t : TState} {base : Nat} {off : Int}
    {x : BitVec 64} (hr : t.regs base = some (.bits 32 x))
    (h8 : (smLoc L g x off).addr % 8 = 0) (f : Fault) :
    eventTmpl Assumptions.all L g t (.tcCommit .one base off none) ≠ .ub f := by
  have hres := commit_resolves hp hg (smLoc L g x off).addr
  have hloc : mbarClusterLoc L g t base off = .ok (smLoc L g x off) := by
    simp only [smLoc] at h8 ⊢
    simp [mbarClusterLoc, sharedEffAddr, readReg, hr, readBits] at h8 ⊢
    simp [h8, pure, Except.pure]
  simp only [eventTmpl, tcCommitTmpl, ofExec, hloc, bind, Except.bind, pure, Except.pure,
    show g < L.threads from hg, ↓reduceIte]
  intro h
  cases hres' : TcCommit.resolve L .one (g / L.block) (smLoc L g x off)
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (smLoc L g x off).cta)) with
  | none => exact hres (by simpa [smLoc] using hres')
  | some s => simp [hres'] at h

set_option maxHeartbeats 4000000 in
/-- **No commit of the MMA warp is undefined behaviour.** -/
theorem commit_safe (hp : Pre p L m) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : (code p L g ent).AtD d t)
    (hc : kernel.code[(code p L g ent).pc d]? = some ins)
    (hf : Fires ((code p L g ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ c, d.site = .cm c) (f : Fault) : e.kind ≠ .ub f := by
  replace h : At t d.site.pc (facts p L g ent d) := h
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have h0 := sbW_al hp
  have hsh := hp.shared
  obtain ⟨site, v⟩ := d
  obtain ⟨c, rfl⟩ := hs
  intro hk
  fin_cases c <;> site_code <;>
  · have hu := fires_ub hf hk
    refine commit_ok hp hg (reg_bits h (by lit_mem) rfl) ?_ f hu
    refine smLoc_al ?_ (by decide)
    first
      | with_reducible exact slotAddr_al hp _
      | with_reducible exact addi_al h0 (by decide)
      | with_reducible exact h0
      | (simp only [BitVec.toNat_ofNat]; omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
