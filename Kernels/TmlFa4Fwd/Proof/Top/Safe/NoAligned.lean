-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Aligned
public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcAgree
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Aligned
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcPlace
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Entry
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Lemmas.Flow.NotClc

@[expose] public section

/-! # ERR-ALIGNED-MISMATCH: aligned instructions agree across the warp

The safety class of Core's `Unsafe` this file owns: `Safe.noAligned` proves it from `Base` and the
absence of undefined behaviour. The barriers are `bar_not_divergent` and `bar_not_exited`, the
collective `tcgen05` instructions the softmax, correction and later warps' `soft_tc_uniform`,
`corr_tc_uniform` and `tc_uniform`; the code has no cluster-barrier operation and no matrix
instruction, and a lane's one register request is at its warp's entry and before its exit
(`Top/Prog/Entry.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {l : Launch} {m : Mem0}

private theorem req_kind {pc : Nat} {k : Kind} (h : SetMaxNReg.isRequest ⟨pc, k⟩ = true) :
    ∃ inc n inst, k = .setMaxReg inc n inst := by
  cases k <;> simp_all [SetMaxNReg.isRequest]

/-- **ERR-ALIGNED-MISMATCH.** -/
theorem Safe.noAligned (hp : Pre p l m)
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) (hub : ¬ HasUb X) :
    ¬ AlignedMismatch l kernel X := by
  rintro ⟨c, hc⟩
  have hFw := launchFollow hp hX
  cases c with
  | tc =>
    rcases hc with hc | hc
    · obtain ⟨e, f, k, pc, pc', ke, kf, hw, hke, hkf, he, hf, hne⟩ :=
        (AlignedClass.divergent_tc_iff l).mp hc
      obtain ⟨h1, h2⟩ : pc = pc' ∧ tcStatic ke = tcStatic kf := by
        rcases Nat.lt_or_ge (Prologue.warpIndex l e.1) 12 with h12 | h12
        · rcases Nat.lt_or_ge (Prologue.warpIndex l e.1) 8 with h8 | h8
          · exact soft_tc_uniform hp hX hFw hw h8 hke hkf he hf
          · exact corr_tc_uniform hp hX hFw hub hw h8 (by omega) hke hkf he hf
        · exact tc_uniform hp hX hFw hw h12 hke hkf he hf
      exact hne.elim (fun h => h h1) (fun h => h h2)
    · obtain ⟨e, f, k, hw, hke, hx⟩ := (AlignedClass.exited_tc_iff l).mp hc
      rcases Nat.lt_or_ge (Prologue.warpIndex l e.1) 12 with h12 | h12
      · rcases Nat.lt_or_ge (Prologue.warpIndex l e.1) 8 with h8 | h8
        · exact soft_tc_unexited hp hX hFw hw h8 hke hx
        · exact corr_tc_unexited hp hX hFw hub hw h8 (by omega) hke hx
      · exact tc_unexited hp hX hFw hw h12 hke hx
  | bar => exact hc.elim (bar_not_divergent hp hX hFw) (bar_not_exited hp hX hFw)
  | cluster =>
    have hno : ∀ e ev, X.get e = some ev → isCluster ev = false := by
      intro e ⟨pc, k⟩ he
      cases k <;> try rfl
      rename_i op
      exact (Flow.no_kind_of_code hX Flow.clusterOp (fun k => ∃ op, k = .cluster op)
        (fun _ ⟨_, h⟩ => by cases h)
        (fun hf ⟨_, hk⟩ => by rw [Flow.fires_cluster_op hf hk]; rfl) kernel_noCluster he
        ⟨op, rfl⟩).elim
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · rw [AlignedClass.member, hno _ _ he] at hme; cases hme
    · have hme' : isCluster ev = true := hme
      rw [hno _ _ he] at hme'; cases hme'
  | matrix =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · rw [AlignedClass.member, noMatrixEvent hX he] at hme; cases hme
    · have hme' : isMatrix ev = true := hme
      rw [noMatrixEvent hX he] at hme'; cases hme'
  | setMaxReg =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, -, -, hne⟩ |
      ⟨e, f, ev, -, he, hme, -, ⟨pc, hx⟩, hle⟩
    · obtain ⟨inc, n, inst, rfl⟩ := req_kind hme
      obtain ⟨inc', n', inst', rfl⟩ := req_kind hmf
      have h1 := req_pc (g := e.1) (k := e.2) hp hX he
      have h2 := req_pc (g := f.1) (k := f.2) hp hX hf
      have hwi : Prologue.warpIndex l e.1 = Prologue.warpIndex l f.1 := hw.2
      rcases hne with hne | hne
      · exact hne (by rw [h1, h2, hwi])
      · exact hne rfl
    · obtain ⟨pe, ke⟩ := ev
      obtain ⟨inc, n, inst, rfl⟩ := req_kind hme
      have h0 := req_ord (g := e.1) (k := e.2) hp hX he
      have h1 := regExit hp hX (Frame.lt_of_get hX (g := f.1) (k := f.2) hx) hx
      have h2 : SetMaxNReg.ordinal X f ≤ (X.tr f.1).countP SetMaxNReg.isRequest :=
        (List.take_sublist _ _).countP_le
      have h3 : ((X.tr e.1).take e.2).countP SetMaxNReg.isRequest = 0 := h0
      have h4 : (X.tr f.1).countP SetMaxNReg.isRequest ≤
          ((X.tr e.1).take e.2).countP SetMaxNReg.isRequest := hle
      have h1' : 1 ≤ SetMaxNReg.ordinal X f := h1
      omega

end PTX.Kernels.TmlFa4Fwd.Proof.Top
