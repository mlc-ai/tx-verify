-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The steps at the end of the MMA warp that `site_cases` does not take: after `bar.sync 2`
the peer pointer (`mapa`, evaluated on its own), and the poll of the own `+320` barrier, which
continues to the deallocation only when the carried address is a bit value. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}
  {ins : Instr}

/-- The peer pointer: `mapa` of the own `+320` barrier to the other CTA of the pair. -/
theorem mapa_peer (hpre : Pre P L mem0) (hg : g < L.threads) {t : TState}
    (h1 : t.regs 956 = some (b32 (L.sharedBase + 320)))
    (h2 : t.regs 957 = some (b32 (1 - L.rankOfCta (g / L.block))))
    (hat : At t (Flow.mbarArrive_7 - 2) F) :
    run kernel asms L g 1 t = some (PTX.next (setReg t 958 (peerPtr L g))) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcl := hpre.cluster
  have hgr := hpre.grid
  have hbl := hpre.block
  have hv := hpre.oneDimLaunch
  have hcta : g / L.block < L.grid := by
    simp only [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hsh := shape_bounds hpre hg
  have hr : readBits L g t 32 (.reg 957) =
      .ok (BitVec.ofNat 64 (1 - L.rankOfCta (g / L.block))) := by
    have hlt : 1 - L.rankOfCta (g / L.block) < 2 ^ 32 := by omega
    simp only [readBits, readReg, h2, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat hlt (by decide)]
  rw [run_mapa (rv := BitVec.ofNat 64 (1 - L.rankOfCta (g / L.block)))
    (loc := ⟨.shared, g / L.block, L.sharedBase + 320⟩)
    (peer := ⟨.shared, peer L g, L.sharedBase + 320⟩) Flow.code_1119 hat
    (readSharedAddress_b32 hg hcta (by omega) h1) hr ?_
    (asms_localRule_none (by simp [Assumption.FloatForm.ofOp])
      (by simp [Assumption.ApproxForm.ofOp]) L g t)]
  · rfl
  · have h1 := hv.1
    simp only [Launch.mapShared, Launch.peerCta, Launch.oneDim_clusterOfCta h1,
      Launch.oneDim_rankOfCta h1, Launch.oneDim_clusterStart h1, Launch.oneDim_clusterSizeOf h1,
      hcl, BitVec.toNat_ofNat, peer, clusterOf, ctaOf, rank]
    simp only [rank, clusterOf, ctaOf, Launch.oneDim_clusterOfCta h1, hcl] at hsh
    have hlt : 1 - g / L.block % 2 < 2 := by omega
    rw [Nat.mod_eq_of_lt (by omega : 1 - g / L.block % 2 < 18446744073709551616)]
    have hX : g / L.block / 2 * 2 + (1 - g / L.block % 2) < L.grid := by
      rw [hgr]; rw [hgr] at hcta; omega
    simp [hcta, hlt, hX]

theorem step_bar1 (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (hi : Inv L g ⟨.bar1, i, tr, base, pro⟩)
    (h : At t Site.bar1.pc (facts L g ⟨.bar1, i, tr, base, pro⟩))
    (hc : kernel.code[Site.bar1.pc]? = some ins)
    (hf : Fires Site.bar1.pc (eventTmpl asms L g t ins.op) e (some u)) :
    mma_cont L g ⟨.bar1, i, tr, base, pro⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  right
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 (PTX.next t) = some t1 ∧
      At t1 (Flow.mbarArrive_7 - 2) (factsAt L g (Flow.mbarArrive_7 - 2)
        ⟨.arrivePeer, i, tr, base, pro⟩) := by
    have hrk : L.rankOfCta (g / L.block) < 2 := by
      simp only [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]; omega
    mma_seg_s (At.next h) hpre hg [xor_one_lt2 hrk]
  have hm : run kernel asms L g 1 t1 = some (PTX.next (setReg t1 958 (peerPtr L g))) :=
    mapa_peer hpre hg (holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (by table_decide)))
      (holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (by table_decide))) ht1
  have h2 := At.set (r := 958) (v := peerPtr L g) ht1
    (facts_ne (show 958 ∉ Flow.live (Flow.mbarArrive_7 - 2) by table_decide))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 (PTX.next (setReg t1 958 (peerPtr L g))) =
      some t3 ∧ At t3 Site.arrivePeer.pc (facts L g ⟨.arrivePeer, i, tr, base, pro⟩) := by
    mma_seg_s h2 hpre hg
  exact ⟨⟨.arrivePeer, i, tr, base, pro⟩, t3, by simp [next],
    run_rtg (run_comp hr1 (run_comp hm hr3)), atS_of_at rfl ht3, ⟨hi.t, nofun, hi.trip⟩⟩


/-- The hand-off poll: a failed poll returns to it; a successful one runs to the deallocation,
or stops the machine when the carried address is no bit value, whose deallocation is then
undefined behaviour (a dead state). -/
theorem step_waitDealloc (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (hi : Inv L g ⟨.waitDealloc, i, tr, base, pro⟩)
    (h : At t (Site.waitDealloc).pc (facts L g ⟨.waitDealloc, i, tr, base, pro⟩))
    (hc : kernel.code[(Site.waitDealloc).pc]? = some ins)
    (hf : Fires (Site.waitDealloc).pc (eventTmpl asms L g t ins.op) e (some u)) :
    mma_cont L g ⟨.waitDealloc, i, tr, base, pro⟩ e u ∨
      (next L g ⟨.waitDealloc, i, tr, base, pro⟩ e = none ∧
        Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_27)
  have hpc := h.1
  rw [← hpc] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [hpc]
  have h1 := At.set (r := 5467) (v := .pred ok) h
    (facts_ne (show 5467 ∉ Flow.live Flow.mbarWait_27 by table_decide))
  cases ok with
  | false =>
    have hseg : Seg kernel asms L g 2 (Site.waitDealloc.pc + 1)
        ((5467, .pred false) :: facts L g ⟨.waitDealloc, i, tr, base, pro⟩) Site.waitDealloc.pc
        (facts L g ⟨.waitDealloc, i, tr, base, pro⟩) := by mma_close hpre hg
    obtain ⟨t', hr, ht'⟩ := hseg _ h1
    exact .inl (.inr ⟨_, t', by simp [next], run_rtg hr, atS_of_at rfl ht', hi⟩)
  | true =>
    have hseg : Seg kernel asms L g 2 (Site.waitDealloc.pc + 1)
        ((5467, .pred true) :: facts L g ⟨.waitDealloc, i, tr, base, pro⟩) Site.dealloc.pc
        (facts L g ⟨.dealloc, i, tr, base, pro⟩) := by mma_close hpre hg
    obtain ⟨t', hr, ht'⟩ := hseg _ h1
    by_cases hb : base.regBits.isSome = true
    · exact .inl (.inr ⟨⟨.dealloc, i, tr, base, pro⟩, t', by simp [next, hb], run_rtg hr,
        atS_of_at rfl ht', ⟨hi.t, nofun, hi.trip⟩⟩)
    · refine .inr ⟨by simp [next, hb], ?_⟩
      have h379 : t'.regs 379 = some base := by
        have := holds_mem ht'.2.2.2.2
          (Flow.mem_factsFrom (show 379 ∈ Flow.live Site.dealloc.pc by table_decide))
        rwa [show valueOf L g ⟨.dealloc, i, tr, base, pro⟩ 379 = base by mma_values] at this
      obtain ⟨f, hrf⟩ := readBits_regBits_none (L := L) (g := g) (w := 32) h379
        (by simpa using hb)
      have hbl : L.block % 32 = 0 := by rw [hpre.block]
      refine ⟨t', f, run_rtg hr, ?_⟩
      rw [out_event ht'.2.2.2.1 (by rw [ht'.1]; exact Flow.code_tmemDealloc_0) rfl rfl]
      simp [eventTmpl, tcTmpl, hbl, hrf, ofExec, bind, Except.bind]

theorem stepOk_bar1 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value} (i tr : Nat)
    (base : Value) (pr : Nat → Value) : (code asms L g pro).StepOk ⟨.bar1, i, tr, base, pr⟩ :=
  stepOk_of (fun hn => by cases hn; exact nofun)
    fun hi h hc hf => .inl (step_bar1 hpre hg i tr base pr hi (at_of_atS rfl h) hc hf)

theorem stepOk_waitDealloc (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.waitDealloc, i, tr, base, pr⟩ :=
  stepOk_of (fun hn => by
      simp only [next] at hn
      split at hn
      · split_ifs at hn with hok hb <;> cases hn
        · exact fun _ => hb
        · exact nofun
      · cases hn)
    fun hi h hc hf => step_waitDealloc hpre hg i tr base pr hi (at_of_atS rfl h) hc hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
