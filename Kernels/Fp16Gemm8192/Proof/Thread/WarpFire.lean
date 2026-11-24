-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpSites
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaUnelected
public import Kernels.Fp16Gemm8192.Proof.Thread.Warp
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # A thread at a collective site can perform its collective

At a collective site (`CollSite`) the thread's template, after local steps from the end of its run,
admits every event of `CollSite.Fires`: the full-mask election and warp barrier with any instance
label and leader, and the shuffle of the thread's warp index with any received value
(`coll_fire_thm`). The masks are the full mask by the site's register values. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A full-mask election's template admits every instance label and leader. -/
theorem fires_elect_any {A : List Assumption} {t : TState} {dst : Option Nat} {p : Nat}
    {mask : Opnd} {pc : Nat} {bits : BitVec 64} (hm : readBits L g t 32 mask = .ok bits)
    (hb : bits.toNat = fullMask) (inst leader : Nat) :
    ∃ u, Fires pc (eventTmpl A L g t (.warp ⟨.elect, none, [dst, some p], [], some mask⟩))
      ⟨pc, .elect fullMask inst leader⟩ (some u) := by
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by norm_num)
  have hmem : electMember bits.toNat (laneOf L g) := by
    refine ⟨hlane, ?_⟩
    have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [hb, fullMask, h32, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hlane
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm]
  rw [ite_eq_left hmem]
  exact ⟨_, inst, leader, by rw [hb], rfl⟩

/-- The full-mask warp barrier's template admits every instance label. -/
theorem fires_warpBar_any {A : List Assumption} {t : TState} {pc : Nat} (inst : Nat) :
    ∃ u, Fires pc (eventTmpl A L g t (.warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩))
      ⟨pc, .warpBar fullMask inst⟩ (some u) := by
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by norm_num)
  have hb : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = fullMask := by decide
  have hmem : electMember (truncBits 32 (BitVec.ofInt 64 (-1))).toNat (laneOf L g) := by
    refine ⟨hlane, ?_⟩
    have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [hb, fullMask, h32, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hlane
  simp only [eventTmpl, warpTmpl_barWarp, warpBarTmpl, readBits, pure, Except.pure]
  rw [ite_eq_left hmem]
  exact ⟨_, inst, by rw [hb], rfl⟩

/-- **A thread at a collective site can perform it**: after local steps from the end of its run,
every event of the site is a step of the thread. -/
theorem coll_fire_thm (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event} {d : ThreadD}
    {t : TState} {s : CollSite}
    (hσ : (code L g).toMachine.after (some (code L g).init) es = some (some d))
    (hs : d.coll = some s) (hr : Run kernel Prod L g {} es (some t)) :
    ∃ t1, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      ∀ e, s.Fires L g e → ∃ u, EStep kernel Prod L g t1 e (some u) := by
  obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
  have hout := Code.site_out (sound hpre hg) hgood
  have hat := hgood.1
  refine ⟨t1, hl, fun e he => ?_⟩
  rcases d with ⟨site, w⟩ | (l | ⟨site, w', q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ | c)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · obtain ⟨recv, ok, rfl⟩ := he
      have hr9 : t1.regs 55 = some (b32 (g % L.block / 32)) :=
        holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 55 ∈ Flow.live Prologue.Site.shfl.pc by table_decide))
      have hb : L.block % 32 = 0 := by rw [hpre.block]
      have hpc : t1.pc = Prologue.Site.shfl.pc := hat.1
      have hu : ∃ u, Fires t1.pc ((code L g).tmpl (some (.inl ⟨.shfl, w⟩)) t1)
          ⟨CollSite.shfl.pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ (some u) := by
        simp only [Code.tmpl, hpc, Prologue.Site.pc, Flow.code_shfl_0, eventTmpl,
          warpTmpl_shfl_idx, shflTmpl,
          readBits, readValue, readReg, hr9, b32, Value.bytes, hb, pure, Except.pure]
        rw [ite_eq_left (by decide), ite_eq_left trivial,
          show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 by decide,
          show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide]
        exact ⟨_, recv, ok, rfl, rfl⟩
      obtain ⟨u, hu⟩ := hu
      exact ⟨u, _, hout, hu⟩
    · obtain ⟨inst, leader, rfl⟩ := he
      have hm : readBits L g t1 32 (.reg 57) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 57 ∈ Flow.live Prologue.Site.elect.pc by table_decide))) (by decide)
      obtain ⟨u, hu⟩ := fires_elect_any (A := Prod) (dst := none) (p := 976)
        (pc := t1.pc) hm (by decide) inst leader
      refine ⟨u, _, hout, ?_⟩
      have hpc : t1.pc = Prologue.Site.elect.pc := hat.1
      simp only [Code.tmpl, hpc, Prologue.Site.pc, Flow.code_elect_0] at hu ⊢
      exact hu
    · obtain ⟨inst, rfl⟩ := he
      obtain ⟨u, hu⟩ := fires_warpBar_any (A := Prod) (L := L) (g := g) (t := t1) (pc := t1.pc) inst
      refine ⟨u, _, hout, ?_⟩
      have hpc : t1.pc = Prologue.Site.warpBar.pc := hat.1
      simp only [Code.tmpl, hpc, Prologue.Site.pc, Flow.code_warpBar_0] at hu ⊢
      exact hu
    · obtain ⟨inst, leader, rfl⟩ := he
      have hm : readBits L g t1 32 (.reg 649) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 649 ∈ Flow.live Prologue.Site.roleElect.pc by table_decide))) (by decide)
      obtain ⟨u, hu⟩ := fires_elect_any (A := Prod) (dst := none) (p := 977)
        (pc := t1.pc) hm (by decide) inst leader
      refine ⟨u, _, hout, ?_⟩
      have hpc : t1.pc = Prologue.Site.roleElect.pc := hat.1
      simp only [Code.tmpl, hpc, Prologue.Site.pc, Flow.code_elect_1] at hu ⊢
      exact hu
  · simp [ThreadD.coll] at hs
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨inst, leader, rfl⟩ := he
    have hm : readBits L g t1 32 (.reg 836) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 836 ∈ Flow.live Mma.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨u, hu⟩ := fires_elect_any (A := Prod) (dst := none) (p := 1000)
      (pc := t1.pc) hm (by decide) inst leader
    refine ⟨u, _, hout, ?_⟩
    have hpc : t1.pc = Mma.Site.elect.pc := hat.1
    simp only [Code.tmpl, hpc, Mma.Site.pc, Flow.code_elect_3] at hu ⊢
    exact hu
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨inst, leader, rfl⟩ := he
    have hm : readBits L g t1 32 (.reg 630) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 630 ∈ Flow.live Scheduler.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨u, hu⟩ := fires_elect_any (A := Prod) (dst := none) (p := 994)
      (pc := t1.pc) hm (by decide) inst leader
    refine ⟨u, _, hout, ?_⟩
    have hpc : t1.pc = Scheduler.Site.elect.pc := hat.1
    simp only [Code.tmpl, hpc, Scheduler.Site.pc, Flow.code_elect_2] at hu ⊢
    exact hu
  · simp [ThreadD.coll] at hs

end
end PTX.Kernels.Fp16Gemm8192.Proof
