-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Loop
import Kernels.InklingRelDecode.Proof.Mma.Offsets
import Kernels.InklingRelDecode.Gen.StepMma
import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.SiteCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w
local notation "S" => SegU kernel Assumptions.all L g

private theorem no_limit {t : TState} (ht : At t 2425 (F d 2425))
    (hw : d.word.regBits = none) : Machine.Dead (K := kernel) (A := Assumptions.all)
      (L := L) (g := g) t := by
  obtain ⟨hp,_,_,hf,hR⟩ := ht
  have hr : t.regs 471 = some d.word :=
    holds_mem hR (mem_factsFrom (val := valueOf L regs w d) (show 471 ∈ Flow.live 2425 by decide))
  obtain ⟨f,hf'⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hr hw
  apply dead_of_error (hp ▸ Flow.code_2425) rfl hf
  rw [Lib.workerInt (by rfl) hp (by decide)]
  simp only [execInt, DType.width, hf']
  rfl

private theorem final_facts (d : D) :
    F {d with i := d.i + 1, site := .finBar} 2550 = F {d with site := .finBar} 2550 := by
  unfold liveFacts
  rw [show Flow.live 2550 = [3,462,463,464,465,466,528,529,530,531,532,534,1949,2020] by decide]
  simp only [factsFrom, List.map_cons, List.map_nil, valueOf, values, lookupLit]

private theorem inv_start (d : D) (hi : d.i = 0) : Inv {d with site := startSite d.limit} := by
  unfold startSite
  split_ifs
  · trivial
  · change d.i < d.limit ∧ d.limit ≤ 2147483646
    omega

theorem enter_loop (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i = 0) :
    let dst := {d with site := startSite d.limit}
    S 2425 (F d 2425) dst.site.pc (F dst dst.site.pc) := by
  dsimp only
  cases hw : d.word.regBits with
  | none => exact fun t ht => .inr (no_limit ht hw)
  | some bits =>
    apply limit_check.comp
    by_cases hh : 2147483646 < d.limit
    · rw [show startSite d.limit = .finBar by simp [startSite,hh]]
      exact over_limit hh
    have hn : d.limit ≤ 2147483646 := by omega
    apply (within_limit hn).comp
    apply output_base.comp
    apply (SegU.of_seg (setup_descriptors hs hi)).comp
    apply (iter_limit (by simp [hw]) hn).comp
    apply (SegU.of_seg (seed_cursors hs hi)).comp
    apply (index_check (by omega : d.i < 2 ^ 31) (by omega)).comp
    by_cases hz : d.limit = 0
    · rw [show startSite d.limit = .finBar by simp [startSite,hz]]
      apply (pv_branch (by omega : d.limit ≤ d.i)).comp
      apply (SegU.of_seg (first_iter (by omega : d.i < 2 ^ 31))).comp
      apply (skip_pv hi).comp
      have h := loop_back (L := L) (g := g) (regs := regs) (w := w) hs
        (by omega : d.i ≤ d.limit) hn
      rw [show iterNext d = {d with site := .finBar, i := d.i + 1} by
        simp [iterNext, hi, hz]] at h
      change S 2447 (F d 2447) 2550 (F {d with site := .finBar} 2550)
      rw [← final_facts d]
      exact h
    · rw [show startSite d.limit = .qkBar by simp [startSite,hz,hh]]
      apply (qk_branch (by omega : d.i < d.limit)).comp
      exact SegU.of_seg (ready_head hs (by omega : d.i < 2 ^ 31))

theorem start_bar_step {Q : Params} {m : Mem0} (hp : Pre Q L m) (i : Nat) (v : Value) :
    (code L g regs w).StepAtU ⟨.bar0,i,v⟩ := by
  let d : D := ⟨.bar0,i,v⟩
  let dst := {d with site := startSite d.limit}
  refine ⟨fun _ => ⟨_, Flow.code_2424, rfl, trivial⟩, ?_⟩
  intro t e u ins hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2424)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have hv : Inv dst := inv_start d hi
  have span := enter_loop (g := g) (regs := regs) (w := w) (d := d) hp.sharedRange hi
  have h0 := At.next (Code.at_of_atD hat rfl rfl)
  change At _ 2425 (F d 2424) at h0
  have live : F d 2424 = F d 2425 :=
    congrArg (fun rs => factsFrom rs (valueOf L regs w d))
      (by decide : Flow.live 2424 = Flow.live 2425)
  rw [live] at h0
  obtain ⟨s,hτ,hgood⟩ := Code.landsU (C := code L g regs w) (d := dst)
    h0 span hv rfl rfl
  exact .inl (.inr ⟨dst,s,rfl,hτ,hgood⟩)

end PTX.Kernels.InklingRelDecode.Proof.Mma
