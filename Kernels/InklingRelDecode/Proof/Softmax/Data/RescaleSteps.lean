-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Update
public import Kernels.InklingRelDecode.Proof.Lib.Havoc
public import Lemmas.Flow.DataTcLoad
public import Lemmas.Flow.DataElems
import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.ReachFrameGuard
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The data steps of the rescale window

The load of the accumulator (pc 2260) puts its 64 words in registers 1547 to 1610 and the value
state keeps them (`Vals.ov`). From the wait of pc 2261 the generated run (`Gen.rs_run`) multiplies
each by the rescale factor, up to the barrier of pc 2326. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- A run with a condition as a segment that may end dead. -/
theorem segU_of_segD {n a b : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : SegD kernel Assumptions.all L g n a F b G C) :
    SegU kernel Assumptions.all L g a F b G := by
  intro t ht
  by_cases hc : C
  · obtain ⟨u, hr, hu⟩ := (h t ht).1 hc
    exact .inl ⟨u, run_rtg hr, hu⟩
  · exact .inr ((h t ht).2 hc)

/-- **The rescale run** from the loaded words to the barrier of pc 2326. -/
theorem rs_reach (v : Vals) :
    Reach kernel Assumptions.all L g 2262 (dFS L .waitLdO v) (dFS L .bar24 v) := by
  have p1 : SegU kernel Assumptions.all L g 2262 (dFS L .waitLdO v) 2326 (dFS L .bar24 v) :=
    segU_of_segD (Gen.rs_run L g (rsV L v))
  have p2 : Reach kernel Assumptions.all L g 2326 (dFS L .bar24 v) (dFS L .bar24 v) :=
    reach_frameSetG (S := []) Lib.rulesFrame (by rw [dFS_keys]; decide +kernel)
      (fun _ h => nomatch h) (by decide +kernel) (fun _ h => h)
  exact SegU.reach_then p1 p2

/-- **The data step of the accumulator load of pc 2260**: the words it returns are in registers
1547 to 1610. -/
theorem data_ldO {d : D} (hs : d.c.site = .ldO) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 2260 := by
    change d.c.site.pc = 2260
    rw [hs]
    rfl
  apply DataStep.tcLoad (by rw [pc]; exact Flow.code_tmemLoad_1) (fun s h => by cases h)
    (by rw [pc]; change Assumptions.all.any (·.tcLdWait 2260) = false; decide +kernel)
  intro hi a vals d' t hn hl hat
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hl64 : vals.length = 64 := by rw [hl]; rfl
  show (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g)
      (setRegs (PTX.next t) ovRegs vals) t' → Stops kernel Assumptions.all L g t' →
        Holds t'.regs (dF L _)) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g)
        (setRegs (PTX.next t) ovRegs vals)
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  have hF := facts_dF _ hreg
  have hd : dF L d = dFS L .ldO d.v := by simp [dF, hs]
  have hnd : ovRegs.Nodup := by decide +kernel
  have hoff : ∀ q ∈ (code e L g).facts d, q.1 ∉ ovRegs := by
    intro q hq hmem
    have : q.1 ∈ ((code e L g).facts d).map Prod.fst := List.mem_map_of_mem hq
    simp only [Control.facts, List.map_append, PTX.Flow.factsFrom_keys, dF,
      dFS_keys, hs] at this
    have all : ∀ r ∈ Control.ctlLive 2260 ++ dKeys .ldO, r ∉ ovRegs := by decide +kernel
    exact all _ (by simpa [Site.pc] using this) hmem
  have hu := at_tcLoad (vals := vals) (⟨hpc.trans pc, hsub, hacc, hft, hreg⟩ :
    At t 2260 ((code e L g).facts d)) hnd hoff
  have hv : dF L ⟨{ d.c with site := .waitLdO }, record L d
      ⟨(code e L g).pc d, .tc (.ld a vals (.s16x32bx2 64))⟩ .waitLdO⟩ =
      dFS L .waitLdO { d.v with ov := vals } := by
    simp [dF, record, hs]
  rw [hv]
  refine reach_frameSetG (S := []) Lib.rulesFrame (by rw [dFS_keys]; decide +kernel)
    (fun _ h => nomatch h) (by decide +kernel) (fun R h => ?_) _ hu
  rw [holds_append] at h
  have h1 := facts_dF _ h.1
  rw [hd] at h1
  refine holds_of_mem fun r x hm => ?_
  rcases List.mem_append.mp (rs0_of_load d.v hl64 _ hm) with hx | hx
  · exact holds_mem h1 (round_sub (s := .ldO) rfl d.v _ hx)
  · exact holds_mem h.2 hx

/-- **The data step of the wait of pc 2261**: the run multiplies the loaded words. -/
theorem data_waitLdO {d : D} (hs : d.c.site = .waitLdO) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 2261 := by
    change d.c.site.pc = 2261
    rw [hs]
    rfl
  apply DataStep.next (op := .tcWaitLd) (by rw [pc]; exact Flow.code_tmemWait_2)
    (fun t ev u hf => fires_tcWaitLd_next hf)
  intro hi ev d' t hn hat
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  have hF := facts_dF _ hreg
  have hv : dF L ⟨{ d.c with site := .bar24 }, record L d ev .bar24⟩ = dFS L .bar24 d.v := by
    simp [dF, record, hs]
  have hd : dF L d = dFS L .waitLdO d.v := by simp [dF, hs]
  rw [hv]
  refine rs_reach (L := L) (g := g) d.v _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PTX.next, hpc]
    exact pc
  · simp [PTX.next, hsub]
  · simp [PTX.next, hacc]
  · simp [PTX.next, hft]
  · rw [hd] at hF
    simpa [PTX.next] using hF

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
