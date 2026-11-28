-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Init
public import Kernels.InklingRelDecode.Proof.Softmax.Data.RunAdv
public import Kernels.InklingRelDecode.Gen.SoftmaxPack
public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesP
public import Lemmas.Flow.DataTcLoad
public import Lemmas.Flow.SegFrameR
public import Lemmas.Flow.ReachFrameGuard
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The pairs of scores at the wait of the score load

The load of pc 1265 returns the 64 score words of the thread's row into registers 876 to 939
(`Vals.s`); the 32 moves of pcs 1266 to 1297 join them in pairs (registers 2447 to 2478), the
facts the first window reads at the wait of pc 1298. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem spF_keys (s : List Value) :
    (spF s).map Prod.fst = (List.range 32).map (2447 + ·) := by
  simp [spF, List.map_map, Function.comp_def]

/-- The register file of the pairs' run: the loaded words. -/
def sV (s : List Value) (r : Nat) : Value := s.getD (r - 876) (b32 0)

theorem sp_out (s : List Value) : Gen.sp_facts1 (sV s) = spF s := rfl

theorem loopSite_ne_waitLd (e : Entry) (t i : Nat) : loopSite e t i ≠ .waitLd := by
  rcases loopSite_mem e t i with h | h | h <;> rw [h] <;> decide

/-- Only the score load's site is followed by the wait of the load. -/
theorem next_waitLd {d : D} {ev : Event} {c' : Control.D}
    (h : Control.next e L g d.c ev = some (some c')) (hc : c'.site = .waitLd) :
    d.c.site = .ldS := by
  cases hs : d.c.site <;> simp only [Control.next, hs] at h <;> (try split at h) <;>
    try (simp at h; done)
  all_goals
    simp only [Option.some.injEq] at h
    subst h
    try (simp at hc ⊢; done)
  all_goals
    exfalso
    revert hc
    simp only [advance]
    (try split_ifs) <;> simp [loopSite_ne_waitLd]

theorem sv_mem (vals : List Value) (hl : vals.length = 64) {r : Nat} (h1 : 876 ≤ r)
    (h2 : r < 940) : (r, sV vals r) ∈ sRegs.zip vals := by
  have hr : r - 876 < 64 := by omega
  rw [List.mem_iff_getElem?]
  refine ⟨r - 876, ?_⟩
  simp [sRegs, sV, h1, hl, hr]

theorem sp_mem (vals : List Value) (hl : vals.length = 64) :
    ∀ x ∈ Gen.sp_facts0 (sV vals), x ∈ sRegs.zip vals := by
  simp only [Gen.sp_facts0, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first
    | exact fun _ h => nomatch h
    | exact sv_mem vals hl (by omega) (by omega)

/-- **The moves of pcs 1266 to 1297** join the loaded words in pairs. -/
theorem sp_reach (vals : List Value) (hl : vals.length = 64) :
    Reach kernel Assumptions.all L g 1266 (sRegs.zip vals) (spF vals) := by
  have p1 := Code.SegU.sub_start (segU_of_segD' (Gen.sp_run L g (sV vals))) (sp_mem vals hl)
  rw [sp_out] at p1
  have p2 : Reach kernel Assumptions.all L g 1298 (spF vals) (spF vals) :=
    reach_frameSetG (S := []) Lib.rulesFrame (by rw [spF_keys]; decide +kernel)
      (fun _ h => nomatch h) (by decide +kernel) (fun _ h => h)
  exact SegU.reach_then p1 p2

/-- **The data step of the score load of pc 1265**: the moves that follow join its words. -/
theorem pairs_ldS {d : D} (hs : d.c.site = .ldS) : DataStep (codeS e L g) pF d := by
  have pc : (codeS e L g).pc d = 1265 := by
    change d.c.site.pc = 1265
    rw [hs]
    rfl
  apply DataStep.tcLoad (by rw [pc]; exact Flow.code_tmemLoad_0) (fun s h => by cases h)
    (by rw [pc]; change Assumptions.all.any (·.tcLdWait 1265) = false; decide +kernel)
  intro hi a vals d' t hn hl hat
  obtain ⟨c', hnc, rfl⟩ := succ_inv (show succ e L g d _ = some (some d') from hn)
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hl64 : vals.length = 64 := by rw [hl]; rfl
  obtain ⟨hpc, hsub, hacc, hft, -⟩ := hat
  have hu := at_tcLoad (vals := vals) (F := []) (ds := sRegs)
    (⟨hpc.trans pc, hsub, hacc, hft, trivial⟩ : At t 1265 []) (by decide +kernel)
    (fun _ h => nomatch h)
  have hd : pF ⟨{ d.c with site := .waitLd }, record L d
      ⟨(codeS e L g).pc d, .tc (.ld a vals (.s16x32bx2 64))⟩ .waitLd⟩ = spF vals := by
    simp [pF, record, hs]
  rw [hd]
  rw [List.nil_append] at hu
  exact sp_reach (L := L) (g := g) vals hl64 _ hu

/-- **The pairs of scores after every state**: only the score load's state has them. -/
theorem pair_step (d : D) : DataStep (codeS e L g) pF d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hs : d.c.site = .ldS
  · exact @pairs_ldS e L g d hs t ev u d' ins hat hi hc' hf hn
  · obtain ⟨c', hnc, rfl⟩ := succ_inv (show succ e L g d ev = some (some d') from hn)
    have h : c'.site ≠ .waitLd := fun h => hs (next_waitLd hnc h)
    exact .inl fun _ _ _ => by simp [pF, h]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
