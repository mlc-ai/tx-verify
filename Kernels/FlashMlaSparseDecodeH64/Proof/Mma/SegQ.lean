-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.Step.TcCpWs
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepMma

@[expose] public section

/-! # The landing at the first Q load

The code before the first Q load (pcs 1897–1905) adds 128 to the generic pointer to `param_1`
(pc 1902): the kernel's parameter-pointer reading turns it into the Q descriptor's numeric
address (`run_paramAdd`), which the symbolic walk does not know. `land_q0` cuts every segment
that ends at the first Q load at pc 1897; the scoped rule of `seg_sym` applies it, so that the
three sites that reach the first Q load (the election and the two length loads) are proved by
`mma_sites`. -/

/-! # The MMA warp's step tactics

`mma_sites s` discharges the step obligations of the sites of `s` that the theorem's hypothesis
`hs` admits: `site_cases` with the machine's transitions, segments by `seg_fp` closed by `rfl` or
`sym_close` (`mma_seg`), the trivial invariant and guards. No assumption gives an integer
instruction of the role a rule of its own (`asms_localRule_int`), and a branch on a parameter
word is decided by the case split's hypothesis (`sym_decide`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

scoped macro_rules
  | `(tactic| sym_local_none) => `(tactic| (
      intro t ht a ha
      exact asms_localRule_int (t := t) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (by simp [Assumptions.peerPackRule, Assumptions.peerPack, ht]) a ha))

scoped macro_rules
  | `(tactic| sym_decide) => `(tactic| first
      | assumption
      | exact Bool.eq_false_iff.mpr (by assumption))

/-- The MMA warp's segments, closed by the table's terms. -/
macro "mma_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- `mma_sites s except […]`: the obligations of the sites of `s` that `hs` admits. -/
syntax "mma_sites " ident (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mma_sites $s $[except [$ovs,*]]?) => `(tactic|
      site_cases $s:ident $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, poll, loopEntry, loopEnd, leadNext, afterTopk, lensD, ncWord]
        seg_by (mma_seg) inv_by (exact fun _ => trivial) guard_by (trivial))

/-- `mma_issue lemma`: an event that continues at the next instruction by `lemma` (the
`tcgen05.cp` and `.ws` MMA sites, which `advances` does not know). -/
syntax "mma_issue " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mma_issue $adv) => `(tactic|
      issue_step $adv
        trans [succ, poll, loopEntry, loopEnd, leadNext, afterTopk, lensD, ncWord]
        seg_by (mma_seg) inv_by (exact fun _ => trivial))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A segment to pc 1897 with the first Q load's table extends to the load.** -/
theorem land_q0 (hp : Pre P L m) {s : Nat} {F : List (Nat × Value)}
    {l0 l1 neg cnt pha par : BitVec 64}
    (h : ∃ n, Seg kernel Assumptions.all L g n s F 1897
      (factsFrom (Flow.live 1897) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩))) :
    ∃ n, Seg kernel Assumptions.all L g n s F 1906
      (factsFrom (Flow.live 1906) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) := by
  obtain ⟨n1, h1⟩ := h
  obtain ⟨n2, h2⟩ : ∃ n, Seg kernel Assumptions.all L g n 1897
      (factsFrom (Flow.live 1897) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) 1902
      (factsFrom (Flow.live 1902) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) := by
    seg_sym using mma_seg
  have h3 : Seg kernel Assumptions.all L g 1 1902
      (factsFrom (Flow.live 1902) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) 1903
      ((3058, .bits 64 (BitVec.ofNat 64 (P.param1Base + (128 : Int).toNat))) ::
        factsFrom (Flow.live 1902) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) := by
    intro t ht
    exact ⟨_, run_paramAdd (pc := 1902) (k := 128) Flow.code_1902 ht (by decide)
      (holds_mem (atHolds ht) (r := 3006) (mem_factsFrom (by decide))) hp.param1Object
      (by decide), At.set ht (fun q hq => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        exact fun h => by subst h; exact absurd hr (by decide))⟩
  obtain ⟨n4, h4⟩ : ∃ n, Seg kernel Assumptions.all L g n 1903
      ((3058, .bits 64 (BitVec.ofNat 64 (P.param1Base + (128 : Int).toNat))) ::
        factsFrom (Flow.live 1902) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) 1906
      (factsFrom (Flow.live 1906) (valueOf P L g ⟨.qLoad 0, l0, l1, neg, cnt, pha, par⟩)) := by
    seg_sym using mma_seg
  exact ⟨_, (h1.comp h2).comp (h3.comp h4)⟩

set_option hygiene false in
/-- A segment that ends at the first Q load is cut at pc 1897 (`land_q0`). -/
scoped macro_rules
  | `(tactic| seg_sym using $tac) => `(tactic| (
      refine land_q0 hp ?_
      seg_sym using $tac))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
