-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Steps.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part040
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056

@[expose] public section

/-! # Warpgroup 2's obligation at its `setmaxnreg` (pcs 2606–2630)

The `setmaxnreg`, then the five scalar `ld.param` of `param_0` (`seg_ldp`, under `Pre`: the
batch count, the two length pointers and the two lengths) and the tests on them (pc 2611: a CTA
beyond the batch returns; pc 2617: a null first length pointer skips its load; pc 2627: a null
second length pointer skips its load). Every branch is stepped by naming its predicate
(`SegU.pick`) and splitting on it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- A valid `setmaxnreg` continues at the next instruction. -/
theorem fires_setMaxReg_next {t u : TState} {inc : Bool} {n pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.setMaxReg inc n)) e (some u)) :
    u = PTX.next t := by
  simp only [eventTmpl, SetMaxNReg.tmpl] at hf
  split at hf <;> simp_all [Fires]

/-- A scalar `ld.param` of `param_0` at `pc`, then the rest of the segment. -/
theorem ldp_then (hp : Pre P L m) {pc d off x n b : Nat} {ty : DType} {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304) (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : d ∉ F.map Prod.fst)
    (rest : SegU kernel Assumptions.all L g (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) b G) :
    SegU kernel Assumptions.all L g pc F b G :=
  SegU.comp (SegU.of_seg (seg_ldp hp hc hty hal hoff hf h2991
    fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq))) rest

set_option hygiene false in
/-- An `ld.param` at code lemma `c` (field at `off` of `n` bytes into `d`). -/
local macro "ldp_at " c:term:max ty:term:max off:term:max d:term:max n:term:max x:term:max :
    tactic => `(tactic| (
  refine ldp_then (ty := $ty) (off := $off) (d := $d) (n := $n) (x := $x) hp $c (by decide)
    (by decide) (by decide) (by simp [p0fields])
    (by repeat (first | exact mem_factsFrom_eq (by decide +kernel) rfl |
      apply List.mem_cons_of_mem))
    (by simp only [List.map_cons, factsFrom_keys]; decide +kernel) ?_))

/-- The lengths at the entry: the parameters. -/
abbrev d1 (ac : List Value) (cnt : BitVec 64) (sb pb : Bool) (P : Params) : D :=
  ⟨.smr, 0, ac, pw P.topk, pw P.extra_topk, cnt, sb, pb⟩

set_option hygiene false in
/-- Cut the segment at the branch at `pc` (code lemma `c`) on predicate `p` of value `x`. -/
local macro "br_at " pc:term:max p:term:max x:term:max c:term:max : tactic => `(tactic| (
  refine SegU.comp (b := $pc) (G := factsFrom (ctlLive $pc) (valueOf P L g (d1 ac cnt sb pb P)))
    (by dq_seg) ?_
  refine SegU.pick (r := $p) (x := .pred $x)
    (mem_factsFrom_eq (show $p ∈ ctlLive $pc by decide +kernel) rfl) ?_
  refine SegU.comp (SegU.branch _ $c bra_rule noSegments.segFreePc) ?_))

set_option hygiene false in
/-- The `setmaxnreg` to the site `S` (the tests' outcomes `hz` decide it), up to the first
test. -/
local macro "smr_adv " S:term:max : tactic => `(tactic| (
  refine Code.advanceU (C := code P L g w) (dn := ⟨$S, 0, ac, pw P.topk, pw P.extra_topk, cnt,
    sb, pb⟩) Flow.code_2606 rfl (fun hf => fires_setMaxReg_next hf)
    (fun _ => by simp only [code, succ, afterSmr, afterA, hz, Bool.false_eq_true, ↓reduceIte])
    rfl rfl rfl rfl Nat.one_pos ?_
  refine SegU.comp (b := 2609) (G := factsFrom (ctlLive 2609) (valueOf P L g (d1 ac cnt sb pb P)))
    (by dq_seg) ?_
  ldp_at Flow.code_2609 (.int .b 32) 0 2429 4 P.b
  br_at 2611 130 (scmp .ge .s (r2W L g) (pw P.b)) Flow.code_2611
  rw [h1]))

set_option hygiene false in
/-- After the first test: the four `ld.param`, up to the second test. -/
local macro "smr_mid" : tactic => `(tactic| (
  refine SegU.comp (b := 2612) (G := factsFrom (ctlLive 2612) (valueOf P L g (d1 ac cnt sb pb P)))
    (by dq_seg) ?_
  ldp_at Flow.code_2612 (.int .b 64) 80 3017 8 (P.topkLenBase.getD 0)
  ldp_at Flow.code_2613 (.int .b 32) 40 2985 4 P.topk
  ldp_at Flow.code_2614 (.int .b 64) 144 3018 8 (P.extraTopkLenBase.getD 0)
  ldp_at Flow.code_2615 (.int .b 32) 120 2986 4 P.extra_topk
  br_at 2617 131 (eqz64 (pw8 (P.topkLenBase.getD 0))) Flow.code_2617
  rw [h2]))

theorem stepAt_smr (hp : Pre P L m) (d : D) (hs : d.site = .smr) : (code P L g w).StepAtU d := by
  dq_site
  cases h1 : scmp .ge .s (r2W L g) (pw P.b)
  · cases h2 : eqz64 (pw8 (P.topkLenBase.getD 0))
    · have hz := And.intro h1 h2
      smr_adv .lenA; smr_mid; dq_seg
    · cases h3 : eqz64 (pw8 (P.extraTopkLenBase.getD 0))
      · have hz := And.intro h1 (And.intro h2 h3)
        smr_adv .lenB; smr_mid
        br_at 2627 132 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) Flow.code_2627
        rw [h3]; dq_seg
      · have hz := And.intro h1 (And.intro h2 h3)
        smr_adv .wq; smr_mid
        br_at 2627 132 (eqz64 (pw8 (P.extraTopkLenBase.getD 0))) Flow.code_2627
        rw [h3]; dq_seg
  · have hz := h1
    smr_adv .exit; dq_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
