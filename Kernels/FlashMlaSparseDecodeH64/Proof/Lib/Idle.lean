-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LdParam
public import Lemmas.Flow.Step.SiteIte
public import Kernels.FlashMlaSparseDecodeH64.Gen.StepWg1

@[expose] public section

/-! # The idle code's first event, and the walk to it

Warpgroup 1's idle code (pcs 2587–2605) is entered by the head's dispatch and by the lanes of the
MMA and TMA warps that lose their election. Its local prefix (pcs 2587–2595: the batch size's
load and test, the two length pointers' loads and tests) leads, depending on the launch, to its
first event (`idleFirst`): the return for a CTA beyond the batch, else the first length load the
set pointers ask for, else named barrier 12. `idleVal` is the register table there (the
pointers, the row's addresses in them, the barrier's id and count, else the entry table).

`IdleWalk.walk`: from pc 2587 with the batch row and the parameter pointer (`idleWk0`), local
steps reach the idle code's first event with its table. A role handing a lane to the idle code
composes its walk to pc 2587 with this one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The idle code's event sites. -/
inductive IdleSite where
  | ldA | ldB | bar | ret
  deriving DecidableEq

def IdleSite.pc : IdleSite → Nat
  | .ldA => 2596 | .ldB => 2601 | .bar => 2604 | .ret => 3611

section
variable (P : Params) (L : Launch) (g : Nat)

/-- After the top-k length's test: the extra length's load, or the barrier. -/
def idleAfterA : IdleSite :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then .bar else .ldB

/-- **The idle code's first event.** -/
def idleFirst : IdleSite :=
  if scmp .ge .s (r2W L g) (pw P.b) then .ret
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then idleAfterA P else .ldA

/-- The idle code's registers beyond the entry table. -/
def idleVals : List (Nat × Value) :=
  [(920, w32 (pw P.b)), (3015, .bits 64 (pw8 (P.topkLenBase.getD 0))),
   (3016, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))),
   (3106, .bits 64 (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3108, .bits 64 (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (923, w32 (i32 12)), (924, w32 (i32 384))]

/-- **The idle code's register table.** -/
def idleVal (r : Nat) : Value := ((idleVals P L g).lookup r).getD (entryVal L g r)

/-- The facts at an event of the idle code. -/
abbrev idleEnd (s : IdleSite) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live s.pc) (idleVal P L g)

/-- The facts at pc 2587: the batch row and the parameter pointer. -/
abbrev idleWk0 : List (Nat × Value) :=
  [(460, w32 (r2W L g)), (2991, .ptr 64 false (.param (param "0")) 0)]

/-- The facts after the two pointer loads (pc 2592). -/
abbrev idleWk2 : List (Nat × Value) :=
  (3016, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))) ::
    (3015, .bits 64 (pw8 (P.topkLenBase.getD 0))) :: idleWk0 L g

end

namespace IdleWalk

/-- No assumption gives an integer instruction a rule of its own at a pc outside the audited
parameter-pointer, shared-pointer and peer-score sites (`asms_localRule_int`). -/
scoped macro_rules
  | `(tactic| sym_local_none) => `(tactic| (
      intro t ht a ha
      exact asms_localRule_int (t := t) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (by simp [Assumptions.peerPackRule, Assumptions.peerPack, ht]) a ha))

/-- A branch on a parameter: decided by the case split's hypothesis up to unfolding. -/
scoped macro_rules
  | `(tactic| sym_decide) => `(tactic| first
      | assumption
      | exact Bool.eq_false_iff.mpr (by assumption))

/-- The walk's segments, closed by the table's terms. -/
scoped macro "idle_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The batch size's load (pc 2587). -/
theorem walk_b (hp : Pre P L m) :
    Seg kernel Assumptions.all L g 1 2587 (idleWk0 L g) 2588
      ((920, w32 (pw P.b)) :: idleWk0 L g) :=
  seg_ldp hp Flow.code_2587 (.inl ⟨rfl, rfl⟩) (by decide) (by decide)
    (by simp [p0fields]) (by simp) (by simp)

/-- Past the batch test, with the two pointer loads (pcs 2588–2591). -/
theorem walk_ptrs (hp : Pre P L m) (hb : ¬ scmp .ge .s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2588 ((920, w32 (pw P.b)) :: idleWk0 L g) 2592
      (idleWk2 P L g) := by
  refine Seg.comp_ex (q := 2590) (H := idleWk0 L g) (by seg_sym using idle_seg) ?_
  refine Seg.comp_ex (q := 2591)
    (H := (3015, .bits 64 (pw8 (P.topkLenBase.getD 0))) :: idleWk0 L g)
    ⟨1, seg_ldp hp Flow.code_2590 (.inr ⟨rfl, rfl⟩) (by decide) (by decide)
      (by simp [p0fields]) (by simp) (by simp)⟩ ?_
  exact ⟨1, seg_ldp hp Flow.code_2591 (.inr ⟨rfl, rfl⟩) (by decide) (by decide)
    (by simp [p0fields]) (by simp) (by simp)⟩

theorem walk_ret (hp : Pre P L m) (hb : scmp .ge .s (r2W L g) (pw P.b) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2587 (idleWk0 L g) 3611 (idleEnd P L g .ret) :=
  Seg.comp_ex ⟨1, walk_b hp⟩ (by seg_sym using idle_seg)

theorem walk_A (hp : Pre P L m) (hb : ¬ scmp .ge .s (r2W L g) (pw P.b) = true)
    (hA : ¬ eqz64 (pw8 (P.topkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2587 (idleWk0 L g) 2596 (idleEnd P L g .ldA) :=
  Seg.comp_ex ⟨1, walk_b hp⟩ (Seg.comp_ex (walk_ptrs hp hb) (by seg_sym using idle_seg))

theorem walk_B (hp : Pre P L m) (hb : ¬ scmp .ge .s (r2W L g) (pw P.b) = true)
    (hA : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (hB : ¬ eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2587 (idleWk0 L g) 2601 (idleEnd P L g .ldB) :=
  Seg.comp_ex ⟨1, walk_b hp⟩ (Seg.comp_ex (walk_ptrs hp hb) (by seg_sym using idle_seg))

theorem walk_bar (hp : Pre P L m) (hb : ¬ scmp .ge .s (r2W L g) (pw P.b) = true)
    (hA : eqz64 (pw8 (P.topkLenBase.getD 0)) = true)
    (hB : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true) :
    ∃ n, Seg kernel Assumptions.all L g n 2587 (idleWk0 L g) 2604 (idleEnd P L g .bar) :=
  Seg.comp_ex ⟨1, walk_b hp⟩ (Seg.comp_ex (walk_ptrs hp hb) (by seg_sym using idle_seg))

/-- **The walk from pc 2587 to the idle code's first event.** -/
theorem walk (hp : Pre P L m) :
    ∃ n, Seg kernel Assumptions.all L g n 2587 (idleWk0 L g) (idleFirst P L g).pc
      (idleEnd P L g (idleFirst P L g)) := by
  unfold idleFirst idleAfterA
  split_ifs with hb hA hB
  · exact walk_ret hp hb
  · exact walk_bar hp hb hA hB
  · exact walk_B hp hb hA hB
  · exact walk_A hp hb hA

end IdleWalk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
