-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Machine

@[expose] public section

/-! # The startup's obligations

Every state of the startup machine other than its exits satisfies its step obligation, by
`site_cases`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Startup
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The startup's segments, as the output warp's. -/
macro "st_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

/-- No assumption gives the tensor-map prefetch a rule of its own. -/
theorem asms_prefetch_none {L : Launch} {g : Nat} {t : TState} {gen : Bool} {w r : Nat} :
    ∀ b ∈ Assumptions.all, b.localRule L g t (.prefetchTensorMap gen w (.reg r)) = none := by
  intro a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The tensor-map prefetch of warp 0** (pcs 39, 41, 43): a hint with no effect on the state,
given the map parameter's object (`Pre.maps`). -/
theorem seg_prefetch (hp : Pre p L m) {pc r i a : Nat}
    {F : List (Nat × Value)}
    (hi : (i, a) ∈ [(9, p.qMapAddress), (10, p.oMapAddress), (11, p.biasMapAddress)])
    (hc : kernel.code[pc]? = some ⟨none, .prefetchTensorMap true 64 (.reg r)⟩)
    (hr : (r, .ptr 64 true (.param (param i)) 0) ∈ F) (hpc : pc ∉ Assumptions.swExp2Sites) :
    Seg kernel Assumptions.all L g 1 pc F (pc + 1) F := by
  have hm : L.paramObjects (param i) = some (mapParam i, a) ∧ a % 64 = 0 ∧ a + 128 ≤ 2 ^ 64 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2, h3, -⟩ := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp); exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := hp.maps 10 p.oMapAddress ⟨3, p.oMap⟩ (by simp); exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
      exact ⟨h1, h2, h3⟩
  exact Seg.prefetchTensorMap hc hr (.inr rfl) hm.1
    ⟨rfl, by simp [mapParam, ParamObjectDecl.bytes], by simp [mapParam],
      by simpa [mapParam] using hm.2.1, by simpa [mapParam, ParamObjectDecl.bytes] using hm.2.2⟩
    (fun _ _ => asms_prefetch_none) (Epilogue.segFree hpc)

/-- The value of a map parameter's generic pointer after `cvta.param`. -/
abbrev mapPtr (i : Nat) : Value := .ptr 64 true (.param (param i)) 0

/-- The branch at pc 37 or 45 on a predicate the facts give as false. -/
theorem seg_skip {pc tgt q : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (q, false), .bra tgt false⟩)
    (hq : (q, Value.pred false) ∈ F) (hpc : pc ∉ Assumptions.swExp2Sites) :
    Seg kernel Assumptions.all L g 1 pc F (pc + 1) F := by
  have h := Seg.bra (L := L) (g := g) (uni := false) hc hq
    (fun t _ a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (Epilogue.segFree hpc)
  simpa using h

/-- The warp-zero test's facts. -/
abbrev zf (q : Nat) (F : List (Nat × Value)) : List (Nat × Value) := (q, .pred false) :: F

/-- **Warp 0's path from the third shuffle to its first election** (pcs 36 to 46): the code's
own steps (`h₁ … h₆`, by `seg_fp`), the two tests of the warp index against zero, which the
recorded word `x` fails (`hx`), and the three prefetches (`seg_prefetch`). -/
theorem seg_warp0 (hp : Pre p L m) {F G : List (Nat × Value)} {x : BitVec 64}
    (hx : Epilogue.scmpi .ne .b x 0 = false)
    (h1 : Seg kernel Assumptions.all L g 1 36 F 37
      ((18, .pred (Epilogue.scmpi .ne .b x 0)) :: F))
    (h2 : Seg kernel Assumptions.all L g 1 38 (zf 18 F) 39 ((7507, mapPtr 9) :: zf 18 F))
    (h3 : Seg kernel Assumptions.all L g 1 40 ((7507, mapPtr 9) :: zf 18 F) 41
      ((7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F))
    (h4 : Seg kernel Assumptions.all L g 1 42 ((7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F)
      43 ((7509, mapPtr 11) :: (7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F))
    (h5 : Seg kernel Assumptions.all L g 1 44
      ((7509, mapPtr 11) :: (7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F) 45
      ((19, .pred (Epilogue.scmpi .ne .b x 0)) ::
        (7509, mapPtr 11) :: (7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F))
    (h6 : Seg kernel Assumptions.all L g 0 46
      (zf 19 ((7509, mapPtr 11) :: (7508, mapPtr 10) :: (7507, mapPtr 9) :: zf 18 F)) 46 G) :
    Seg kernel Assumptions.all L g 10 36 F 46 G := by
  rw [hx] at h1 h5
  refine (h1.comp ((seg_skip Flow.code_37 (by simp) (by decide)).comp (h2.comp
    ((seg_prefetch hp (i := 9) (a := p.qMapAddress) (by simp) Flow.code_39 (by simp)
      (by decide)).comp (h3.comp
    ((seg_prefetch hp (i := 10) (a := p.oMapAddress) (by simp) Flow.code_41 (by simp)
      (by decide)).comp (h4.comp
    ((seg_prefetch hp (i := 11) (a := p.biasMapAddress) (by simp) Flow.code_43 (by simp)
      (by decide)).comp (h5.comp ((seg_skip Flow.code_45 (by simp) (by decide)).comp
      h6)))))))))).of_len rfl

macro "pf_seg" : tactic =>
  `(tactic| refine seg_warp0 ‹_› (Bool.eq_false_of_ne_true ‹_›) (by st_seg) (by st_seg)
    (by st_seg) (by st_seg)
    (by st_seg) (by st_seg))

theorem stepAt_sh (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ j, d.site = .sh j) :
    (code p L g).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, x1, x2, x3⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, afterBlock, enterOf]
    seg_by (first | pf_seg | st_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_elect (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ j, d.site = .elect j) :
    (code p L g).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, x1, x2, x3⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, afterBlock, enterOf]
    seg_by (first | pf_seg | st_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_init (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ n, d.site = .init n) :
    (code p L g).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, x1, x2, x3⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, afterBlock, enterOf]
    seg_by (first | pf_seg | st_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

theorem stepAt_fence (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .fence ∨ d.site = .bar) :
    (code p L g).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, x1, x2, x3⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32, afterBlock, enterOf]
    seg_by (first | pf_seg | st_seg) inv_by (exact fun _ => trivial) guard_by (trivial)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Startup
