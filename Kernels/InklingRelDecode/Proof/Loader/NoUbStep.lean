-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsLoop
public import Lemmas.Flow.LandsFor
import Kernels.InklingRelDecode.Proof.Loader.StepsEntry
import Kernels.InklingRelDecode.Proof.Loader.StepsBack
import Kernels.InklingRelDecode.Proof.Loader.StepsInc
import Kernels.InklingRelDecode.Proof.Loader.StepsLast
import Kernels.InklingRelDecode.Proof.Loader.StepsTest
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.Footprint
import Lemmas.Flow.TensorIssue

@[expose] public section

/-! # The strict steps of the loader's entry, block-table loads and last packet. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32
noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value}

theorem laneEq : compare .eq .b 32 (r32 (andi (BitVec.ofNat 64 (g % L.block)) 31)) (i32 0) =
      decide (laneOf L g = 0) := by
  unfold PTX.compare laneOf
  rw [decide_eq_decide]
  nf_simp [r32, andi, i32]
  omega

/-- Close the facts of a span from the register values of a typed counter. -/
macro "loader_norm" : tactic => `(tactic| (simp only [Nat.reduceBEq, valueOf, loopValue, bits,
    truncBits_idem, List.lookup, Arith32.shl, Arith32.r32, Arith32.i32, Arith32.mad32,
    Arith32.add32, Arith32.addi, Arith32.shru, replaceCounter, incValue, Arith32.andi,
    Arith32.not32, Arith32.mul32,
    quotient, Value.regBits, Option.getD_some, Nat.add_zero, beq_self_eq_true, ↓reduceIte] <;>
    first | rfl | exact congrArg Value.pred laneEq))

/-- The facts of the back edge's comparison. -/
macro "test_norm" : tactic => `(tactic| (simp only [Nat.reduceBEq, valueOf, loopValue, bits,
    nextCounter, replaceCounter, incValue, truncBits_idem, List.lookup, Option.getD_some,
    Value.regBits, beq_self_eq_true, ↓reduceIte, Arith32.r32, PTX.compare, decide_eq_decide,
    ne_eq, Int.ofNat_inj, BitVec.toNat_inj] <;> first | rfl |
    exact congrArg Value.pred (decide_eq_decide.mpr (not_congr eq_comm))))

theorem index_for (x y : BitVec 64) (a b : Value) :
    let regs := inputs Q L g rest
    Seg kernel Assumptions.all L g 14 2360 (factsFrom (Flow.live 2360)
      (entryValue Q L g w rest (.bits 32 x) (.bits 32 y) a b)) 2374
      ((code L g w regs).facts ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩) := by
  intro regs t ht
  dsimp only [code, entryValue] at ht ⊢
  seg_fp ht using loader_norm

theorem cmp_false {x y : BitVec 64}
    (hs : ¬ toSigned 32 (bits (.bits 32 y)) ≤ toSigned 32 (bits (.bits 32 x))) :
    Value.pred (compare .ge ((some IType.s).getD IType.b) 32 (truncBits 32 x) (truncBits 32 y)) =
      Value.pred false := by
  simp only [bits, Value.regBits, Option.getD_some] at hs
  simpa [PTX.compare, intOf] using hs

theorem cmp_true {x y : BitVec 64}
    (hs : toSigned 32 (bits (.bits 32 y)) ≤ toSigned 32 (bits (.bits 32 x))) :
    Value.pred (compare .ge ((some IType.s).getD IType.b) 32 (truncBits 32 x) (truncBits 32 y)) =
      Value.pred true := by
  simp only [bits, Value.regBits, Option.getD_some] at hs
  simpa [PTX.compare, intOf] using hs

theorem enter_for (x y : BitVec 64) (a b : Value)
    (hs : ¬ toSigned 32 (bits (.bits 32 y)) ≤ toSigned 32 (bits (.bits 32 x))) :
    let regs := inputs Q L g rest
    Seg kernel Assumptions.all L g 27 2347
      ((code L g w regs).facts ⟨.beginBar, .bits 32 x, .bits 32 y, a, b⟩) 2374
      ((code L g w regs).facts ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩) := by
  intro regs
  let F := (code L g w regs).facts ⟨.beginBar, .bits 32 x, .bits 32 y, a, b⟩
  have cmp : Seg kernel Assumptions.all L g 1 2347 F 2348 ((19, .pred false) :: F) := by
    intro t ht
    dsimp only [F, code] at ht ⊢
    seg_fp ht using (first | rfl | exact cmp_false hs)
  have br : Seg kernel Assumptions.all L g 1 2348 ((19, .pred false) :: F) 2349
      ((19, .pred false) :: F) := by
    intro u hu
    dsimp only [F, code] at hu ⊢
    seg_fp hu using rfl
  exact cmp.comp (br.comp ((setup_span (Q := Q) (L := L) (g := g) (w := w) (rest := rest)
    _ _ a b).comp (index_for x y a b)))

theorem leave_for (x y : BitVec 64) (a b : Value)
    (hs : toSigned 32 (bits (.bits 32 y)) ≤ toSigned 32 (bits (.bits 32 x))) :
    let regs := inputs Q L g rest
    Seg kernel Assumptions.all L g 2 2347
      ((code L g w regs).facts ⟨.beginBar, .bits 32 x, .bits 32 y, a, b⟩) 2419
      ((code L g w regs).facts ⟨.endBar, .bits 32 x, .bits 32 y, a, b⟩) := by
  intro regs
  let F := (code L g w regs).facts ⟨.beginBar, .bits 32 x, .bits 32 y, a, b⟩
  have cmp : Seg kernel Assumptions.all L g 1 2347 F 2348 ((19, .pred true) :: F) := by
    intro t ht
    dsimp only [F, code] at ht ⊢
    seg_fp ht using exact cmp_true hs
  have br : Seg kernel Assumptions.all L g 1 2348 ((19, .pred true) :: F) 2419
      ((code L g w regs).facts ⟨.endBar, .bits 32 x, .bits 32 y, a, b⟩) := by
    intro u hu
    dsimp only [F, code] at hu ⊢
    seg_fp hu using rfl
  exact cmp.comp br

theorem beginBar_for (x y : BitVec 64) (a b : Value) (e : Event) :
    (code L g w (inputs Q L g rest)).StepFor ⟨.beginBar, .bits 32 x, .bits 32 y, a, b⟩ e := by
  intro t u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2346)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have h0 := At.next (Code.at_of_atD ht rfl rfl)
  by_cases hs : toSigned 32 (bits (.bits 32 y)) ≤ toSigned 32 (bits (.bits 32 x))
  · obtain ⟨s, hr, hg⟩ := Code.landsFor (C := code L g w (inputs Q L g rest))
      (d := ⟨.endBar, .bits 32 x, .bits 32 y, a, b⟩) h0 (leave_for x y a b hs)
      (fun h => by cases h) rfl rfl
    exact .inl (.inr ⟨_, s, by simp [next, hs], hr, hg⟩)
  · obtain ⟨s, hr, hg⟩ := Code.landsFor (C := code L g w (inputs Q L g rest))
      (d := ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩) h0 (enter_for x y a b hs)
      (fun h => by cases h) rfl rfl
    exact .inl (.inr ⟨_, s, by simp [next, hs], hr, hg⟩)

/-- The strict step of a load of a typed word into a fresh register. -/
theorem recordFor {C : Flow.Code kernel Assumptions.all L g} (d : C.D) (dn : Value → C.D)
    {a : MemAccess} {r : Nat} {e : Event}
    (hc : kernel.code[C.pc d]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (hext : a.ext = .same) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = []) (hfree : ∀ q ∈ C.facts d, q.1 ≠ r)
    (hnext : ∀ x bs, C.next d ⟨C.pc d, .rd x bs⟩ = (rebuild 3 bs).toOption.map
      (fun v => some (dn v)))
    (hsub : ∀ v, C.sub (dn v) = 0) (hacc : ∀ v, C.acc (dn v) = [])
    (hinv : ∀ v, C.inv (dn v))
    (typed : ∀ x bs, e.kind = .rd x bs → ∀ v, rebuild 3 bs = .ok v → ∃ p, v = .bits 32 p)
    (span : ∀ p, Seg kernel Assumptions.all L g (C.pc (dn (.bits 32 p)) - C.pc d - 1)
      (C.pc d + 1) ((r, .bits 32 p) :: C.facts d) (C.pc (dn (.bits 32 p)))
      (C.facts (dn (.bits 32 p)))) : C.StepFor d e := by
  intro t u ins hat _ hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  rw [hr]
  cases hv : rebuild 3 bs with
  | error f =>
    refine .inr ⟨by rw [hnext, hv]; rfl, Machine.dead_of_fault (f := f) ?_⟩
    simp only [afterLoad, hv]
  | ok v =>
    obtain ⟨p, rfl⟩ := typed x bs rfl v hv
    have ht := Code.at_of_atD hat hs ha
    obtain ⟨_, hsub0, hacc0, _, _⟩ := id ht
    rw [afterLoad_ok hsub0 hacc0 hv]
    have heq : {setReg t r (.bits 32 p) with pc := t.pc + 1, sub := 0, acc := []} =
        PTX.next (setReg t r (.bits 32 p)) := by cases t; simp_all [PTX.next, setReg]
    rw [heq]
    obtain ⟨u, hrun, hu⟩ := Code.landsFor (C := C) (d := dn (.bits 32 p))
      (At.set ht hfree) (span p) (hinv _) (hsub _) (hacc _)
    exact .inl (.inr ⟨dn (.bits 32 p), u, by rw [hnext, hv]; rfl, hrun, hu⟩)


/-- **A block-table load of the loader, whose word is an integer, is strict.** -/
theorem page_for (upper : Bool) (i n a b : Value) (e : Event)
    (typed : ∀ x bs, e.kind = .rd x bs → ∀ v, rebuild 3 bs = .ok v → ∃ p, v = .bits 32 p) :
    (code L g w (inputs Q L g rest)).StepFor ⟨.page upper, i, n, a, b⟩ e := by
  cases upper
  · refine recordFor (C := code L g w (inputs Q L g rest)) ⟨.page false, i, n, a, b⟩
      (fun v => ⟨.warpBar 0, i, n, v, b⟩) Flow.code_2382 rfl rfl rfl rfl rfl rfl
      (by fact_free) ?_ (fun _ => rfl) (fun _ => rfl) (fun _ h => by cases h)
      typed ?_
    · intro x bs
      change ((rebuild 3 bs).toOption.bind _) = _
      cases rebuild 3 bs <;> rfl
    · intro p t ht
      dsimp only [code] at ht ⊢
      seg_fp ht using loader_norm
  · refine recordFor (C := code L g w (inputs Q L g rest)) ⟨.page true, i, n, a, b⟩
      (fun v => ⟨.warpBar 2, i, n, a, v⟩) Flow.code_2399 rfl rfl rfl rfl rfl rfl
      (by fact_free) ?_ (fun _ => rfl) (fun _ => rfl) (fun _ h => by cases h)
      typed ?_
    · intro x bs
      change ((rebuild 3 bs).toOption.bind _) = _
      cases rebuild 3 bs <;> rfl
    · intro p t ht
      dsimp only [code] at ht ⊢
      seg_fp ht using loader_norm

theorem inc_for (x y : BitVec 64) (a b : Value) :
    let regs := inputs Q L g rest
    let V := loopValue L g w regs ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩
    Seg kernel Assumptions.all L g 1 2413 (factsFrom (Flow.live 2413) V) 2414
      (factsFrom (Flow.live 2414) (replaceCounter V (incValue (.bits 32 x)))) := by
  intro regs V t ht
  dsimp only [V] at ht ⊢
  seg_fp ht using loader_norm

theorem ring_for (x y : BitVec 64) (a b : Value) :
    let regs := inputs Q L g rest
    Seg kernel Assumptions.all L g 9 2365 (loopFacts (L := L) (g := g) (w := w) (regs := regs)
      (.bits 32 x) (.bits 32 y) a b 2365) 2374
      ((code L g w regs).facts ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩) := by
  intro regs t ht
  dsimp only [loopFacts, code] at ht ⊢
  seg_fp ht using loader_norm

theorem test_for (x y : BitVec 64) (a b : Value) :
    let regs := inputs Q L g rest
    let N := loopValue L g w regs ⟨.poll, nextCounter (.bits 32 x), .bits 32 y, a, b⟩
    Seg kernel Assumptions.all L g 1 2417
      (factsFrom (Flow.live 2417) (replaceCounter N (incValue (.bits 32 x)))) 2418
      ((25, .pred (decide (r32 (bits (.bits 32 x) + 1) ≠ bits (.bits 32 y)))) ::
        factsFrom (Flow.live 2417) N) := by
  intro regs N t ht
  dsimp only [N] at ht ⊢
  seg_fp ht using test_norm

theorem loop_for (x y : BitVec 64) (a b : Value) :
    let regs := inputs Q L g rest
    let V := loopValue L g w regs ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩
    let C := code L g w regs
    let i : Value := .bits 32 x
    let n : Value := .bits 32 y
    Seg kernel Assumptions.all L g (if r32 (bits i + 1) = bits n then 6 else 15) 2413
      (factsFrom (Flow.live 2413) V) (C.pc (afterPacket i n a b))
      (C.facts (afterPacket i n a b)) := by
  intro regs V C i n
  let N := loopValue L g w regs ⟨.poll, nextCounter i, n, a, b⟩
  have front := (inc_for (Q := Q) (L := L) (g := g) (w := w) (rest := rest) x y a b).comp
    ((cursors_span (Q := Q) (L := L) (g := g) (w := w) (rest := rest) i n a b).comp
      (test_for (Q := Q) (L := L) (g := g) (w := w) (rest := rest) x y a b))
  by_cases h : r32 (bits i + 1) = bits n
  · simp only [h, ↓reduceIte, afterPacket]
    have last : Seg kernel Assumptions.all L g 1 2418
        ((25, .pred (decide (r32 (bits i + 1) ≠ bits n))) :: factsFrom (Flow.live 2417) N)
        (C.pc ⟨.endBar, nextCounter i, n, a, b⟩)
        (C.facts ⟨.endBar, nextCounter i, n, a, b⟩) := by
      intro t ht
      dsimp only [C, V, N, code] at ht ⊢
      have hfalse : decide (bits n ≠ bits n) = false := decide_eq_false (not_not_intro rfl)
      simp only [h, hfalse] at ht
      seg_fp ht using rfl
    exact Seg.of_len (front.comp last) (by norm_num)
  · simp only [h, ↓reduceIte, afterPacket]
    have last : Seg kernel Assumptions.all L g 1 2418
        ((25, .pred (decide (r32 (bits i + 1) ≠ bits n))) :: factsFrom (Flow.live 2417) N) 2365
        (loopFacts (L := L) (g := g) (w := w) (regs := regs) (nextCounter i) n a b 2365) := by
      intro t ht
      dsimp only [V, N, loopFacts] at ht ⊢
      rw [decide_eq_true h] at ht
      seg_fp ht using rfl
    exact Seg.of_len (front.comp (last.comp (ring_for (Q := Q) (L := L) (g := g) (w := w)
      (rest := rest) (r32 (bits i + 1)) y a b))) (by norm_num)

theorem copy_for (x y : BitVec 64) (a b : Value) (e : Event) :
    (code L g w (inputs Q L g rest)).StepFor ⟨.copy 3 true, .bits 32 x, .bits 32 y, a, b⟩ e := by
  intro t u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2412)
  obtain ⟨_, _, _, rfl, _⟩ := fires_cpTensor_issue hf
  have ht0 := At.next (Code.at_of_atD ht rfl rfl)
  have hp : At (PTX.next t) 2413 (factsFrom (Flow.live 2413)
      (loopValue L g w (inputs Q L g rest) ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩)) := by
    apply At.mono ht0
    obtain ⟨_, _, _, _, hR⟩ := ht0
    exact holds_factsFrom_mono hR (show ∀ r ∈ Flow.live 2413, r ∈ Flow.live 2412 by decide)
  obtain ⟨s, hτ, hs⟩ := Code.landsFor (C := code L g w (inputs Q L g rest))
    (d := afterPacket (.bits 32 x) (.bits 32 y) a b) hp (loop_for x y a b)
    (fun h => by unfold afterPacket at h; split at h <;> cases h)
    (by unfold afterPacket; split <;> rfl) (by unfold afterPacket; split <;> rfl)
  exact .inl (.inr ⟨_, s, rfl, hτ, hs⟩)

theorem elect_for (x y : BitVec 64) (a b : Value) (e : Event) :
    (code L g w (inputs Q L g rest)).StepFor ⟨.elect 3, .bits 32 x, .bits 32 y, a, b⟩ e := by
  let regs := inputs Q L g rest
  let C := code L g w regs
  intro t u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2409)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  let d : D := ⟨.elect 3, .bits 32 x, .bits 32 y, a, b⟩
  let lead : Value := .bits 32 (BitVec.ofNat 64 ld)
  obtain ⟨hpc, hsub, hacc, hflt, hR⟩ := (Code.at_of_atD ht rfl rfl : At t 2409 (C.facts d))
  let F := (609, lead) :: C.facts d
  have hs : At (setReg t 609 lead) 2409 F :=
    ⟨hpc, hsub, hacc, hflt, by simp [setReg], holds_update hR (by fact_free)⟩
  have fresh : ∀ q ∈ F, q.1 ≠ 24 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (by decide : 609 ≠ 24)
    · exact (show ∀ q ∈ C.facts d, q.1 ≠ 24 by fact_free) q hq
  by_cases h : laneOf L g = ld
  · let dn : D := ⟨.copy 3 false, .bits 32 x, .bits 32 y, a, b⟩
    have go : Seg kernel Assumptions.all L g 0 2410 ((24, .pred true) :: F)
        (C.pc dn) (C.facts dn) := by
      intro u hu
      dsimp only [F, C, d, dn, code] at hu ⊢
      seg_fp hu using rfl
    have ht2 := At.set (v := .pred true) hs fresh
    obtain ⟨s, hτ, hs⟩ := Code.landsFor (C := C) (d := dn) ht2 go (fun hh => by cases hh) rfl rfl
    rw [beq_iff_eq.mpr h]
    exact .inl (.inr ⟨dn, s, by simp [code, next, h, dn], hτ, hs⟩)
  · have ht2 := At.set (v := .pred false) hs fresh
    obtain ⟨_, seg⟩ := skipCopies (Q := Q) (L := L) (g := g) (w := w) (rest := rest)
      (.bits 32 x) (.bits 32 y) a b ld
    obtain ⟨u, hu⟩ := seg _ ht2
    have hp : At u 2413 (factsFrom (Flow.live 2413)
        (loopValue L g w regs ⟨.poll, .bits 32 x, .bits 32 y, a, b⟩)) := hu.2
    obtain ⟨s, hτ', hs⟩ := Code.landsFor (C := C) (d := afterPacket (.bits 32 x) (.bits 32 y) a b)
      hp (loop_for x y a b)
      (fun h => by unfold afterPacket at h; split at h <;> cases h)
      (by unfold afterPacket; split <;> rfl) (by unfold afterPacket; split <;> rfl)
    rw [beq_eq_false_iff_ne.mpr h]
    exact .inl (.inr ⟨_, s, by simp [code, next, h, finish_last], (run_rtg hu.1).trans hτ', hs⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
