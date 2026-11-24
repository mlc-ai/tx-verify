-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoopAddr
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand

@[expose] public section

/-! # The back edge of the bias round -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi andi paramW sel xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32 ori w32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The bias wait reached on the loop back edge. -/
abbrev loopState (u : V) : D :=
  D.mk' (.ws .bias) { u with bt := addi u.bt (-1) }

private def loopLast (L : Launch) (g : Nat) (bt : BitVec 64) : List (Nat × Value) :=
  (2535, b32 L.sharedBase) ::
    factsFrom (loopWritten.filter fun r => r != 3964 && r != 4037) (loopOutput L g bt)

private theorem pwB_loop_finish (L : Launch) (g : Nat) (bt : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 5102 (factsFrom (loopKeys 14) (loopMid L g bt)) 5109
      (factsFrom loopWritten (loopOutput L g bt)) := by
  have h0 : Seg kernel Assumptions.all L g 3 5102 (factsFrom (loopKeys 14) (loopMid L g bt))
      5105 (loopLast L g bt) := by
    soft_seg
  have h1 := Seg.selpV (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (F := loopLast L g bt) (c := stg L g) Flow.code_5105 (by fact_mem)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
    (keys_ne (by kernel_rfl)) (fun t _ a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (Gen.segFree _ (by kernel_rfl)) rfl rfl
  have he :
      (if stg L g = true then .bits 16 (truncBits 16 (BitVec.ofInt 64 1))
        else .bits 16 (truncBits 16 (BitVec.ofInt 64 0)) : Value) =
        .bits 16 (sel16 (stg L g)) := by
    cases stg L g <;> rfl
  change ∃ n, Seg kernel Assumptions.all L g n 5105 (loopLast L g bt) 5106
    ((1050, _) :: loopLast L g bt) at h1
  simp only [DType.width] at h1
  rw [he] at h1
  refine Seg.comp_ex ⟨3, h0⟩ (Seg.comp_ex h1 ⟨3, ?_⟩)
  intro t ht
  seg_fp ht using
    cases hs : stg L g <;> simp only [loopOutput, sbSi, sbS, sel16, hs] <;> rfl

private theorem pwB_loop_words (L : Launch) (g : Nat) (bt : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 5032 (loopInput L g bt) 5109
      (factsFrom loopWritten (loopOutput L g bt)) :=
  Seg.comp_ex (pwB_loop_start L g bt) (Seg.comp_ex
    ⟨56, (pwB_loop_addrs1 L g bt).comp (pwB_loop_addrs2 L g bt)⟩ (pwB_loop_finish L g bt))

/-- The bias round's registers from the two words of the tile and the two values that read the
tile counter (`c`, `e`). -/
private def biasT (p : Params) (L : Launch) (g : Nat) (x y nb bp sp pp : BitVec 64)
    (c e : Value) : List (Nat × Value) :=
  [(631, .pred (stg L g)), (632, .pred (scmpi .ne .b (andi (tidW L g) 31) 0)),
   (1359, .bits 32 (x)), (1361, .bits 32 (y)),
   (3964, sbSi L g 80), (3965, sbSi L g 320), (3970, .bits 32 (tmS L g)),
   (3971, .bits 32 (ori (tmS L g) 96)), (3972, .bits 32 (ori (tmS L g) 32)),
   (3973, .bits 32 (ori (tmS L g) 64)), (3976, .bits 32 (rowSb L g)),
   (3977, .bits 32 (bOff L g)), (4037, .bits 32 (sbS L g)), (4170, .bits 32 (bAddr0 L g)),
   (4235, .bits 32 (sel (stg L g) (i32 12) (i32 11))), (4237, .bits 32 (sbS L g)),
   (4238, w32 (i32 1)), (634, c),
   (637, .pred (stg L g)), (4571, .bits 32 (statA L g)),
   (4821, .bits 32 (ori (tmS L g) 64)), (4822, .bits 32 (ori (tmS L g) 112)),
   (4823, .bits 32 (ori (tmS L g) 96)), (4824, .bits 32 (ori (tmS L g) 80)),
   (5097, .bits 32 (sbS L g)), (5098, w32 (i32 1)), (5117, .bits 32 (sbS L g)),
   (5118, w32 (i32 1)), (5119, sbSi L g 192),
   (7248, w32 nb), (7249, e), (7250, w32 bp), (7253, w32 sp), (7258, w32 pp),
   (7132, .bits 32 (paramW p.scaleLog2Bits)),
   (7896, joinValue (.bits 32 (paramW p.invScaleBits)) (.bits 32 (paramW p.invScaleBits)))] ++
  (List.range 14).map fun i => (3982 + 4 * i, .bits 32 (bAddr L g (bOffs.getD i 0)))

private theorem valuesBias_eq (v : V) : valuesBias p L g v =
    biasT p L g (r299 p L g v) (r301 p L g v) v.nb v.bpar v.spar v.ppar
      (.pred (Epilogue.scmp .lt .u v.bt (r301 p L g v))) (Mma.w32 v.bt) := rfl

private theorem biasT_carried (x y nb bp sp pp : BitVec 64) (c e c' e' : Value)
    (T R S : List (Nat × Value)) :
    factsFrom loopCarried (fun r => ((biasT p L g x y nb bp sp pp c e ++ T).lookup r).getD
      ((R.lookup r).getD ((S.lookup r).getD (.pred false)))) =
    factsFrom loopCarried (fun r => ((biasT p L g x y nb bp sp pp c' e' ++ T).lookup r).getD
      ((R.lookup r).getD ((S.lookup r).getD (.pred false)))) := by
  kernel_rfl

private theorem words_eq {v v' : V} (h1 : v'.sc = v.sc) (h2 : v'.ukw = v.ukw) :
    r299 p L g v' = r299 p L g v ∧ r301 p L g v' = r301 p L g v ∧
      valuesTile p L g v' = valuesTile p L g v := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [r299, r301, valuesTile, r169, r166, r168, r165, r1808, h1, h2]

private theorem valueOf_pwB (v : V) (r : Nat) : valueOf p L g (pwB v) r =
    ((valuesBias p L g v ++ valuesTile p L g v).lookup r).getD (((valuesRole p L g).lookup r).getD
      (((valuesStart p L g).lookup r).getD (.pred false))) := by
  unfold valueOf values; rfl

private theorem valueOf_wsB (v : V) (r : Nat) : valueOf p L g (D.mk' (.ws .bias) v) r =
    ((valuesBias p L g v ++ valuesTile p L g v).lookup r).getD (((valuesRole p L g).lookup r).getD
      (((valuesStart p L g).lookup r).getD (.pred false))) := by
  unfold valueOf values; rfl

private theorem loopCarried_of {v v' : V} (h1 : v'.sc = v.sc) (h2 : v'.ukw = v.ukw)
    (h3 : v'.nb = v.nb) (h4 : v'.bpar = v.bpar) (h5 : v'.spar = v.spar) (h6 : v'.ppar = v.ppar) :
    factsFrom loopCarried (valueOf p L g (pwB v)) =
      factsFrom loopCarried (valueOf p L g (D.mk' (.ws .bias) v')) := by
  obtain ⟨hx, hy, hT⟩ := words_eq (p := p) (L := L) (g := g) h1 h2
  rw [funext (valueOf_pwB v), funext (valueOf_wsB v'), hT, valuesBias_eq, valuesBias_eq, hx, hy,
    h3, h4, h5, h6]
  exact biasT_carried _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem loopCarried_eq (u : V) :
    factsFrom loopCarried (valueOf p L g (pwB u)) =
      factsFrom loopCarried (valueOf p L g (loopState u)) :=
  loopCarried_of rfl rfl rfl rfl rfl rfl

/-- The bias loop back edge needs only the carried control words to reach the next poll. -/
theorem biasLoopControl (u : V) :
    ∃ n, Seg kernel Assumptions.all L g n 5032
      (factsFrom ctlBE (valueOf p L g (pwB u))) 5109 (facts p L g (loopState u)) := by
  let W := valueOf p L g (pwB u)
  let U := valueOf p L g (loopState u)
  obtain ⟨n,h⟩ := seg_frame (lo := 5032) (hi := 5109) (H := factsFrom loopCarried W)
    (pwB_loop_words L g u.bt) (by kernel_rfl) (by kernel_rfl) (by decide) (by decide)
  refine ⟨n,(h.weaken_start fun R hr => ?_).weaken_end fun R hr => ?_⟩
  · apply (holds_append _ _ _).mpr
    rw [show loopInput L g u.bt = factsFrom loopInputs W by kernel_rfl]
    exact ⟨holds_factsFrom_mono hr (fun r hm => List.contains_iff_mem.mp (List.all_eq_true.mp
      (by kernel_rfl : loopInputs.all (ctlBE.contains ·) = true) r hm)),
      holds_factsFrom_mono hr (fun _ hm => (List.mem_filter.mp hm).1)⟩
  · obtain ⟨hw,hc⟩ := (holds_append _ _ _).mp hr
    rw [show factsFrom loopWritten (loopOutput L g u.bt) = factsFrom loopWritten U by
      kernel_rfl] at hw
    have hc' : Holds R (factsFrom loopCarried U) :=
      cast (congrArg (Holds R) (loopCarried_eq (p := p) (L := L) (g := g) u)) hc
    have ht : Holds R (factsFrom (loopWritten ++ loopCarried) U) :=
      (holds_append _ _ _).mpr ⟨hw,hc'⟩
    exact holds_factsFrom_mono ht (fun r hm => List.contains_iff_mem.mp (List.all_eq_true.mp
      (by kernel_rfl : (ctlLive 5109).all ((loopWritten ++ loopCarried).contains ·) = true) r hm))

/-- The loop re-entry updates the control words and carries the three statistics words. -/
theorem pwB_loop (v : V) (b : Bool) (r x : ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 5032 (pwBBranch p L g v b r x) 5109
      (factsD p L g (loopState (biasTailV v b r x))) := by
  let u := biasTailV v b r x
  let W := valueOf p L g (pwB u)
  let U := valueOf p L g (loopState u)
  let G : List (Nat × Value) := [(7251, mxVal u), (7257, .float .f32 x), (1230, negS p)]
  obtain ⟨n, h⟩ := seg_frame (lo := 5032) (hi := 5109) (H := factsFrom loopCarried W ++ G)
    (pwB_loop_words L g u.bt) (by kernel_rfl) (by kernel_rfl) (by decide) (by decide)
  refine ⟨n, (h.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · obtain ⟨_, hmax, hsum, _, hscale, hctl⟩ := hR
    refine (holds_append _ _ _).mpr ⟨?_, (holds_append _ _ _).mpr ⟨?_, hmax, hsum,
      hscale, trivial⟩⟩
    · rw [show loopInput L g u.bt = factsFrom loopInputs W by kernel_rfl]
      exact holds_factsFrom_mono hctl (fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp
        (by kernel_rfl : loopInputs.all (ctlBE.contains ·) = true) q hq))
    · exact holds_factsFrom_mono hctl (fun _ hq => (List.mem_filter.mp hq).1)
  · obtain ⟨hw, hr⟩ := (holds_append _ _ _).mp hR
    obtain ⟨hc, hG⟩ := (holds_append _ _ _).mp hr
    rw [show factsFrom loopWritten (loopOutput L g u.bt) = factsFrom loopWritten U by
      kernel_rfl] at hw
    have hc' : Holds R (factsFrom loopCarried U) :=
      cast (congrArg (Holds R) (loopCarried_eq (p := p) (L := L) (g := g) u)) hc
    have ht : Holds R (factsFrom (loopWritten ++ loopCarried) U) :=
      (holds_append _ _ _).mpr ⟨hw, hc'⟩
    refine land_run (G := G) (ctlK := ctlLive 5109) (fun q hq => ?_)
      (fun _ hr => valueOfD_ctl _ (List.mem_filter.mp hr).2) (by kernel_rfl) hG
      (holds_factsFrom_mono ht (fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp
        (by kernel_rfl : (ctlLive 5109).all ((loopWritten ++ loopCarried).contains ·) =
          true) q hq)))
    simp only [G, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
