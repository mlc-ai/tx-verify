-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiFacts
public import Lemmas.Flow.BranchU

@[expose] public section

/-! # The data step of the softmax-ready arrival

At the arrival (`arrS`, pc 1122) the block ends: the block's end values (`%r2492`, `%r2497`,
`%r2427`: the running maximum, sum and true maximum) become the carried statistics of the next
block (`dataNext`), the chain's flag is kept, and the next block's head (`bar0`) has the facts
`f_car` of them (`reach_1122`). -/

/-! # The loop's exit: the control segment from pc 1123 to the epilogue's first run

At the last block (`%r2426 = 0`, the counter the control machine holds as `cnt = 0` when its
`arrS` step leaves for `ebar0`) the rings' advance is skipped (the branch at pc 1124 on `%p113`
goes to pc 1143), the counters advance (`%r2426 = 1`, `%r2425 + 1`) and the branch at pc 1146 on
`%p117` (`%r2426 ≠ 1`, false) falls through to the epilogue's first run (pc 1147). The segment
keeps the ring parity `%rs313` (id 452), which that run reads. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The exit's control segment**: the parity survives to pc 1147. -/
theorem exitSeg (cnt bi ps : BitVec 64) (hz : scmpi .eq .b cnt 0 = true)
    (hb : scmpi .ne .b (addi cnt 1) 1 = false) :
    SegU kernel Assumptions.all L g 1123
      [(2884, w32 cnt), (2883, w32 bi), (452, .bits 16 ps)]
      1147 [(452, .bits 16 ps)] := by
  refine SegU.comp (b := 1124) (G := [(113, .pred (scmpi .eq .b cnt 0)), (2883, w32 bi),
    (452, .bits 16 ps), (2884, w32 cnt)]) (by ctl_seg) ?_
  rw [hz]
  refine SegU.comp (SegU.branch true Flow.code_1124 bra_rule noSegments.segFreePc) ?_
  refine SegU.comp (b := 1146) (G := [(117, .pred (scmpi .ne .b (addi cnt 1) 1)),
    (452, .bits 16 ps)]) (by ctl_seg) ?_
  rw [hb]
  exact SegU.branch false Flow.code_1146 bra_rule noSegments.segFreePc


/-- The reach from pc 1123 to pc 1154 from the carried facts. -/
theorem reach_exit_core (x : BitVec 64) (V : Nat → Value) (cnt bi ps : BitVec 64)
    (hz : scmpi .eq .b cnt 0 = true) (hb : scmpi .ne .b (addi cnt 1) 1 = false) :
    Reach kernel Assumptions.all L g 1123
      ([(2884, w32 cnt), (2883, w32 bi), (452, .bits 16 ps)] ++
        f_car x (V 2950) (V 2955) (V 2885) (V 2880)) (f_exit V) := by
  let W : Nat → Value :=
    lookupD ([(452, .bits 16 ps)] ++ f_car x (V 2950) (V 2955) (V 2885) (V 2880))
  have hW : Gen.e1_facts1 W = Gen.e1_facts1 V := rfl
  refine SegU.reach_then (q := 1147) (G := [(452, .bits 16 ps)] ++
      f_car x (V 2950) (V 2955) (V 2885) (V 2880))
      (SegU.frameSet rulesFrame (S :=
      [253, 254, 255, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134,
      1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149,
      1150, 1151, 1152, 1153]) (exitSeg cnt bi ps hz hb)
      (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)) ?_
  refine Reach.weaken_start (F := Gen.e1_facts0 W ++ [(2880, V 2880)]) (SegD.reach
    (SegD.frame (H := [(2880, V 2880)]) rulesFrame (Gen.e1_run L g W) rfl (by kernel_rfl)
      (by kernel_rfl) fun _ _ => w0SegFree _)
    Flow.code_1154 trivial rfl fun _ _ h => ?_) fun _ h => ?_
  · unfold f_exit
    rw [← hW]
    exact h
  · exact (holds_append _ _ _).mpr ⟨holds_lookupD (live := [452, 2885, 2950, 2955]) h
      (by kernel_rfl), holds_lookupD (live := [2880]) h (by kernel_rfl)⟩

/-- **The reach from pc 1123 to the epilogue's first barrier** at the last block: the first run
of the epilogue (pcs 1147-1153) from the block's end facts. -/
theorem reach_exit (x : BitVec 64) (m l mx sk : Value) (lo hi : List Value) (mw : Value)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Value × Value) (pm : Value) (vt : Bool) (cnt bi ps : BitVec 64)
    (hz : scmpi .eq .b cnt 0 = true) (hb : scmpi .ne .b (addi cnt 1) 1 = false) :
    Reach kernel Assumptions.all L g 1123
      ([(2884, w32 cnt), (2883, w32 bi), (452, .bits 16 ps)] ++
        (f_fin x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))
      (f_exit (lookupD (f_fin x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))) :=
  Reach.weaken_start (reach_exit_core x _ cnt bi ps hz hb) fun _ h =>
    (holds_append _ _ _).mpr ⟨((holds_append _ _ _).mp h).1,
      holds_lookupD (live := [467, 3243, 2950, 2955, 2885, 2880]) ((holds_append _ _ _).mp h).2
        (by kernel_rfl)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- After the arrival the control state is the next block's head or the epilogue's start. -/
theorem arrS_site {d : D} {e : Event} {c' : Control.D} (hs : d.c.site = .arrS)
    (h : Control.succ P L g w d.c e = some (some c')) : c'.site = .bar0 ∨ c'.site = .ebar0 := by
  simp only [Control.succ, hs] at h
  split at h
  · cases h; exact .inl rfl
  · cases h; exact .inr rfl

/-- Leaving for the epilogue means the block was the last: the counter is zero. -/
theorem exit_cnt {d : D} {e : Event} {c' : Control.D} (hs : d.c.site = .arrS)
    (h : Control.succ P L g w d.c e = some (some c')) (hb : c'.site = .ebar0) :
    scmpi .eq .b d.c.cnt 0 = true ∧ scmpi .ne .b (addi d.c.cnt 1) 1 = false := by
  simp only [Control.succ, hs] at h
  have hadv : (Control.advance d.c).cnt = addi d.c.cnt 1 := by
    unfold Control.advance; split <;> rfl
  rw [hadv] at h
  split at h
  · cases h; cases hb
  · rename_i hne
    have hne' : scmpi .ne .b (addi d.c.cnt 1) 1 = false := by simpa using hne
    refine ⟨?_, hne'⟩
    simp only [scmpi, addi, r32, i32, PTX.compare, truncBits] at hne' ⊢
    simp at hne' ⊢
    omega

/-- **The softmax-ready arrival** (pc 1122): the facts of the next block's head from the
block's end facts, and at the last block those of the epilogue's first barrier. -/
theorem ds_1122 : ∀ d : D, d.c.site = (.arrS) → DataStep (code P L g w) (dF L) d := by
  intro d hs
  refine DataStep.next (C' := code P L g w) (dF := dF L) (by rw [pc_eq hs]; exact Flow.code_1122)
    (by rw [pc_eq hs]; exact fun _ _ _ hf => Code.fires_arrive_next hf) ?_
  intro hi e d' t hn hat
  obtain ⟨c', hc', rfl⟩ := next_ctl hn
  cases hok : d.ok with
  | false =>
    refine .inl fun _ _ _ => ?_
    simp only [dF, dataNext, hs, hok]
    trivial
  | true =>
    obtain ⟨hp, hsb, ha, hf, hF⟩ := at_site (s := .arrS) hs hat (el0 hs hi rfl)
      (by rw [hok, Bool.or_true]) (fun h => by cases h)
    have hat' : At (PTX.next t) 1123 (wF (scX L) .arrS d.b) :=
      ⟨by simp only [PTX.next]; rw [hp]; rfl, hsb, ha, hf, hF⟩
    rcases arrS_site hs hc' with hb | hb
    · refine (reach_1122 L g (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
        (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm
        d.b.vt _ hat').imp_left fun h t' hr hs' => ?_
      have h' := h t' hr hs'
      simp only [dF, dataNext, hs, hok, ite_true]
      rw [hb]; exact h'
    · obtain ⟨hz, hnz⟩ := exit_cnt hs hc' hb
      have hctl : Holds t.regs (factsFrom (Control.ctlLive 1122)
          (Control.valueOf P L g w d.c)) := by
        obtain ⟨-, -, -, -, hAll⟩ := id hat
        have h0 := ((holds_append _ _ _).mp hAll).1
        change Holds t.regs (factsFrom (Control.ctlLive d.c.site.pc) _) at h0
        rw [hs] at h0
        exact h0
      have hc3 : Holds t.regs [(2884, w32 d.c.cnt), (2883, w32 d.c.bi),
          (452, .bits 16 d.c.ps)] :=
        holds_lookupD (live := [2884, 2883, 452]) hctl (by kernel_rfl)
      have hat'' : At (PTX.next t) 1123 ([(2884, w32 d.c.cnt), (2883, w32 d.c.bi),
          (452, .bits 16 d.c.ps)] ++ wF (scX L) .arrS d.b) :=
        ⟨hat'.1, hsb, ha, hf, (holds_append _ _ _).mpr ⟨hc3, hF⟩⟩
      refine (reach_exit (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
        (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm
        d.b.vt d.c.cnt d.c.bi d.c.ps hz hnz _ hat'').imp_left fun h t' hr hs' => ?_
      have h' := h t' hr hs'
      simp only [dF, dataNext, hs, hok, ite_true]
      rw [hb]; exact h'

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
