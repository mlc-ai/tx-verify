-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Arrive
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.BiasN
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
import Kernels.InklingRelDecode.Flow.Code
import Kernels.InklingRelDecode.Gen.TypedLateLane00
import Kernels.InklingRelDecode.Gen.TypedLateLane01
import Kernels.InklingRelDecode.Gen.TypedLate00
import Kernels.InklingRelDecode.Gen.TypedLate01
import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreTail
@[expose] public section
/-! # The setup of the first block after the preloads: pcs 807 to 1049 -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The facts after the preloads: the entry's word and the scale, with the table of `pc`. -/
noncomputable abbrev PF (e : Control.Entry) (L : Launch) (g : Nat) (v : Control.Carry) (pc : Nat) :
    List (Nat × Value) :=
  Data.dF L ⟨⟨.pre 63, 0, v⟩, {}⟩ ++ factsFrom (Control.ctlLive pc)
    (Control.valueOf e L g ⟨.arrive, 0, v⟩)

/-- The facts at the end of the setup: the running maximum is the lowest word. -/
noncomputable abbrev PQ (e : Control.Entry) (L : Launch) (g : Nat) (v : Control.Carry) (pc : Nat) :
    List (Nat × Value) :=
  LF L {} pc (Control.valueOf e L g ⟨.arrive, 0, v⟩)

/-- The facts of the setup before the preloads: the entry's word, with the table of `pc`. -/
noncomputable abbrev BF (e : Control.Entry) (L : Launch) (g : Nat) (v : Control.Carry) (pc : Nat) :
    List (Nat × Value) :=
  Data.dF L ⟨⟨.bar0, 0, v⟩, {}⟩ ++ factsFrom (Control.ctlLive pc)
    (Control.valueOf e L g ⟨.bar0, 0, v⟩)

/-- The facts of the setup at the division: the dividend `1.0` of pc 599 is known. -/
noncomputable abbrev BD (e : Control.Entry) (L : Launch) (g : Nat) (v : Control.Carry) (pc : Nat) :
    List (Nat × Value) :=
  (804, b32 1065353216) :: BF e L g v pc

set_option hygiene false in
/-- The bounds the closers of the setup use. -/
macro "pre_setup" : tactic => `(tactic|
  (have tsmall : (g % L.block * 4) % 4294967296 = g % L.block * 4 := Nat.mod_eq_of_lt (by omega)
   have tsmall64 : (g % L.block * 4) % 18446744073709551616 = g % L.block * 4 :=
     Nat.mod_eq_of_lt (by omega)
   have hs : Lib.sx e.blocks < 2 ^ 64 := by
     unfold Lib.sx
     have := Nat.mod_lt e.blocks (by decide : 0 < 2 ^ 32)
     omega
   have := ok.blockWord
   have hl : e.limit < 2 ^ 32 := by
     have := ok.limitEq
     split at this <;> omega))

set_option hygiene false in
/-- A stretch of the setup from the facts `FA` to `FB`, run exactly (`Seg`). -/
macro "pre_seg " n:ident a:num b:num FA:ident ", " FB:ident " using " tac:tacticSeq : command => `(
theorem $n {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    Seg kernel Assumptions.all L g ($b - $a) $a ($FA e L g v $a) $b ($FB e L g v $b) := by
  pre_setup
  intro t ht
  simp only [BF, BD, PF, PQ, LF, Data.dF, Data.dFS, Data.inRound, Data.entryFact,
    Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using $tac)

set_option hygiene false in
/-- The typed check of a stretch that was run exactly. -/
macro "pre_typed " a:num b:num s:term : term => `(
  SegQ.tauAll _ (segQF_of_seg_typed lateQt (Ft := []) (n := $b - $a) $s rfl (by decide +kernel)
    (by decide +kernel) (AbsSound.mono (absF5_sound (fp3_of (L := L) (g := g) (a := $a)
    (b := $b) (by decide +kernel))) (by decide +kernel) (by decide +kernel)) trivial
    (by decide +kernel)))

set_option hygiene false in
/-- A stretch of the setup from the facts `FA` to `FB`, run exactly (`Seg`) and checked for the
tags at its two ends. -/
macro "pre_ex " n:ident a:num b:num FA:ident ", " FB:ident " using " tac:tacticSeq : command => `(
theorem $n {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) $a ($FA e L g v $a)
      $b ($FB e L g v $b) := by
  pre_setup
  refine SegQ.tauAll _ ?_
  first
  | refine segQF_of_seg_typed lateQt (Ft := []) (n := $b - $a) ?_ rfl (by decide +kernel)
      (by decide +kernel) (AbsSound.mono (absF5_sound (fp3_of (L := L) (g := g) (a := $a)
      (b := $b) (by decide +kernel))) (by decide +kernel) (by decide +kernel)) trivial
      (by decide +kernel)
  | refine SegQF.of_seg_frame Lib.rulesFrame ?_ rfl (by decide +kernel) (by decide +kernel)
      (PlainSegs.mono (fp3_of (L := L) (g := g) (a := $a) (b := $b)
      (by decide +kernel)).plain.plain.segs (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel)
  intro t ht
  simp only [BF, BD, PF, PQ, LF, Data.dF, Data.dFS, Data.inRound, Data.entryFact,
    Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using $tac)

theorem and12 (t : Nat) (h : t < 256) : t * 4 &&& 12 = t % 4 * 4 := by
  revert t h
  decide +kernel

set_option hygiene false in
macro "late_idx" : tactic => `(tactic|
  (simp only [Control.valueOf, Control.scalarValue, Control.u32, Nat.reduceEqDiff, ↓reduceIte]
   all_goals try nf_simp [and12 _ hT]
   all_goals omega))

pre_ex ps_808 808 809 PF, PF using late_idx
pre_ex ps_809 809 810 PF, PF using late_idx
theorem val_809 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 809 = b32 (g % L.block % 4 * 4) := by
  simp [Control.valueOf, Control.scalarValue]

theorem and12_val (t : Nat) (h : t < 256) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (t * 4)) &&& truncBits 32 (BitVec.ofInt 64 12)) =
      b32 (t % 4 * 4) := by
  revert t h
  decide +kernel

pre_ex ps_810 810 811 PF, PF using
  rw [val_809]
  exact and12_val _ hT
pre_ex ps_811 811 812 PF, PF using late_idx
pre_ex ps_812 812 814 PF, PF using
  first
  | (change _ = b64 (Lib.sx e.blocks % 2 ^ 64)
     rw [Nat.mod_eq_of_lt hs]
     exact Control.cvt_s64_s32 _)
  | (simp only [Control.valueOf, Control.scalarValue, Nat.reduceEqDiff, ↓reduceIte]
     apply congrArg (Value.bits 64)
     apply BitVec.eq_of_toNat_eq
     simp only [truncBits, BitVec.toNat_ofNat]
     omega)

/-- The packs of the bias words: the lane's windows keep the facts. -/
theorem ps_pack {v : Control.Carry} :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 814
      (PF e L g v 814) 943 (PF e L g v 943) := by
  refine SegQ.comp (b := 823) (G := PF e L g v 943) ?_ ?_
  · winh lw_l00_814
  refine SegQ.comp (b := 831) (G := PF e L g v 943) ?_ ?_
  · winh lw_l00_823
  refine SegQ.comp (b := 839) (G := PF e L g v 943) ?_ ?_
  · winh lw_l00_831
  refine SegQ.comp (b := 847) (G := PF e L g v 943) ?_ ?_
  · winh lw_l00_839
  · winh lw_l01_847

theorem shl7_val (a : Nat) :
    Value.bits 32 (if (truncBits 32 (BitVec.ofInt 64 7)).toNat ≥ 32 then 0
      else truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) <<<
        (truncBits 32 (BitVec.ofInt 64 7)).toNat)) = b32 (a * 128 % 2 ^ 32) := by
  have h7 : (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 := by decide
  simp only [h7]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [ge_iff_le, Nat.reduceLeDiff, ↓reduceIte, BitVec.toNat_ofNat]
  omega

pre_ex ps_943 943 944 PF, PF using
  simp only [Control.valueOf, Control.scalarValue, Control.u32, Nat.reduceEqDiff, ↓reduceIte]
  exact shl7_val _

pre_ex ps_944 944 946 PF, PQ using rfl
pre_ex ps_946 946 948 PQ, PQ using
  simp only [Control.valueOf, Control.scalarValue, Control.u32, Nat.reduceEqDiff, ↓reduceIte]
  first
  | decide
  | exact congrArg b32 (by have := ok.keyRange; omega)

/-- **The setup after the preloads** up to the test of the loop: pcs 807 to 1049. -/
theorem pre_to_test {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 807
      (PF e L g v 807) 1049 (PQ e L g v 1049) := by
  refine SegQ.comp (b := 808) (G := PF e L g v 808) ?_ ?_
  · exact segQ_single (d := 499) Flow.code_807 (by decide +kernel)
      (single_late (by decide +kernel)) (sub_facts (fun _ h => h) (by decide +kernel))
      (rf_ne (fun p hp => by
        simp only [Data.dF, Data.dFS, Data.entryFact, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl <;> simp) (by decide +kernel))
  refine SegQ.comp (b := 809) (G := PF e L g v 809) (ps_808 hT ok) ?_
  refine SegQ.comp (b := 810) (G := PF e L g v 810) (ps_809 hT ok) ?_
  refine SegQ.comp (b := 811) (G := PF e L g v 811) (ps_810 hT ok) ?_
  refine SegQ.comp (b := 812) (G := PF e L g v 812) (ps_811 hT ok) ?_
  refine SegQ.comp (b := 814) (G := PF e L g v 814) (ps_812 hT ok) ?_
  refine SegQ.comp (b := 943) (G := PF e L g v 943) ps_pack ?_
  refine SegQ.comp (b := 944) (G := PF e L g v 944) (ps_943 hT ok) ?_
  refine SegQ.comp (b := 946) (G := PQ e L g v 946) (ps_944 hT ok) ?_
  refine SegQ.comp (b := 948) (G := PQ e L g v 948) (ps_946 hT ok) ?_
  refine SegQ.comp (b := 1049) (G := PQ e L g v 948) (SegQ.tauAll _ (SegQF.jmpS (qt := lateQt)
    Flow.code_948 (fun t _ a ha => Lib.bra_rule t a ha) (segFree (by decide)) (by decide +kernel)))
    ?_
  exact SegQ.weaken fun _ h => holds_of_forall fun p hp => holds_mem h
    (sub_facts (fun _ h => h) (by decide +kernel) p hp)

pre_ex ps_1049 1049 1050 PQ, PQ using late_loop

/-- **The setup after the preloads and the route**: from pc 807 to the site that follows. -/
theorem pre_route {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 807
      (PF e L g v 807) (Control.loopSite e (g % L.block) 0).pc
      (RF e L g (b32 4286578688) 0 v (Control.loopSite e (g % L.block) 0).pc) := by
  refine (pre_to_test hT ok).comp ((ps_1049 hT ok).comp ?_)
  by_cases h1 : 0 = e.limit
  · have hs : Control.loopSite e (g % L.block) 0 = .epilogue := by simp [Control.loopSite, h1]
    rw [hs]
    exact route_to_epi _ ok h1
  · by_cases h2 : Control.nextEnabled e (g % L.block) 0 = true
    · have hs : Control.loopSite e (g % L.block) 0 = .nxt 0 := by
        simp [Control.loopSite, h1, h2]
      rw [hs]
      exact route_to_nxt _ ok (by omega) h1
    · have hs : Control.loopSite e (g % L.block) 0 = .waitS := by
        simp [Control.loopSite, h1, h2]
      rw [hs]
      exact route_to_wait _ ok (by omega) h1 (by simpa using h2)

theorem pre_last_ld : ldOk 806 85 326 = true := by decide +kernel

theorem pre_last_aft : afterF lateQt 806 [] = true := by decide +kernel

theorem pre_last_nk : 326 ∉ (lateQt 807).map Prod.fst := by decide +kernel

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The words after the last preload: the maximum starts at the lowest word. -/
def preW (w : Data.Vals) (y : Value) : Data.Vals :=
  { w with
    m := b32 4286578688, l := b32 0, cur := Function.update w.ld 63 y,
    ld := fun _ => Data.dflt }

/-- **The last preload continues** at the loop's first site, past the setup. -/
theorem sstep_pre_last (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.pre 63, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => ?_
  obtain ⟨rfl, -⟩ := hinv.pre 63 rfl
  have hb : Data.loopB (Control.loopSite e (g % L.block) 0) := by
    rcases loopSite_cases e (g % L.block) 0 with h | h | h <;> simp [Data.loopB, h]
  apply ld_soft (d := ⟨⟨.pre 63, 0, v⟩, w⟩) (p := 806) (r := 326)
    (f := fun y => ⟨⟨Control.loopSite e (g % L.block) 0, 0, v⟩, preW w y⟩) rfl pre_last_ld
    ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩ ?_ ?_ ?_ pre_last_aft pre_last_nk (fun y => ?_)
  · exact facts_ne (by dsimp only; decide +kernel) (by
      simp only [Data.dKeys, List.mem_cons, List.not_mem_nil, or_false]
      omega)
  · intro x bs y hy
    simp [Data.succ, Control.next, Data.record, Lib.loadWord, hy, hb, Except.toOption, preW]
  · intro y hi
    exact Control.loop_inv (i := 0) hi.entry hi.thread hi.bound
  · refine SegQ.fromFacts (F' := PF e L g v 807) ?_ (SegQ.endIn (pre_route hinv.thread hinv.entry)
      fun p hp => ?_)
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
        simp only [Data.dF, Data.dFS] at h ⊢
        exact h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        have k : ∀ r ∈ Control.ctlLive 807, r ∈ Control.ctlLive 806 := by decide +kernel
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (mem_factsFrom (k r hr)))
    · rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (dF_loop e (g % L.block) 0 _ _ _ p h)
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
