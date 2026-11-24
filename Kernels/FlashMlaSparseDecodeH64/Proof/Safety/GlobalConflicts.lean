-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.FinalOutput
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TensorAccessAllocation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace

@[expose] public section

/-! # Global memory accesses have disjoint inputs and unique output writers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.AsyncCopy Wg0 Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def InRange (base size : Nat) (l : Loc) : Prop :=
  base ≤ l.addr ∧ l.addr < base + size

private theorem ranges_disjoint {a b n m : Nat} {l : Loc} (h : Apart n m a b)
    (ha : InRange a n l) (hb : InRange b m l) : False := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  unfold Apart at h
  omega

private theorem one_byte {a : Acc} {l : Loc} (hc : a.Covers l) (hOne : a.size = 1) :
    a.loc = l := by
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hc
  have hAddr : a.loc.addr = l.addr := by omega
  cases hLoc : a.loc
  cases l
  rw [hLoc] at hSpace hCta hAddr
  rw [Loc.mk.injEq]
  exact ⟨hSpace.symm, hCta.symm, hAddr⟩

private inductive GlobalClass (P : Params) (X : Execution) (a : Acc) (l : Loc) :
    Ref → Bool → Prop
  | input : ¬ InRange P.outBase (tensorBytes P) l → ¬ InRange P.lseBase (lseBytes P) l →
      GlobalClass P X a l ref false
  | lse : X.Writes i a bs → InRange P.lseBase (lseBytes P) l →
      GlobalClass P X a l (.thread i) true
  | output : X.TensorStoreIssue i addr sp → TensorStore.writeLoc sp x y b = some l →
      InRange P.outBase (tensorBytes P) l →
      GlobalClass P X a l (.async i (.write (.store x y b))) true

private theorem classify_global (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {ref : Ref} {a : Acc} {w : Bool} {l : Loc} (hGlobal : l.space = .global)
    (hInt : X.Intent ref a w) (hc : a.Covers l) : GlobalClass P X a l ref w := by
  have hSpace := hc.1.symm.trans hGlobal
  cases ref with
  | thread i =>
    change X.Access i a w at hInt
    have hNo (tag : Nat) (ap : Acc) (old : List (Option Byte)) (new : Option (List Byte)) :
        X.get i ≠ some ⟨tag, .rmw ap old new⟩ :=
      fun he => GlobalWrites.no_rmw hX ⟨tag, he⟩
    rcases (Execution.access_iff_of_not_rmw hNo).mp hInt with ⟨bs, hr, rfl⟩ | ⟨bs, hw, rfl⟩
    · have hShared := (OrdinaryReadWindow.read_window hpre hX hs ht hr).1
      rw [hShared] at hSpace
      cases hSpace
    · obtain ⟨_, _, _, hLoc, hSize, _⟩ := GlobalWrites.lse_write hpre hs hX ht hw hSpace
      have hg := Frame.lt_of_get hX hw.choose_spec
      change a.loc.InRange a.size l at hc
      rw [hLoc, hSize, lseLocOf_eq] at hc
      exact .lse hw (lseRange (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg)
        (Nat.mod_lt _ (by decide)) hc)
  | async i p =>
    obtain ⟨rfl, hf⟩ := hInt
    cases p <;> try contradiction
    case readLoad x y b =>
      obtain ⟨s, address, hi, hl, hOne⟩ := hf
      rw [one_byte hc hOne] at hl
      rcases tensor_load_input_range hpre hX hs ht hi hl with h | h | ⟨hExtra, h⟩
      · exact .input (ranges_disjoint hpre.qApartO h) (ranges_disjoint hpre.inputApartLse h)
      · exact .input (ranges_disjoint hpre.kvApartO h) (ranges_disjoint hpre.kvApartLse h)
      · exact .input (ranges_disjoint (hpre.extraKvApartO.resolve_left hExtra) h)
          (ranges_disjoint (hpre.extraKvApartLse.resolve_left hExtra) h)
    case readStore x y b =>
      obtain ⟨s, address, hi, hLoc, _⟩ := hf
      obtain ⟨d, j, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hi
      have hg := Frame.lt_of_get hX hi.choose_spec
      rw [(Wg0OutputTrace.tileSpec hpre hX (hs i.1 hg).machine hi hd hSite).2] at hLoc
      unfold TensorStore.readLoc at hLoc
      cases hSlot : TensorTransfer.slotAt (outputSpec P L i.1 j).descriptor x y b with
      | none => simp [hSlot] at hLoc
      | some slot =>
        rw [hSlot, Option.map_some] at hLoc
        have hShared : a.loc.space = .shared := by rw [← Option.some.inj hLoc]; rfl
        rw [hShared] at hSpace
        cases hSpace
    case readPrefetch =>
      obtain ⟨_, _, hi, _, _⟩ := hf
      exact (TensorLoadSources.no_tensor_prefetch hX hi).elim
    case readCopy =>
      rcases hf with ⟨_, hi, _⟩ | hi
      · exact (GlobalWrites.no_copy hX hi).elim
      · exact (GlobalWrites.no_bulk_prefetch hX hi).elim
    case writeLoad =>
      obtain ⟨_, _, hi, hLoc, _⟩ := hf
      have hShared := (TensorSharedBounds.write_loc_windows hpre hX hs ht hi hLoc).1
      rw [hShared] at hSpace
      cases hSpace
    case writeStore x y b =>
      obtain ⟨_, _, hi, hLoc, hOne⟩ := hf
      rw [one_byte hc hOne] at hLoc
      obtain ⟨_, j, _, _, hWarp, hx, hy, hb, hDest⟩ := output_destination hpre hs hX ht hi hLoc
      have hg := Frame.lt_of_get hX hi.choose_spec
      refine .output hi hLoc (outputRange (e := eOf L i.1) (q := qOf L i.1)
        (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg) hy
        (outputColumn_lt j hWarp hx) hb ?_)
      rw [← hDest]
      exact ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
    case oldStore =>
      obtain ⟨_, _, hi, hReduce, _, _⟩ := hf
      obtain ⟨d, j, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hi
      have hg := Frame.lt_of_get hX hi.choose_spec
      rw [(Wg0OutputTrace.tileSpec hpre hX (hs i.1 hg).machine hi hd hSite).2] at hReduce
      cases hReduce
    case writeCopy =>
      obtain ⟨_, hi, _⟩ := hf
      exact (GlobalWrites.no_copy hX hi).elim
    case writeElem =>
      obtain ⟨_, hi, _⟩ := hf
      exact (GlobalWrites.no_copy hX hi).elim
    case oldElem =>
      obtain ⟨_, _, hi, _⟩ := hf
      exact (GlobalWrites.no_copy hX hi).elim
    case writeCta =>
      obtain ⟨_, _, hi, _, _⟩ := hf
      exact (GlobalWrites.no_clc hX hi).elim
    case mmaRead =>
      have hShared := (MmaAccessWindow.footprint hpre hX hs ht hf.2).2.1
      rw [hShared] at hSpace
      cases hSpace

/-- No two distinct conflicting intents share a global byte, even when one is still pending. -/
theorem no_global_conflict (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {e f : Ref} {a b : Acc} {l : Loc} (hGlobal : l.space = .global)
    (hConflict : Conflict X e f a b) (ha : a.Covers l) (hb : b.Covers l) : False := by
  obtain ⟨hne, we, wf, he, hf, hWrites, _⟩ := hConflict
  have hc := classify_global hpre hX hs ht hGlobal he ha
  have hd := classify_global hpre hX hs ht hGlobal hf hb
  cases hc with
  | input hOut hLse =>
    cases hd with
    | input => simp at hWrites
    | lse _ h => exact hLse h
    | output _ _ h => exact hOut h
  | lse hw h =>
    cases hd with
    | input _ hLse => exact hLse h
    | lse hw' _ =>
      exact hne (congrArg Ref.thread (lse_writer_unique hpre hs hX ht hGlobal hw hw' ha hb))
    | output _ _ h' => exact ranges_disjoint hpre.outApartLse h' h
  | output hi hLoc h =>
    cases hd with
    | input hOut _ => exact hOut h
    | lse _ h' => exact ranges_disjoint hpre.outApartLse h h'
    | output hi' hLoc' _ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := output_destination_unique hpre hs hX ht hi hi' hLoc hLoc'
      exact hne rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
