-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's start and the head of an item

From `setmaxnreg`: the first item's coordinates (two `FastDivmod` chains), the KV tile count
(the signed ceiling of `seqlen_k / 128`; the segment is cut at its `selp`, whose predicate is
false under `Pre`, `seqlen_k` being a multiple of 128), the Q full barriers' addresses with the
peer-bit mask, the branch past the item loop (`Work.start_branch`), and on entering the loop the
CTA's `.shared::cluster` window (`cvta`, `cvta.to.shared::cluster`, cut at each) and the four Q
destinations (shared pointer plus an immediate, cut at each). At an item's head the rank
broadcast gives the K/V and Q rows. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The first state of the item loop. -/
abbrev d0 : D := ⟨.head, 0, 0, 0, 1, 1⟩

/-- From `setmaxnreg` to the ceiling's `selp`. -/
theorem start_a (hpre : Pre P L mem0) (d : D) :
    Seg kernel asms L g 23 195 (factsAt L g 194 d) 218 (factsAt L g 218 d0) := by
  intro t h
  have hsh := shape hpre
  seg_fp h using
    try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]
    all_goals first
      | w_rfl
      | (simp only [batchW, qbW, quotW, workW]
         rw [mulHiW_comm (BitVec.ofNat 64 (cid L g))]
         unfold_w
         rfl)
      | norm_signed [Prologue.sb]

/-- From the `selp` to the branch past the item loop, through the two peer-bit masks. -/
theorem start_b (hpre : Pre P L mem0) (hg : g < L.threads) :
    Seg kernel asms L g (4 + (1 + (2 + (1 + 4)))) 218 (factsAt L g 218 d0) 230
      (factsAt L g 230 d0) := by
  have hb := (shape hpre).1
  have h1 : Seg kernel asms L g 4 218 (factsAt L g 218 d0) 222 (factsAt L g 222 d0) :=
    fun t h => by loader_seg h hpre
  have h2 := seg_peer (L := L) (g := g) (F := factsAt L g 222 d0) (k := 0) hpre hg Flow.code_222
    (by decide) (tbl_mem (r := 337) (by live_dec)
      (by simp only [valueOf, table, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit,
        Option.getD_some, Option.getD_none])) (by omega) (facts_ne (by live_dec))
  have h3 : Seg kernel asms L g 2 223 ((353, peerV L g 0) :: factsAt L g 222 d0) 225
      (factsAt L g 225 d0) := fun t h => by loader_seg h hpre
  have h4 := seg_peer (L := L) (g := g) (F := factsAt L g 225 d0) (k := 8) hpre hg Flow.code_225
    (by decide) (tbl_mem (r := 354) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])) (by omega)
      (facts_ne (by live_dec))
  have h5 : Seg kernel asms L g 4 226 ((355, peerV L g 8) :: factsAt L g 225 d0) 230
      (factsAt L g 230 d0) := fun t h => by loader_seg h hpre
  exact Seg.comp h1 (Seg.comp h2 (Seg.comp h3 (Seg.comp h4 h5)))

/-- The CTA's shared base as a generic and as a `.shared::cluster` pointer. -/
abbrev genP (L : Launch) (g : Nat) : Value :=
  .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 L.sharedBase)
abbrev clP (L : Launch) (g : Nat) : Value :=
  .ptr 64 false (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 (BitVec.ofNat 64 L.sharedBase).toNat)

/-- On entering the item loop: the window pointer and the four Q destinations, to the head. -/
theorem start_c (hpre : Pre P L mem0) (hg : g < L.threads) :
    Seg kernel asms L g (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 10)))))))) 231
      (factsAt L g 230 d0) 249 (facts L g d0) := by
  have hb := (shape hpre).1
  have hcta : g / L.block < L.grid := cta_lt hg
  have h1 : Seg kernel asms L g 1 231 (factsAt L g 230 d0) 232 (factsAt L g 232 d0) :=
    fun t h => by loader_seg h hpre
  have h2 : Seg kernel asms L g 1 232 (factsAt L g 232 d0) 233
      ((4070, genP L g) :: factsAt L g 232 d0) :=
    seg_one Flow.code_232 rfl (fun t h => exec_cvtaShared
      (hL := asms_localRule_none) (cl := false) (readSharedAddress_bits
      (holds_mem h.2.2.2.2 (tbl_mem (r := 4069) (by live_dec)
        (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])))
      (.inr rfl) hg hcta (x := L.sharedBase) (show L.sharedBase < 2 ^ 32 by omega)))
      (facts_ne (by live_dec))
  have h3 : Seg kernel asms L g 1 233 ((4070, genP L g) :: factsAt L g 232 d0) 234
      ((4071, clP L g) :: (4070, genP L g) :: factsAt L g 232 d0) :=
    seg_one Flow.code_233 rfl (fun t h => exec_cvtaShared
      (hL := asms_localRule_none) (readSharedAddress_ptr
      (holds_mem h.2.2.2.2 (List.mem_cons_self ..)) (.inr rfl) hg hcta rfl (.inl rfl) (.inl rfl)
      (by simp only [BitVec.toNat_ofNat]; omega)))
      (cons_ne (ex := [(4070, _)]) (by simp) (by live_dec))
  have h4 : Seg kernel asms L g 1 234 ((4071, clP L g) :: (4070, genP L g) ::
      factsAt L g 232 d0) 235 (factsAt L g 235 d0) := fun t h => by
    seg_fp h using
      try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]
      simp only [win, ctaOf, BitVec.toNat_ofNat, Nat.add_zero, Value.ptr.injEq, true_and]
      congr 1
      omega
  have hw : valueOf L g d0 356 =
      .ptr 32 false (.shared (ctaOf L g) (ctaOf L g)) (BitVec.ofNat 64 (L.sharedBase + 0)) := by
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, win]
  have hm : (356, Value.ptr 32 false (.shared (ctaOf L g) (ctaOf L g))
      (BitVec.ofNat 64 (L.sharedBase + 0))) ∈ factsAt L g 235 d0 :=
    tbl_mem (by live_dec) hw
  let ptr (k : Nat) : Value :=
    .ptr 32 false (.shared (ctaOf L g) (ctaOf L g)) (BitVec.ofNat 64 (L.sharedBase + 0 + k))
  have h5 : Seg kernel asms L g 1 235 (factsAt L g 235 d0) 236
      ((357, ptr 68608) :: factsAt L g 235 d0) :=
    seg_one Flow.code_235 rfl (fun t h => exec_add_sharedPtr
      (hL := asms_localRule_none) (k := 68608) (holds_mem h.2.2.2.2 hm)
      (.inl rfl) (by omega) (by omega)) (facts_ne (by live_dec))
  have h6 : Seg kernel asms L g 1 236 ((357, ptr 68608) :: factsAt L g 235 d0) 237
      ((358, ptr 84992) :: (357, ptr 68608) :: factsAt L g 235 d0) :=
    seg_one Flow.code_236 rfl (fun t h => exec_add_sharedPtr
      (hL := asms_localRule_none) (k := 84992)
      (holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ hm)) (.inl rfl) (by omega) (by omega))
      (cons_ne (ex := [(357, _)]) (by simp) (by live_dec))
  have h7 : Seg kernel asms L g 1 237 ((358, ptr 84992) :: (357, ptr 68608) ::
      factsAt L g 235 d0) 238
      ((359, ptr 101376) :: (358, ptr 84992) :: (357, ptr 68608) :: factsAt L g 235 d0) :=
    seg_one Flow.code_237 rfl (fun t h => exec_add_sharedPtr
      (hL := asms_localRule_none) (k := 101376)
      (holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) (.inl rfl)
      (by omega) (by omega)) (cons_ne (ex := [(358, _), (357, _)]) (by simp) (by live_dec))
  have h8 : Seg kernel asms L g 1 238 ((359, ptr 101376) :: (358, ptr 84992) ::
      (357, ptr 68608) :: factsAt L g 235 d0) 239
      ((360, ptr 117760) :: (359, ptr 101376) :: (358, ptr 84992) :: (357, ptr 68608) ::
        factsAt L g 235 d0) :=
    seg_one Flow.code_238 rfl (fun t h => exec_add_sharedPtr
      (hL := asms_localRule_none) (k := 117760)
      (holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hm)))) (.inl rfl) (by omega) (by omega))
      (cons_ne (ex := [(359, _), (358, _), (357, _)]) (by simp) (by live_dec))
  have h9 : Seg kernel asms L g 10 239 ((360, ptr 117760) :: (359, ptr 101376) ::
      (358, ptr 84992) :: (357, ptr 68608) :: factsAt L g 235 d0) 249 (facts L g d0) :=
    fun t h => by loader_seg h hpre [ptr, win]
  exact Seg.comp h1 (Seg.comp h2 (Seg.comp h3 (Seg.comp h4 (Seg.comp h5 (Seg.comp h6
    (Seg.comp h7 (Seg.comp h8 h9)))))))

/-- No item: from the branch to the first drain poll. -/
theorem start_d (hpre : Pre P L mem0) :
    Seg kernel asms L g 4 467 (factsAt L g 230 d0) 471
      (facts L g ⟨.drain 0, 0, 0, 0, 1, 1⟩) :=
  fun t h => by loader_seg h hpre

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- `setmaxnreg`, the start, and the item loop's head or the drain. -/
theorem step_start (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .setMaxReg)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
  obtain rfl := fires_next (by exact trivial) hf
  have hv : valueOf L g d0 51 = .pred (decide ¬ 0 < T L g) := by
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]
    rw [start_branch hpre hg]
  obtain ⟨k, hB⟩ := segTo_bra (L := L) (g := g) (pc := 230) (c := decide ¬ 0 < T L g)
    (d1 := ⟨.drain 0, 0, 0, 0, 1, 1⟩) (d2 := d0) Flow.code_230
    (tbl_mem (pc := 230) (by live_dec) hv) (fun _ => ⟨4, start_d hpre⟩)
    (fun _ => ⟨_, start_c hpre hg⟩)
  have hA := Seg.comp (start_a (g := g) hpre ⟨.setMaxReg, i, tt, s, ph, qp⟩) (start_b hpre hg)
  have hm : At (PTX.next t) 195 (factsAt L g 194 ⟨.setMaxReg, i, tt, s, ph, qp⟩) := At.next h
  right
  by_cases hT : 0 < T L g
  · simp only [hT, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hB
    obtain ⟨t', hr, ht'⟩ := Seg.comp hA hB _ hm
    exact ⟨d0, t', by simp [next, hT], run_rtg hr, ht', ⟨by decide, by decide, by decide,
      fun _ => hT, fun h => by simp [Site.inTrip] at h, fun h => by simp [Site.leadOnly] at h,
      fun u j h => by rcases h with h | h <;> cases h⟩⟩
  · simp only [hT, not_false_eq_true, decide_true, ↓reduceIte] at hB
    obtain ⟨t', hr, ht'⟩ := Seg.comp hA hB _ hm
    exact ⟨⟨.drain 0, 0, 0, 0, 1, 1⟩, t', by simp [next, hT], run_rtg hr, ht', ⟨by decide,
      by decide, by decide,
      fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩⟩

/-- The rank broadcast at an item's head: the rows of the CTA's half, then the K0 poll. -/
theorem step_head (hpre : Pre P L mem0) (hs : d.site = .head) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_4)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv with
  | bits w v =>
    by_cases hv : v = BitVec.ofNat 64 (rank L g)
    · subst hv
      have hs6 : s < 6 := hi.s
      have h1 := At.set (r := 740) (v := .bits w (BitVec.ofNat 64 (rank L g))) h
        (facts_ne (by live_dec))
      have hA : Seg kernel asms L g 4 250
          ((740, .bits w (BitVec.ofNat 64 (rank L g))) :: facts L g ⟨.head, i, tt, s, ph, qp⟩)
          254 (factsAt L g 254 ⟨.head, i, tt, s, ph, qp⟩) := fun t h => by loader_seg h hpre
      have hB : Seg kernel asms L g 7 254 (factsAt L g 254 ⟨.head, i, tt, s, ph, qp⟩) 261
          (facts L g ⟨.wait .k0, i, tt, s, ph, qp⟩) := fun t h => by loader_seg h hpre
      exact step_of_seg (d' := ⟨.wait .k0, i, tt, s, ph, qp⟩) (by simp [next])
        (by inv_site hi hi.lead) h1 ⟨_, Seg.comp hA hB⟩
    · exact .inl (by simp [next, hv])
  | _ => exact .inl (by simp [next])

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
