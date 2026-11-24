-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.LoadShared

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- The packed BF16 source of one scalar element of the vector store. -/
def pStoreSource (k : Fin 4) (sub : Nat) : Nat := 1115 + 3 * (4 * k.val + sub)

/-- Packed word sources of one probability-store vector. -/
def pStoreSrcs (k : Fin 4) : List Opnd :=
  (List.range 4).map fun sub => .reg (pStoreSource k sub)

/-- The decoded direct probability-store vector. -/
def pStoreInstr (k : Fin 4) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 4
    addr := ⟨.reg 474 32, (pTileBase + pChunkStride * k.val : Nat)⟩, srcs := pStoreSrcs k }

/-- The probability store at this chunk uses the corresponding vector. -/
theorem pStore_code (k : Fin 4) :
    kernel.code[(Site.pStore k).pc]? = some ⟨none, .mem (pStoreInstr k)⟩ := by
  fin_cases k <;>
    first | exact Flow.code_704 | exact Flow.code_705 | exact Flow.code_706 | exact Flow.code_707

private theorem pStore_source_value (d : D) (k sub : Fin 4) :
    valueOf P L g d (pStoreSource k sub.val) = pPacked L g d (4 * k.val + sub.val) := by
  fin_cases k <;> fin_cases sub <;> rfl

private theorem pStore_source_live (k sub : Fin 4) :
    pStoreSource k sub.val ∈ (Flow.live (Site.pStore k).pc).filter tracked.contains := by
  fin_cases k <;> fin_cases sub <;> decide +kernel

/-- The computed P word can only emit an aligned shared write. -/
theorem fired_pStore (hpre : Pre P L mem0) {d : D} {k : Fin 4}
    {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .pStore k) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a v stored, t.regs (pStoreSource k d.sub) = some v ∧ storeValue 32 v = .ok stored ∧
      e.kind = .wr a stored.toBytes ∧ siteLoc L g d.site d.block d.sub = some a.loc ∧
      a.size = 4 ∧ o = some (if d.sub + 1 < 4 then {t with sub := d.sub + 1}
        else {t with pc := t.pc + 1, sub := 0}) := by
  rw [hd] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (pStore_code k))
  let base := L.sharedBase + (4096 * half L g + 512 * (warpOf L g % 2) + 16 * laneOf L g)
  let off := pTileBase + pChunkStride * k.val
  let loc : Loc := ⟨.shared, g / L.block, base + off⟩
  have hreg : t.regs 474 = some (b32 base) :=
    reg_value ha (by rw [hd]; fin_cases k <;> decide +kernel)
  have haddr : base + off < 2 ^ 32 := by
    have h0 := sharedBase_lt hpre
    have h1 := halfLt hi.warpLt
    have h2 := hi.laneLt
    have h3 := k.isLt
    dsimp [off, base, pTileBase, pChunkStride]
    omega
  have hloc : effAddr L g t .shared 474 off = .ok loc :=
    effAddr_b32_off hreg haddr
  have hal : loc.addr % 16 = 0 := by
    have hh := hpre.sharedAlignment
    rw [← hpre.sharedBase] at hh
    dsimp [loc, off, base, pTileBase, pChunkStride]
    omega
  have hs := hi.subLt
  rw [hd] at hs
  change d.sub < 4 at hs
  have hts : t.sub = d.sub := ha.2.1
  have hss : (pStoreSrcs k)[t.sub]? = some (.reg (pStoreSource k d.sub)) := by
    rw [hts]
    simp [pStoreSrcs, List.getElem?_range hs]
  have hrule : (pStoreInstr k).rule = some .threadAccess := by fin_cases k <;> rfl
  rw [eventTmpl] at hf
  rw [memTmpl_store (sp := .shared) (base := 474) (w := 32) hrule rfl rfl rfl rfl] at hf
  change Fires (Site.pStore k).pc
    (storeTmpl L g t .shared 32 474 off (pStoreSrcs k)) e o at hf
  let access : Acc := {loc := loc.at (4 * t.sub), size := 4, elem := t.sub}
  have hel : elemAcc loc 4 4 t.sub = .ok access := by
    simp [elemAcc, hal, pure, Except.pure, access]
  have hlen : (pStoreSrcs k).length = 4 := by simp [pStoreSrcs]
  simp only [storeTmpl, hloc, bind, Except.bind, hlen, hel, hss, Nat.reduceDiv] at hf
  let sub : Fin 4 := ⟨d.sub, hs⟩
  let v := pPacked L g d (4 * k.val + d.sub)
  have hr : t.regs (pStoreSource k d.sub) = some v := by
    change t.regs (pStoreSource k sub.val) = some (pPacked L g d (4 * k.val + sub.val))
    rw [← pStore_source_value (P := P) (L := L) (g := g) d k sub]
    exact reg_value ha (by rw [hd]; exact pStore_source_live k sub)
  have hv : storeValue 32 v = .ok v := storeValue_of_bytes (by rfl)
  simp only [readValue, readReg, hr, pure, Except.pure, hv, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  refine ⟨_, v, v, hr, hv, rfl, ?_, rfl, ?_⟩
  · simp [hd, siteLoc, shLoc, ctaOf, access, loc, base, off, hts, Loc.at]
    omega
  · simpa [afterStore, pStoreSrcs, hts] using hu

/-- Each P store emits a scalar four-byte write at its PTX vector element's address. -/
theorem fires_pStore (hpre : Pre P L mem0) {d : D} {k : Fin 4}
    {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .pStore k) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a v stored, t.regs (pStoreSource k d.sub) = some v ∧ storeValue 32 v = .ok stored ∧
      e.kind = .wr a stored.toBytes ∧ siteLoc L g d.site d.block d.sub = some a.loc ∧
      a.size = 4 ∧ u = (if d.sub + 1 < 4 then {t with sub := d.sub + 1}
        else {t with pc := t.pc + 1, sub := 0}) := by
  obtain ⟨a, v, stored, hsrc, hstored, he, hl, hs, hu⟩ := fired_pStore hpre hd ha hi hc hf
  exact ⟨a, v, stored, hsrc, hstored, he, hl, hs, Option.some.inj hu⟩

private def pStoreLive (k : Fin 4) : List Nat :=
  (Flow.live (Site.pStore k).pc).filter tracked.contains

private theorem pStore_next_live {k : Fin 4} (hk : k.val + 1 < 4) :
    pStoreLive ⟨k.val + 1, hk⟩ ⊆ pStoreLive k := by
  change (Flow.live (704 + (k.val + 1))).filter tracked.contains ⊆
    (Flow.live (704 + k.val)).filter tracked.contains
  fin_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exfalso
    exact (show ¬ (3 : Nat) + 1 < 4 by decide) hk

private theorem pStore_acc_nil {d : D} {k : Fin 4} {t : TState}
    (hd : d.site = .pStore k) (ha : (code P L g).AtD d t) : t.acc = [] := by
  rw [ha.2.2.1]
  change siteAcc d = []
  simp [siteAcc, hd]

private theorem step_pStore_beforeLast (hpre : Pre P L mem0)
    (d : D) (k : Fin 4) (hd : d.site = .pStore k) (hk : k.val + 1 < 4) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨a, v, stored, hsrc, hstored, he, hl, hs, hu⟩ := fires_pStore hpre hd ha hi hc hf
    have hac := pStore_acc_nil hd ha
    have hl' : siteLoc L g (.pStore k) d.block d.sub = some a.loc := by simpa [hd] using hl
    have hpc : t.pc = 704 + k.val := by
      rw [show t.pc = d.site.pc from ha.1, hd]
      rfl
    by_cases hmore : d.sub + 1 < 4
    · let d' : D := {d with sub := d.sub + 1}
      have hn : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, writeStep, he, hl', hs, Site.elemBytes, Site.elems, hmore, hk, d']
      rw [ite_eq_left hmore] at hu
      subst u
      have hsub' : d'.sub < d'.site.elems := by
        change d.sub + 1 < d.site.elems
        simpa [hd, Site.elems] using hmore
      have hi' : Inv P L g d' := {hi with subLt := hsub'}
      refine Or.inl (Or.inr ⟨d', _, hn, .refl, ⟨?_, rfl, ?_, ha.2.2.2.1, ?_⟩, hi'⟩)
      · exact ha.1
      · rw [hac]
        change [] = siteAcc d'
        simp [siteAcc, d', hd]
      · exact ha.2.2.2.2
    · let j : Fin 4 := ⟨k.val + 1, hk⟩
      let d' : D := {d with site := .pStore j, sub := 0}
      have hn : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, writeStep, he, hl', hs, Site.elemBytes, Site.elems, hmore,
          hk, d', j]
      rw [ite_eq_right hmore] at hu
      subst u
      have hkeep := pStore_next_live hk
      have hbase : Holds t.regs (factsFrom (pStoreLive k) (valueOf P L g d)) := by
        simpa only [code, facts, hd, pStoreLive] using ha.2.2.2.2
      have hi' := inv_setSite hi (.pStore j) (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
        (by rintro ⟨a, b, h⟩; cases h) (by simp) (by simp)
      refine Or.inl (Or.inr ⟨d', _, hn, .refl,
        ⟨?_, rfl, hac, ha.2.2.2.1, holds_factsFrom_mono hbase hkeep⟩, hi'⟩)
      change t.pc + 1 = 704 + (k.val + 1)
      omega

/-- The scalar P store writes the packed values for the two sparse slots the lane computed. -/
theorem fires_pStore_packed (hpre : Pre P L mem0) {d : D} {k : Fin 4}
    {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .pStore k) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .wr a (pPacked L g d (4 * k.val + d.sub)).toBytes ∧
      siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = 4 := by
  obtain ⟨a, v, stored, hsrc, hstored, he, hl, hs, _⟩ := fires_pStore hpre hd ha hi hc hf
  have hsub : d.sub < 4 := by simpa [hd, Site.elems] using hi.subLt
  let sub : Fin 4 := ⟨d.sub, hsub⟩
  have hr : t.regs (pStoreSource k sub.val) = some (pPacked L g d (4 * k.val + sub.val)) := by
    rw [← pStore_source_value (P := P) (L := L) (g := g) d k sub]
    exact reg_value ha (by rw [hd]; exact pStore_source_live k sub)
  have hre : v = pPacked L g d (4 * k.val + d.sub) := Option.some.inj (hsrc.symm.trans hr)
  rw [hre, storeValue_of_bytes (show (pPacked L g d (4 * k.val + d.sub)).bytes = 32 / 8 from rfl)]
    at hstored
  rw [← Except.ok.inj hstored] at he
  exact ⟨a, he, hl, hs⟩

private theorem run_pStore_first_test (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (hblock : d.block < blocksOf P L g) {t : TState}
    (ha : At t 708 (factsFrom (pStoreLive 3) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 709
      ((111, .pred (decide (d.block = 0))) :: factsFrom (pStoreLive 3) (valueOf P L g d)) := by
  have hlim := (blocksOf_word_bounds hpre hb).2
  simp only [pStoreLive] at ha ⊢
  seg_fp ha using norm_signed []

private theorem pStore_branch_bool (d : D) :
    (decide (d.block = 0) || !d.voteTaken) = !wantsRescale d := by
  by_cases hz : d.block = 0 <;> cases ht : d.voteTaken <;> simp [wantsRescale, hz, ht]

private theorem run_pStore_skip_test (d : D) {t : TState}
    (ha : At t 709 ((111, .pred (decide (d.block = 0))) ::
      factsFrom (pStoreLive 3) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 710
      ((112, .pred (!wantsRescale d)) :: factsFrom (pStoreLive 3) (valueOf P L g d)) := by
  simp only [pStoreLive] at ha ⊢
  seg_fp ha using exact congrArg Value.pred (pStore_branch_bool d)

private def afterPStore (d : D) : Site := if wantsRescale d then .rescaleFence else .soFence

private theorem pStore_end_live (d : D) :
    (Flow.live (afterPStore d).pc).filter tracked.contains ⊆ pStoreLive 3 := by
  cases hz : wantsRescale d <;> simp only [afterPStore, hz, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

private theorem run_pStore_out (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (hblock : d.block < blocksOf P L g) {t : TState}
    (ha : At t 708 (factsFrom (pStoreLive 3) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u (afterPStore d).pc
      (facts P L g {d with site := afterPStore d, sub := 0, rescale := wantsRescale d}) := by
  obtain ⟨t₁, hr₁, ha₁⟩ := run_pStore_first_test hpre hb d hblock ha
  obtain ⟨t₂, hr₂, ha₂⟩ := run_pStore_skip_test d ha₁
  obtain ⟨t₃, hr₃, ha₃⟩ := run_bra Flow.code_710 (!wantsRescale d) ha₂ ha₂.2.2.2.2.1
    (Thread.asms_localRule_bra (by rw [ha₂.1]; decide) (by rw [ha₂.1]; decide))
  have hp : (if !wantsRescale d then 1120 else 711) = (afterPStore d).pc := by
    cases hz : wantsRescale d <;> simp [afterPStore, hz, Site.pc]
  rw [hp] at ha₃
  refine ⟨t₃, run_comp (run_comp hr₁ hr₂) hr₃, ha₃.mono ?_⟩
  change Holds t₃.regs
    (factsFrom ((Flow.live (afterPStore d).pc).filter tracked.contains) (valueOf P L g d))
  exact holds_factsFrom_mono ha₃.2.2.2.2.2 (pStore_end_live d)

private theorem afterPStore_inv {d : D} (hi : Inv P L g d) (hd : d.site = .pStore 3) :
    Inv P L g {d with site := afterPStore d, sub := 0, rescale := wantsRescale d} := by
  let row := {d with rescale := wantsRescale d}
  have hRescale : row.site.inRescale = true → row.rescale = true := by
    change d.site.inRescale = true → _
    simp [hd, Site.inRescale]
  have hi' : Inv P L g row := {hi with rescaleArm := hRescale}
  refine inv_setSite hi' (afterPStore d) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    cases hz : wantsRescale d <;>
      simp [afterPStore, hz, row, Site.inEpilogue, Site.inRescale, Site.needsRowTotal,
        Site.needsExchangeReady]

/-- After four elements the next P vector starts, or the last vector selects the two fence arms. -/
theorem step_pStore (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (d : D) (k : Fin 4) (hd : d.site = .pStore k) : (code P L g).StepAt d := by
  by_cases hk : k.val + 1 < 4
  · exact step_pStore_beforeLast hpre d k hd hk
  have hlast : k = 3 := Fin.ext (by have h := k.isLt; omega)
  subst k
  apply stepAt_of P L g d
  intro t e u ins ha hi hc hf
  obtain ⟨a, _, _, _, _, he, hl, hs, hu⟩ := fires_pStore hpre hd ha hi hc hf
  have hl' : siteLoc L g (.pStore 3) d.block d.sub = some a.loc := by simpa [hd] using hl
  have hac := pStore_acc_nil hd ha
  have hs0 : d.site.inRescale = false := by rw [hd]; rfl
  by_cases hmore : d.sub + 1 < 4
  · let d' : D := {d with sub := d.sub + 1, rescale := wantsRescale d}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, writeStep, he, hl', hs, Site.elemBytes, Site.elems, hmore, d']
    rw [ite_eq_left hmore] at hu
    subst u
    have hsub' : d'.sub < d'.site.elems := by
      change d.sub + 1 < d.site.elems
      simpa [hd, Site.elems] using hmore
    have ha' : d'.site.inRescale = true → d'.rescale = true := by
      intro hx
      change d.site.inRescale = true at hx
      simp [hs0] at hx
    have hi' : Inv P L g d' := {hi with subLt := hsub', rescaleArm := ha'}
    refine Or.inl (Or.inr ⟨d', _, hn, .refl, ⟨ha.1, rfl, ?_, ha.2.2.2.1, ?_⟩, hi'⟩)
    · rw [hac]
      change [] = siteAcc d'
      simp [siteAcc, d', hd]
    · exact ha.2.2.2.2
  · rw [ite_eq_right hmore] at hu
    subst u
    let d' : D := {d with site := afterPStore d, sub := 0, rescale := wantsRescale d}
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, writeStep, he, hl', hs, Site.elemBytes, Site.elems, hmore,
        d', afterPStore]
    have ht : At {t with pc := t.pc + 1, sub := 0} 708
        (factsFrom (pStoreLive 3) (valueOf P L g d)) := by
      refine ⟨?_, rfl, hac, ha.2.2.2.1, ?_⟩
      · change t.pc + 1 = 708
        rw [show t.pc = d.site.pc from ha.1, hd]
        rfl
      · simpa only [code, facts, hd, pStoreLive] using ha.2.2.2.2
    obtain ⟨v, hr, hv⟩ := run_pStore_out hpre hb d hi.blockLt ht
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr,
      ⟨hv.1, hv.2.1, hv.2.2.1.trans (siteAcc_nil d' rfl).symm, hv.2.2.2.1, hv.2.2.2.2⟩,
      afterPStore_inv hi hd⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
