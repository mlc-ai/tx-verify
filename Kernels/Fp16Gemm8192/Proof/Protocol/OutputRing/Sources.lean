-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Safe
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Cover
public import Lemmas.Step.StoreDone
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds
public import Lemmas.TensorStore.TensorStoreCompleteConsistentWriteBytes

@[expose] public section

/-! # The sources of an output tensor store

Every byte a TMA store of a slice reads has a source write visible to the store's read: the staging
store of the thread of the group whose index is the byte's row, in that slice
(`output_sources`). The store leader passed the slice's second output barrier, so every thread of
its group arrived at it (`member_arrival`) after making its sixteen staging stores of the slice
(`ThreadFacts.cons_slice_stores`); those stores happen before the leader's proxy fence
(`store_vis_of_lt`), hence are visible to the store. Every write visible to a read of a staging byte
has a defined byte: an asynchronous write by its effect, a consumer's staging store by its length
(`ThreadFacts.cons_write_len`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A staging store of an earlier output barrier count is visible to a TMA store's read of a byte
it covers. -/
theorem store_vis_of_lt (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {g s pc : Nat} {a : Acc} {bs : List Byte}
    {c : Consumer.D} (hge : X.get (g, s) = some ⟨pc, .wr a bs⟩)
    (hσ : Frame.stateAt (code L) X g s = some (some (.inr (.cons c)))) {l : Loc} (hca : a.Covers l)
    {h i x y kk : Nat} {b : Acc} {wf : Bool} {c' : Consumer.D}
    (hσ' : Frame.stateAt (code L) X h i = some (some (.inr (.cons c'))))
    (hif : X.Intent (.async (h, i) (.read (.store x y kk))) b wf) (hcb : b.Covers l)
    (hsl : l.space = .shared)
    (hlt : Consumer.outBars L g ((X.tr g).take s) < Consumer.outBars L h ((X.tr h).take i)) :
    modelCausality L X l (.thread (g, s)) (.async (h, i) (.read (.store x y kk))) := by
  obtain ⟨k, i0, el, hs, hob, hcta, htid, hlo, hhi⟩ := store_info hX ht hge hσ hca
  obtain ⟨-, eh, ma, sp, st, hgeh, hkh, hsh, hobh, hcom, hcta', htid', hlo', hhi', pcf, hpos,
    hfen⟩ := tma_info hX ht hσ' hif hcb
  obtain ⟨hb1, hb2⟩ := stagingOff_bounds (t := Consumer.tidOf L g) (b := k.val % 2) i0.isLt el.isLt
  obtain ⟨hpar, hgq⟩ := buffer_eq (sb := L.sharedBase) (t := Consumer.tidOf L g)
    (b := k.val % 2) (t' := Consumer.tidOf L h) (b' := st.val % 2) (a := l.addr)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by omega) (by omega) hlo' hhi'
  have hgrp : Consumer.outId L g = Consumer.outId L h := by
    simp only [Consumer.outId]; omega
  have hct : g / L.block = h / L.block := hcta.symm.trans hcta'
  have hht : h < L.threads := Frame.lt_of_get hX hgeh
  have hil : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp hgeh).1
  have hcov : AsyncCovers X (h, i) (.read (.store x y kk)) l := ⟨b, wf, hif, hcb⟩
  refine ⟨hcov, .inl ⟨(h, i - 1), some (.shared .cta), none, ⟨pcf, hfen⟩, hht,
    ⟨hsl, by rw [hcta']⟩, ⟨hht, hht, rfl⟩,
    store_before_fence hpre hX ht hagree hge hσ rfl hgeh hσ' hkh hct hgrp hlt, ?_⟩⟩
  exact .single (.inl (po_of_source_not_access rfl (by omega) hil (by simp [hfen, Event.acc])))

/-- The four events of a prefix: two consecutive events split a longer prefix. -/
theorem take_two {es : List Event} {n : Nat} {e1 e2 : Event} (h1 : es[n]? = some e1)
    (h2 : es[n + 1]? = some e2) : es.take (n + 2) = es.take n ++ [e1, e2] := by
  rw [show n + 2 = (n + 1) + 1 by omega, List.take_add_one, List.take_add_one, h2, h1]
  simp

/-- The specification of a slice's TMA store: the output map's tile from a shared base. -/
def outSpec (b0 : Nat) (cls : TensorDescriptor.AllocationClass) (origin : Fin 2 → Int)
    (cta base : Nat) : TensorStore.Spec :=
  ⟨⟨1, Fp16Gemm8192.mapD b0 cls, origin, ⟨.shared, cta, base⟩, none⟩, none⟩

theorem outSpec_col {b0 cls origin cta base}
    (slot : TensorTransfer.Slot (outSpec b0 cls origin cta base).descriptor) :
    slot.1.val < 32 := by
  simp [outSpec, Fp16Gemm8192.mapD, encodeTiled, TensorTile.count, TensorTile.step]

theorem outSpec_row {b0 cls origin cta base}
    (slot : TensorTransfer.Slot (outSpec b0 cls origin cta base).descriptor) :
    slot.2.1.val < 128 := by
  simp [outSpec, Fp16Gemm8192.mapD, encodeTiled, TensorTile.rows, TensorTile.rowsOf,
    TensorTile.count, TensorTile.step]

theorem outSpec_byte {b0 cls origin cta base}
    (slot : TensorTransfer.Slot (outSpec b0 cls origin cta base).descriptor) :
    slot.2.2.val < 2 := slot.2.2.isLt

/-- A slot's source read of the output map's store is its shared source byte. -/
theorem outSpec_readLoc {b0 cls origin cta base}
    (slot : TensorTransfer.Slot (outSpec b0 cls origin cta base).descriptor) :
    TensorStore.readLoc (outSpec b0 cls origin cta base) slot.1.val slot.2.1.val slot.2.2.val =
      some ((outSpec b0 cls origin cta base).sharedLoc slot) := by
  have hslotAt : TensorTransfer.slotAt (outSpec b0 cls origin cta base).descriptor slot.1.val
      slot.2.1.val slot.2.2.val = some slot := by
    simp only [TensorTransfer.slotAt, dite_eq_left slot.1.isLt, dite_eq_left slot.2.1.isLt,
      dite_eq_left slot.2.2.isLt]
  simp only [TensorStore.readLoc, hslotAt, Option.map_some]

/-- The shared source byte of a slot of the output map's store. -/
theorem outSpec_sharedLoc {b0 cls origin cta base}
    (slot : TensorTransfer.Slot (outSpec b0 cls origin cta base).descriptor) :
    (outSpec b0 cls origin cta base).sharedLoc slot =
      ⟨.shared, cta, base + TensorSwizzle.offset .b64 base
        (64 * slot.2.1.val + 2 * slot.1.val + slot.2.2.val)⟩ :=
  Option.some.inj ((outSpec_readLoc slot).symm.trans
    (output_readLoc (outSpec_col slot) (outSpec_row slot) (outSpec_byte slot)))

/-- A write whose bytes are as many as its footprint defines every byte it covers. -/
theorem wbyte_defined {a : Acc} {bs : List Byte} {loc : Loc} (hlen : bs.length = a.size)
    (hcov : a.Covers loc) : ∃ value, wbyte a bs loc = some value := by
  have hr : loc.addr - a.loc.addr < bs.length := by
    unfold Acc.Covers Loc.InRange at hcov
    omega
  exact ⟨bs[loc.addr - a.loc.addr], List.getElem?_eq_getElem hr⟩

/-- **The sources of an output tensor store.** Every byte a TMA store of a slice reads has a visible
source write, and every visible write of such a byte has a defined byte. -/
theorem output_sources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    (hacc : StagingAccessors L X)
    (hub : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) {i : EvId} {a : Nat}
    {spec : TensorStore.Spec} (hi : X.TensorStoreIssue i a spec) :
    Step.StoreDone.VisibleReadSources L X i spec := by
  obtain ⟨pc, hge⟩ := hi
  obtain ⟨h, ti⟩ := i
  have hht : h < L.threads := Frame.lt_of_get hX hge
  obtain ⟨d, hσd⟩ := Frame.event_state ht.sound hX ht.tracked hge nofun
  obtain ⟨c, st, rfl, hsite, -, b0, cls, origin, hspec⟩ := ht.cons_tma hht hge hσd
  have hspec' : spec = outSpec b0 cls origin (h / L.block)
      (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2)) := hspec
  subst hspec'
  set cta := h / L.block with hcta
  have hk : ti < (X.tr h).length := (List.getElem?_eq_some_iff.mp hge).1
  obtain ⟨h2, ⟨pcb, hbar⟩, ⟨pcf, hfen⟩⟩ := ht.cons_tma_prev hht hk hσd hsite
  have hrw := ht.role_warp hht (idx_le hge) hσd
  simp only [roleWarp] at hrw
  have hblock := hpre.block
  have hal := hpre.sharedAlignment
  set grp := Consumer.tidOf L h / 32 / 4 with hgrpdef
  have hq2 : grp < 2 := by simp only [hgrpdef, Consumer.tidOf]; omega
  have hcg : cta < L.grid := by
    have : h < L.grid * L.block := hht
    rw [hcta, Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  intro slot loc hdest
  have hcol := outSpec_col slot
  have hrow := outSpec_row slot
  have hbyte := outSpec_byte slot
  have hloc := outSpec_sharedLoc slot
  set x := slot.1.val with hxdef
  set y := slot.2.1.val with hydef
  set bb := slot.2.2.val with hbbdef
  have hphase : (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2)) / 128 % 4 =
      0 := by
    simp only [Consumer.stagingBase]; omega
  have hv := source_in_store (sb := L.sharedBase) (T := Consumer.tidOf L h) (par := st.val % 2)
    (t' := 128 * grp + y) (x := x) (y := y) (b := bb) hphase hcol hrow hbyte rfl
  have hb1 := stagingOff_bounds (t := 128 * grp + y) (b := st.val % 2) (i := x / 8)
    (el := x / 2 % 4) (by omega) (by omega)
  -- the byte is staging memory
  have hstaging : IsStaging L ((outSpec b0 cls origin cta
      (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot) := by
    rw [hloc]
    refine ⟨rfl, ?_, ?_⟩ <;>
    · simp only [Consumer.stagingBase, Consumer.stagingOff, Consumer.stage] at hv hb1 ⊢
      omega
  have hex1 : ∃ w a' bs, X.MemWrites w a' bs ∧
      a'.Covers ((outSpec b0 cls origin cta
        (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot) ∧
      ByteCausality L X ((outSpec b0 cls origin cta
        (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot) w
        (storeSlotReadRef (h, ti) slot) := by
    -- the thread of the group whose index is the row
    have hlt384 : 128 * grp + y < L.block := by omega
    set g' := cta * L.block + (128 * grp + y) with hg'
    have hg'cta : g' / L.block = cta := by rw [hg', hblock]; omega
    have hg'mod : g' % L.block = 128 * grp + y := by rw [hg', hblock]; omega
    have hg'lt : g' < L.threads := by
      show g' < L.grid * L.block
      rw [hg', hblock]
      omega
    have hbarB : X.IsBarrier (h, ti - 2) (grp + 10) (some 128) pcb := hbar
    have hpassed : (h, ti - 2).2 + 1 < (X.tr h).length := by simp only; omega
    have hw : (g' % L.block) / 32 ∈ group grp := by
      rw [hg'mod]
      simp only [group, Finset.mem_insert, Finset.mem_singleton]
      omega
    obtain ⟨i', pc', hbar', hcount⟩ := member_arrival hpre hX ht hq2 hbarB hpassed
      (.of_all hagree _) (g := g') hg'cta hg'lt hw
    have hbar'' : X.get (g', i') = some ⟨pc', .bar (grp + 10) (some 128)⟩ := hbar'
    obtain ⟨dm, hσm⟩ := Frame.event_state ht.sound hX ht.tracked hbar'' nofun
    obtain ⟨cm, rfl⟩ := ht.bar_role hg'lt hbar'' hσm rfl
    obtain ⟨hrelm, -, -, -, hbarm, -⟩ := ht.cons_out hg'lt hbar'' hσm
    obtain ⟨hrelh, -, -, -, -, -⟩ := ht.cons_out hht hge hσd
    have e1 : Consumer.outId L g' = grp + 10 := by
      simp only [Consumer.outId, Consumer.tidOf, hg'mod]; omega
    obtain ⟨s', hs'⟩ : ∃ s', cm.site = .barA s' ∨ cm.site = .barB s' := by
      rcases hbarm (grp + 10) (some 128) rfl with ⟨-, hid, -⟩ | ⟨hs, -, -⟩
      · exfalso
        simp only [Consumer.tidOf, hg'mod] at hid
        omega
      · exact hs
    have hO : Consumer.outBars L g' ((X.tr g').take i') =
        Consumer.outBars L h ((X.tr h).take (ti - 2)) := by
      rw [Consumer.outBars_eq, Consumer.outBars_eq, e1]
      exact hcount
    have hT : Consumer.outBars L h ((X.tr h).take ti) =
        Consumer.outBars L h ((X.tr h).take (ti - 2)) + 1 := by
      have hsplit := take_two (es := X.tr h) (n := ti - 2)
        (e1 := ⟨pcb, .bar (Consumer.outId L h) (some 128)⟩)
        (e2 := ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩) hbar
        (by rw [show ti - 2 + 1 = ti - 1 by omega]; exact hfen)
      rw [show ti - 2 + 2 = ti by omega] at hsplit
      rw [Consumer.outBars_eq, Consumer.outBars_eq, hsplit]
      simp [List.countP_append, Execution.isBarId]
    have hOh := hrelh.1
    simp only [Consumer.D.outPhase, hsite] at hOh
    have hOm := hrelm.1
    have hB : cm.site = .barB st := by
      have := s'.isLt
      have := st.isLt
      rcases hs' with hA | hB
      · exfalso
        simp only [Consumer.D.outPhase, hA] at hOm
        omega
      · simp only [Consumer.D.outPhase, hB] at hOm
        have hs'st : s' = st := Fin.ext (by omega)
        rw [← hs'st]
        exact hB
    have hk' : i' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hbar'').1
    obtain ⟨hlen16, hst⟩ := ht.cons_slice_stores hg'lt (hub g') hk' hσm hB
    have hm16 : 4 * (x / 8) + x / 2 % 4 < 16 := by omega
    obtain ⟨pcw, aw, bsw, hwget, hwloc, hwsize, hwlen⟩ := hst _ hm16
    rw [show (4 * (x / 8) + x / 2 % 4) / 4 = x / 8 by omega,
      show (4 * (x / 8) + x / 2 % 4) % 4 = x / 2 % 4 by omega, hg'cta] at hwloc
    have hcovw : aw.Covers ((outSpec b0 cls origin cta
        (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot) :=
          by
      rw [hloc]
      unfold Acc.Covers Loc.InRange
      rw [hwloc, hwsize]
      have htid' : Consumer.tidOf L g' = 128 * grp + y := hg'mod
      simp only [htid']
      refine ⟨?_, ?_, hv.1, hv.2⟩ <;> trivial
    have hint : X.Intent (.thread (g', i' - 16 + (4 * (x / 8) + x / 2 % 4))) aw true :=
      Or.inr (.inl ⟨bsw, ⟨pcw, hwget⟩, rfl⟩)
    rcases hacc _ aw true _ hint hcovw hstaging with
      ⟨e', pc'', bs'', cw, href, hget', hσw⟩ | ⟨i2, x2, y2, k2, c2, href, -⟩
    swap
    · cases href
    cases href
    have hif : X.Intent (.async (h, ti) (.read (.store x y bb)))
        ⟨(outSpec b0 cls origin cta
          (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot,
          1, false, false, .cta, 0, false⟩ false :=
      ⟨rfl, _, a, ⟨pc, hge⟩, outSpec_readLoc slot, rfl⟩
    have hcb : (⟨(outSpec b0 cls origin cta
          (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot,
          1, false, false, .cta, 0, false⟩ : Acc).Covers ((outSpec b0 cls origin cta
          (L.sharedBase +
            Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2))).sharedLoc slot) :=
      ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
    have hmono := countP_take_mono (Execution.isBarId (Consumer.outId L g')) (X.tr g')
      (a := i' - 16 + (4 * (x / 8) + x / 2 % 4)) (b := i') (by omega)
    rw [← Consumer.outBars_eq, ← Consumer.outBars_eq] at hmono
    exact ⟨.thread (g', i' - 16 + (4 * (x / 8) + x / 2 % 4)), aw, bsw, .inl ⟨pcw, hwget⟩, hcovw,
      .direct (store_vis_of_lt hpre hX ht hagree hwget hσw hcovw hσd hif hcb hstaging.1 (by omega))⟩
  refine ⟨hex1, fun w a' bs hw hcov _ => ?_⟩
  cases w with
  | async j p =>
    refine hX.async_write_byte_defined hw (fun s hs => ?_) hcov
    unfold AsyncCopy.issuedBy at hs
    split at hs
    · rename_i pc' s' hj
      obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hj (by simp)
      exact absurd rfl ((ht.ring_event (Frame.lt_of_get hX hj) hj hσ).copy s')
    · cases hs
  | thread e =>
    rcases hacc _ a' true _ hw.intent hcov hstaging with
      ⟨e', pc'', bs'', cw, href, hget', hσw⟩ | ⟨i2, x2, y2, k2, c2, href, -⟩
    swap
    · cases href
    cases href
    obtain ⟨pcw, hgw⟩ | ⟨old, pcw, hgw⟩ := hw
    swap
    · exact (Safety.no_rmw hX ht hgw).elim
    obtain ⟨g1, k1⟩ := e
    exact wbyte_defined (ht.cons_write_len (Frame.lt_of_get hX hgw) hgw hσw) hcov

/-- **The output ring's sources.** -/
theorem outputSources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    (hacc : StagingAccessors L X)
    (hub : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) : OutputSources L X :=
  fun _ _ _ hi => output_sources hpre hX ht hagree hacc hub hi

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
