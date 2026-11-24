-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Layout

@[expose] public section

/-! # The output ring orders its staging bytes

Two conflicting accesses of a staging byte are staging stores or TMA store reads of the warp
group and slice parity owning the byte (`StagingAccessors`). Stores of
different slices are ordered by the output barrier (`store_before_store`), stores of one slice
write distinct bytes per thread (`stagingOff_inj`); a store and a TMA store of a later or the
same slice are ordered through the proxy fence (`store_before_fence`), of an earlier slice
through the drain wait (`tma_before_store`); TMA store reads do not conflict
(`stagingOrdered`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A staging store covering a byte: its slice, element and the byte's place. -/
theorem store_info (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g s pc : Nat}
    {a : Acc} {bs : List Byte} {c : Consumer.D} (hge : X.get (g, s) = some ⟨pc, .wr a bs⟩)
    (hσ : Frame.stateAt (code L) X g s = some (some (.inr (.cons c)))) {l : Loc} (hl : a.Covers l) :
    ∃ (k : Fin 8) (i el : Fin 4), c.site = .store k i el ∧
      Consumer.outBars L g ((X.tr g).take s) % 16 = 2 * k.val + 1 ∧
      l.cta = g / L.block ∧ Consumer.tidOf L g < 256 ∧
      L.sharedBase + Consumer.stagingOff (Consumer.tidOf L g) (k.val % 2) i el ≤ l.addr ∧
      l.addr < L.sharedBase + Consumer.stagingOff (Consumer.tidOf L g) (k.val % 2) i el + 4 := by
  have hgt : g < L.threads := Frame.lt_of_get hX hge
  obtain ⟨hrel, hst, -, -, -, -⟩ := ht.cons_out hgt hge hσ
  obtain ⟨k, i, el, hs, hloc, hsize⟩ := hst a bs rfl
  have hrw := ht.role_warp hgt (idx_le hge) hσ
  simp only [roleWarp] at hrw
  obtain ⟨-, hlc, hlo, hhi⟩ := hl
  rw [hloc] at hlc hlo hhi
  rw [hsize] at hhi
  have h1 := hrel.1
  simp only [Consumer.D.outPhase, hs] at h1
  have hk := k.isLt
  exact ⟨k, i, el, hs, by omega, hlc, by simp only [Consumer.tidOf] at hrw ⊢; omega, hlo, hhi⟩

/-- A TMA store read covering a byte: its slice, and the byte's place in its staging buffer. -/
theorem tma_info (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {h i : Nat}
    {x y kk : Nat} {b : Acc} {wf : Bool} {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X h i = some (some (.inr (.cons c))))
    (hif : X.Intent (.async (h, i) (.read (.store x y kk))) b wf) {l : Loc} (hl : b.Covers l) :
    wf = false ∧ ∃ eh ma sp, ∃ st : Fin 8, X.get (h, i) = some eh ∧ eh.kind = .tensorStore ma sp ∧
      c.site = .tma st ∧
      Consumer.outBars L h ((X.tr h).take i) % 16 = (2 * st.val + 2) % 16 ∧
      2 * commits ((X.tr h).take i) + 2 = Consumer.outBars L h ((X.tr h).take i) ∧
      l.cta = h / L.block ∧ Consumer.tidOf L h < 256 ∧
      L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2) ≤ l.addr ∧
      l.addr < L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2) + 8192 ∧
      ∃ pcf, 0 < i ∧
        X.get (h, i - 1) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨hwf, sp, ma, ⟨pci, hge⟩, hrl, hsz⟩ := hif
  refine ⟨hwf, ⟨pci, .tensorStore ma sp⟩, ma, sp, ?_⟩
  have hht : h < L.threads := Frame.lt_of_get hX hge
  obtain ⟨hrel, -, htma, -, -, -⟩ := ht.cons_out hht hge hσ
  obtain ⟨st, hs, hfp, pcf, hpos, hfen⟩ := htma ma sp rfl
  have hrw := ht.role_warp hht (idx_le hge) hσ
  simp only [roleWarp] at hrw
  obtain ⟨hsp, hct, hlo, hhi⟩ := hfp x y kk b.loc hrl
  obtain ⟨-, hlc, hl1, hl2⟩ := hl
  rw [hsz] at hl2
  have h1 := hrel.1
  have h2 := hrel.2
  simp only [Consumer.D.outPhase, Consumer.D.outLag, hs] at h1 h2
  refine ⟨st, hge, rfl, hs, h1, h2, by rw [hlc, hct], by simp only [Consumer.tidOf] at hrw ⊢; omega,
    by omega, by omega, pcf, hpos, hfen⟩

/-- A byte in two staging buffers is in one: same group, same slice parity. -/
theorem buffer_eq {sb t t' b b' a : Nat} (hb : b < 2) (hb' : b' < 2)
    (h1 : sb + Consumer.stagingBase t b ≤ a) (h2 : a < sb + Consumer.stagingBase t b + 8192)
    (h3 : sb + Consumer.stagingBase t' b' ≤ a) (h4 : a < sb + Consumer.stagingBase t' b' + 8192) :
    b = b' ∧ t / 32 / 4 = t' / 32 / 4 := by
  simp only [Consumer.stagingBase] at h1 h2 h3 h4
  omega

/-- A staging store and a TMA store read of the same byte are ordered. -/
theorem store_tma_vis (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    {g s pc : Nat} {a : Acc} {bs : List Byte}
    {c : Consumer.D} (hge : X.get (g, s) = some ⟨pc, .wr a bs⟩)
    (hσ : Frame.stateAt (code L) X g s = some (some (.inr (.cons c)))) {l : Loc} (hca : a.Covers l)
    {h i x y kk : Nat} {b : Acc} {wf : Bool} {c' : Consumer.D}
    (hσ' : Frame.stateAt (code L) X h i = some (some (.inr (.cons c'))))
    (hif : X.Intent (.async (h, i) (.read (.store x y kk))) b wf) (hcb : b.Covers l)
    (hsl : l.space = .shared) :
    modelCausality L X l (.thread (g, s)) (.async (h, i) (.read (.store x y kk))) ∨
      modelCausality L X l (.async (h, i) (.read (.store x y kk))) (.thread (g, s)) := by
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
  have hk := k.isLt
  have hst := st.isLt
  have hcov : AsyncCovers X (h, i) (.read (.store x y kk)) l := ⟨b, wf, hif, hcb⟩
  rcases Nat.lt_or_ge (Consumer.outBars L g ((X.tr g).take s))
      (Consumer.outBars L h ((X.tr h).take i)) with hlt | hge'
  · left
    refine ⟨hcov, .inl ⟨(h, i - 1), some (.shared .cta), none, ⟨pcf, hfen⟩, hht,
      ⟨hsl, by rw [hcta']⟩, ⟨hht, hht, rfl⟩,
      store_before_fence hpre hX ht hagree hge hσ rfl hgeh hσ' hkh hct hgrp hlt, ?_⟩⟩
    exact .single (.inl (po_of_source_not_access rfl (by omega) hil (by simp [hfen, Event.acc])))
  · right
    have h3 : Consumer.outBars L h ((X.tr h).take i) + 3 ≤
        Consumer.outBars L g ((X.tr g).take s) := by omega
    obtain ⟨w, hpres, hbw, hhb⟩ := tma_before_store hpre hX ht hagree hge hσ rfl hgeh hσ' hkh hct
      hgrp h3
    refine ⟨hcov, w, .inl ⟨.bulk .read, rfl, hbw, fun q hq => ?_⟩, .inl hhb⟩
    simp only [GroupWaitStages, hgeh, Option.map_some, hkh, List.mem_singleton] at hq
    subst hq
    exact hpres

/-- **The output ring.** Two conflicting accesses of a staging byte are ordered at it. -/
theorem stagingOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    (hacc : StagingAccessors L X) :
    StagingOrdered L X := by
  intro e f a b l hcon hca hcb hst
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := hcon
  rcases hacc e a we l hie hca hst with
    ⟨⟨g, s⟩, pc, bs, c, rfl, hge, hσ⟩ | ⟨⟨h, i⟩, x, y, kk, c, rfl, hσ⟩ <;>
  rcases hacc f b wf l hif hcb hst with
    ⟨⟨g', s'⟩, pc', bs', c', rfl, hge', hσ'⟩ | ⟨⟨h', i'⟩, x', y', kk', c', rfl, hσ'⟩
  · -- two staging stores
    obtain ⟨k, i0, el, hs, hob, hcta, htid, hlo, hhi⟩ := store_info hX ht hge hσ hca
    obtain ⟨k', i0', el', hs', hob', hcta', htid', hlo', hhi'⟩ := store_info hX ht hge' hσ' hcb
    obtain ⟨hb1, hb2⟩ := stagingOff_bounds (t := Consumer.tidOf L g) (b := k.val % 2)
      i0.isLt el.isLt
    obtain ⟨hb1', hb2'⟩ := stagingOff_bounds (t := Consumer.tidOf L g') (b := k'.val % 2)
      i0'.isLt el'.isLt
    obtain ⟨hpar, hgq⟩ := buffer_eq (sb := L.sharedBase) (t := Consumer.tidOf L g)
      (b := k.val % 2) (t' := Consumer.tidOf L g') (b' := k'.val % 2) (a := l.addr)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by omega) (by omega) (by omega)
      (by omega)
    have hgrp : Consumer.outId L g = Consumer.outId L g' := by
      simp only [Consumer.outId]; omega
    have hct : g / L.block = g' / L.block := hcta.symm.trans hcta'
    rcases Nat.lt_trichotomy (Consumer.outBars L g ((X.tr g).take s))
        (Consumer.outBars L g' ((X.tr g').take s')) with hlt | heq | hgt
    · exact .inl (.inl (store_before_store hpre hX ht hagree hge hσ rfl hge' hct hgrp hlt))
    · -- the same slice: the same element, so the same thread
      have hkk : k = k' := by
        have := k.isLt
        have := k'.isLt
        apply Fin.ext
        omega
      subst hkk
      have hal := hpre.sharedAlignment
      have hs8 : Consumer.stage (Consumer.tidOf L g) i0 % 8 = 0 := by
        simp only [Consumer.stage]; omega
      have hs8' : Consumer.stage (Consumer.tidOf L g') i0' % 8 = 0 := by
        simp only [Consumer.stage]; omega
      have hoff : Consumer.stagingOff (Consumer.tidOf L g) (k.val % 2) i0 el =
          Consumer.stagingOff (Consumer.tidOf L g') (k.val % 2) i0' el' := by
        simp only [Consumer.stagingOff] at hlo hhi hlo' hhi' ⊢
        omega
      obtain ⟨htt, -, -, -⟩ := stagingOff_inj hgq i0.isLt i0'.isLt el.isLt el'.isLt hoff
      have hgg : g = g' := by
        simp only [Consumer.tidOf] at htt
        have := Nat.div_add_mod g L.block
        have := Nat.div_add_mod g' L.block
        rw [hct] at *
        omega
      subst hgg
      have hss : s ≠ s' := fun h => hne (by rw [h])
      have hl1 : s < (X.tr g).length := (List.getElem?_eq_some_iff.mp hge).1
      have hl2 : s' < (X.tr g).length := (List.getElem?_eq_some_iff.mp hge').1
      rcases Nat.lt_or_gt_of_ne hss with h1 | h1
      · exact .inl (.inl (.single (.inl (po_of_overlap (Or.inr (.inl ⟨_, ⟨_, hge⟩, rfl⟩))
          (Or.inr (.inl ⟨_, ⟨_, hge'⟩, rfl⟩)) rfl h1 ⟨l, hca, hcb⟩))))
      · exact .inr (.inl (.single (.inl (po_of_overlap (Or.inr (.inl ⟨_, ⟨_, hge'⟩, rfl⟩))
          (Or.inr (.inl ⟨_, ⟨_, hge⟩, rfl⟩)) rfl h1 ⟨l, hcb, hca⟩))))
    · exact .inr (.inl
        (store_before_store hpre hX ht hagree hge' hσ' rfl hge hct.symm hgrp.symm hgt))
  · exact store_tma_vis hpre hX ht hagree hge hσ hca hσ' hif hcb hst.1
  · exact (store_tma_vis hpre hX ht hagree hge' hσ' hcb hσ hie hca hst.1).symm
  · -- two TMA store reads do not conflict
    exfalso
    obtain ⟨h1, -⟩ := hie
    obtain ⟨h2, -⟩ := hif
    subst h1 h2
    rcases hw with h | h <;> cases h

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
