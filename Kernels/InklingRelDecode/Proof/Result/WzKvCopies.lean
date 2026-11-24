-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.WzOperand

@[expose] public section

/-!
# The K/V copies of a block an issued MMA reads, on every consistent execution

`Lp.kvCopies_of` proves `Result.Mma.KvCopies` from `Complete L X`: the loader and the prologue
reach their copy sites. Here the copies come from the MMA warp's poll of the slot's `kv_ready`
barrier instead. An MMA of block `i` is issued by the committing lane after more successful polls
of `kv_ready (i % 3)` than `i / 3` (`Ring.Cover.lane_counts`), so the lane's poll for use
`i / 3` observed every item of that use (`Ring.Kv.consumer_observes`): eight tensor copies with
completion records, which are observed copies (`tensorNotify_facts`) of use `i / 3`
(`item_copy`) and pairwise distinct (`item_inj`).

Every copy of the slot writes one box of the slot and is of a block (`copy_dst`), which is `i`
since the use and the slot determine it (`Sx.copy_use_block`). Two distinct copies of one use do
not write one byte (`Sx.copy_same_use`), so the eight copies write eight distinct boxes of the
eight, and every box is written by one of them (`kvCopiesF_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wz
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A tensor copy's slot, box and block**: it completes on `kv_ready t` of its CTA, its spec is
`kvCopySpec` with the destination of box `(isV, slab, hh)` of slot `t`, and it is a copy of a
block `ib` with `ib % 3 = t` (the prologue's copy site `i`, block `i / 4`, or the loader's state
of iteration `ib`). -/
theorem copy_dst (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ t < 3, ∃ isV slab hh, isV ≤ 1 ∧ slab ≤ 1 ∧ hh ≤ 1 ∧
      sp.mbar = kvReady L (g / L.block) t ∧
      (∃ col row bar, sp = kvCopySpec Q (g / L.block) col row
        (L.sharedBase + 32768 * t + 98304 * isV + 8192 * slab + 16384 * hh) bar) ∧
      ∃ ib, CopyBlock Q L X (g, k) ib ∧ ib % 3 = t := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
  obtain ⟨col, row, dst, bar, hk, -, -, -⟩ :=
    Interface.copy_spec_at hpre hX hf.sound hf.ldRng hg he ⟨a, sp, rfl⟩ hTT
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, hspec⟩ := hk
  have hsb : ProA.SbRoom L := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    unfold ProA.SbRoom
    omega
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, i, hi, hs', a', s', hev, -, -, h3, hsb', -⟩ | ⟨d, P, hσ, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    have hdst : dst = ProA.copyDst L g d.dt i := by
      have := hsb'
      rw [hspec] at this
      simp only [EvW.kvCopySpec, Loc.mk.injEq] at this
      exact this.2.2
    rw [ProA.copyDst_form L g d.dt hsb hi] at hdst
    have := ProA.half_lt d.dt (i / 4)
    refine ⟨i / 4, by omega, i % 2, i % 4 / 2, ProA.half d.dt (i / 4), by omega, by omega,
      by omega, ?_, ⟨col, row, bar, ?_⟩, i / 4, Or.inr ⟨d, i, hσ, hi, hs', rfl⟩, by omega⟩
    · rw [h3]
      simp only [EvD.kvReadyOf, EvD.Bar.loc, EvD.Bar.off, kvReady, EvW.barLoc, EvW.kvReadyOff]
      congr 1
      omega
    · rw [hspec, hdst]
      congr 1
      omega
  · have hcp : Ring.Ld.isCp d.site = true := by
      unfold EvW.LdShape at hsh
      cases hst : d.site <;> rw [hst] at hsh <;> simp at hsh <;> rfl
    obtain ⟨b, hb, hev⟩ := Ring.ldShape_cp hsh hcp
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    have hb' : (b.2.1 = 0 ∨ b.2.1 = 1) ∧ (b.2.2 = 0 ∨ b.2.2 = 1) := by
      revert hb
      cases hs : d.site <;> simp [EvW.ldBox] <;> intro h <;> subst h <;> simp
    refine ⟨d.i % 3, Nat.mod_lt _ (by omega), if b.1 then 1 else 0, b.2.1, b.2.2,
      by split <;> omega, by omega, by omega, rfl, ⟨EvW.ldCol L g d b.1 b.2.2,
      EvW.ldRow L g d b.2.1, kvReady L (g / L.block) (d.i % 3), ?_⟩, d.i,
      Or.inl ⟨d, P, hσ, rfl⟩, rfl⟩
    unfold EvW.ldCopy EvW.ldDst
    obtain ⟨v, sl, hh⟩ := b
    cases v <;> simp

/-! ### The items of a use -/

section items
open Ring.Kv
open PTX.MBarrier hiding okPolls

variable {S : Ring.Kv.Slot}

/-- **A copy item of a use is an observed copy of that use.** -/
theorem item_copy (hX : Consistent L kernel asms mem0 X) (H : Hyp L kernel asms X S)
    {k : Ring.Kv.Kind} {u : Nat} (hx : (k, u) ∈ SF X S) (hk : k.val ≠ 0) :
    ∃ pc al sp, X.get (opF X S k u) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      copyUse X S (opF X S k u) = u ∧
      ∃ o, X.tensor (opF X S k u) = some o ∧ o.spec = sp := by
  obtain ⟨-, r, hr, hid, -, -, h1⟩ := Finset.mem_filter.mp hx
  have ha := h1 hk
  have hδ := H.δ_le
  have hit : itF X S k u = .async (opF X S k u) (.notify .load) := by simp [itF, hk]
  have hobj : objectAction X X.async S.full (.async (opF X S k u) (.notify .load)) =
      some (.completeTx copyBytes) := by
    have h := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid, hit, ha] at h
    exact h
  obtain ⟨pc', a', s', o, hget', hobs, -, -, -⟩ := PairTmaRing.tensorNotify_facts hobj
  have hspec : o.spec = s' := by
    obtain ⟨mA, pc'', hget''⟩ := (hX.tensor _ o hobs).1
    have h := Option.some.inj (hget'.symm.trans hget'')
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
    exact h.2.2.symm
  rcases item_completion H (x := (k, u)) hk hr hid ha with
    ⟨hδ1, hu, pc, al, sp, he, hm⟩ | ⟨hpz, j, pc, al, sp, hop, he, hm, hcnt, -⟩
  · have hop : opF X S k u = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      simp only at hu
      simp [opF, hδ1, hu, hk]
    refine ⟨pc, al, sp, he, hm, ?_, o, hobs, ?_⟩
    · simp only at hu
      rw [hop, hu]
      simp [copyUse, hδ1]
    · rw [hspec]
      have h := Option.some.inj (hget'.symm.trans he)
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
      exact h.2.2
  · simp only at hpz hcnt
    refine ⟨pc, al, sp, by rw [hop]; exact he, hm, ?_, o, hobs, ?_⟩
    · have hnp : ¬ (S.δ = 1 ∧ ∃ i : Fin 8, (S.cp, j) = S.pCp i) := by
        rintro ⟨hδ1, i, hi⟩
        exact (H.pre_ne hδ1).2 i (congrArg Prod.fst hi).symm
      rw [hop]
      simp only [copyUse, hnp, ↓reduceIte, hcnt]
      have := k.isLt
      omega
    · rw [hspec]
      have h := Option.some.inj (hget'.symm.trans (by rw [hop]; exact he))
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
      exact h.2.2

/-- **The copy items of one use are distinct events.** -/
theorem item_inj (H : Hyp L kernel asms X S) {k k' : Ring.Kv.Kind} {u : Nat} (hx : (k, u) ∈ SF X S)
    (hx' : (k', u) ∈ SF X S) (hk : k.val ≠ 0) (hk' : k'.val ≠ 0)
    (heq : opF X S k u = opF X S k' u) : k = k' := by
  obtain ⟨-, r, hr, hid, -, -, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, r', hr', hid', -, -, h1'⟩ := Finset.mem_filter.mp hx'
  have := k.isLt
  have := k'.isLt
  rcases item_completion H (x := (k, u)) hk hr hid (h1 hk) with
    ⟨hδ1, hu, -⟩ | ⟨hpz, j, pc, al, sp, hop, he, -, hcnt, -⟩
  · simp only at hu
    have e1 : opF X S k u = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      simp [opF, hδ1, hu, hk]
    have e2 : opF X S k' u = S.pCp ⟨k'.val - 1, by have := k'.isLt; omega⟩ := by
      simp [opF, hδ1, hu, hk']
    rw [e1, e2] at heq
    have h := H.pre_inj hδ1 heq
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · rcases item_completion H (x := (k', u)) hk' hr' hid' (h1' hk') with
      ⟨hδ1, hu, -⟩ | ⟨-, j', pc', al', sp', hop', he', -, hcnt', -⟩
    · exact absurd ⟨hδ1, hu⟩ hpz
    · simp only at hcnt hcnt' hop hop'
      rw [hop, hop'] at heq
      simp only [Prod.mk.injEq, true_and] at heq
      subst heq
      exact Fin.ext (by omega)

end items

/-! ### The copies of a block -/

/-- The first byte of box `(isV, slab, hh)` of slot `s` is the copy's write at `(0, 0, 0)`. -/
theorem box_loc {sb s isV slab hh cta col row : Nat} {bar : Loc} (hsb : sb % 128 = 0)
    (hS : slab ≤ 1) (hH : hh ≤ 1) :
    TensorCopy.writeLoc (kvCopySpec Q cta col row
        (sb + 32768 * s + 98304 * isV + 8192 * slab + 16384 * hh) bar) 0 0 0 =
      some ⟨.shared, cta, kvAddr sb s isV (64 * slab) (64 * hh) 0⟩ := by
  have h := copy_loc_kv Q sb s isV cta col row bar (n := 64 * slab) (d := 64 * hh) (z := 0) hsb
    (by omega) (by omega) (by omega)
  rw [show 64 * slab / 64 = slab by omega, show 64 * hh / 64 = hh by omega,
    show 64 * hh % 64 = 0 by omega, show 64 * slab % 64 = 0 by omega] at h
  exact h

/-- **`KvCopiesF` on every consistent execution.** -/
theorem kvCopiesF_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (G : Sr.SrPkg L kernel asms mem0 X) : KvCopiesF Q L X := by
  refine ⟨fun {m dm i} isV slab hh hm hmi hAt hblk hV hS hH => ?_⟩
  obtain ⟨gm, km⟩ := m
  obtain ⟨d0, sp0, acc0, mask0, pcm, hem⟩ := hmi
  obtain ⟨P, hσ⟩ := hAt
  have hm' : gm < L.threads := hm
  have hk : km < (X.tr gm).length := len_of_get hem
  have hc : gm / L.block < L.grid := ProA.grid_lt hm'
  have hs3 : i % 3 < 3 := Nat.mod_lt _ (by omega)
  have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
  obtain ⟨pArr, pCp, hP⟩ := Lp.preRing_of hpre hX hf (gm / L.block) hc (i % 3) hs3
  have H := Lp.slot_hyp hpre hX hf hR hp G hc hs3 hP
  have hcm : gm = G.cm (gm / L.block) :=
    (G.lane _ hc).mma_thread (x := (gm, km)) ⟨_, _, _, _, pcm, hem⟩ rfl
  have hpc := Ring.Cover.lane_polls hpre hX hf hR hk hσ hs3
  obtain ⟨t0, ins0, o0, -, hinv0, -, -⟩ := Frame.fired_site hf.sound hX hem hσ
  have hI : Mma.Inv dm := hinv0.2.1
  have hu1 : i / 3 + 1 ≤ okPolls (kvReady L (gm / L.block) (i % 3)) ((X.tr gm).take km) := by
    rw [hpc]
    unfold Ring.below
    rcases hblk with ⟨j, hs, hi⟩ | ⟨j, hs, hi⟩
    · simp only [Ring.Mm.polled, hs]
      omega
    · have := hI.pv (by simp [Mma.PvSite, hs])
      simp only [Ring.Mm.polled, hs]
      omega
  have hpol : i / 3 < okPolls (Lp.slotOf Q L X (gm / L.block) (i % 3) (G.cm (gm / L.block))
      pArr pCp).full (X.tr (Lp.slotOf Q L X (gm / L.block) (i % 3) (G.cm (gm / L.block))
      pArr pCp).cm) := by
    have hle : okPolls (kvReady L (gm / L.block) (i % 3)) ((X.tr gm).take km) ≤
        okPolls (kvReady L (gm / L.block) (i % 3)) (X.tr gm) := by
      unfold okPolls
      exact (List.take_sublist _ _).countP_le
    show i / 3 < okPolls (kvReady L (gm / L.block) (i % 3)) (X.tr (G.cm (gm / L.block)))
    rw [← hcm]
    omega
  have hx : ∀ j : Fin 8, ((⟨j.val + 1, by omega⟩ : Ring.Kv.Kind), i / 3) ∈ Ring.Kv.SF X
      (Lp.slotOf Q L X (gm / L.block) (i % 3) (G.cm (gm / L.block)) pArr pCp) :=
    fun j => (Ring.Kv.consumer_observes hX H (b := 0) hpol _).1
  -- the box, the spec and the block of each item
  have hbox : ∀ j : Fin 8, ∃ (isV' slab' hh' : Nat), isV' ≤ 1 ∧ slab' ≤ 1 ∧ hh' ≤ 1 ∧
      ∃ (o : TensorCopy.Observation) (al col row : Nat) (bar : Loc),
        X.TensorIssue (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block) (i % 3)
          (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3)) al o.spec ∧
        X.tensor (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block) (i % 3)
          (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3)) = some o ∧
        CopyBlock Q L X (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block) (i % 3)
          (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3)) i ∧
        o.spec.mbar = kvReady L (gm / L.block) (i % 3) ∧
        Ring.Kv.copyUse X (Lp.slotOf Q L X (gm / L.block) (i % 3) (G.cm (gm / L.block)) pArr
          pCp) (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block) (i % 3)
          (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3)) = i / 3 ∧
        o.spec = kvCopySpec Q (gm / L.block) col row
          (L.sharedBase + 32768 * (i % 3) + 98304 * isV' + 8192 * slab' + 16384 * hh') bar := by
    intro j
    obtain ⟨pc, al, sp, he, hmb, huse, o, hobs, hos⟩ := item_copy hX H (hx j) (by simp)
    generalize Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block) (i % 3) (G.cm (gm / L.block)) pArr
      pCp) ⟨j.val + 1, by omega⟩ (i / 3) = e at he huse hobs ⊢
    obtain ⟨g1, k1⟩ := e
    obtain ⟨t, ht, v1, s1, h1, hv1, hs1, hh1, hmt, ⟨col, row, bar, hsp⟩, ib, hcb, hib⟩ :=
      copy_dst hpre hX hf he
    have hkv : kvReady L (g1 / L.block) t = kvReady L (gm / L.block) (i % 3) := hmt.symm.trans hmb
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, Loc.mk.injEq] at hkv
    obtain ⟨-, hc1, ht1⟩ := hkv
    have htt : t = i % 3 := by omega
    obtain ⟨-, hcu⟩ := Sx.copy_use_block hpre hX hf hR hp hs3 hP (G.cm (gm / L.block)) he
      (by rw [hmt, hc1, htt]) hcb
    have hib' : ib = i := by
      have := hcu.symm.trans huse
      omega
    subst hib'
    refine ⟨v1, s1, h1, hv1, hs1, hh1, o, al, col, row, bar, ⟨pc, by rw [hos]; exact he⟩, hobs,
      hcb, by rw [hos, hmt, hc1, htt], huse, ?_⟩
    rw [hos, hsp, hc1, htt]
  choose isVf slabf hhf hVf hSf hHf o al col row bar hTI hobs hcb hmb huse hspec using hbox
  -- the boxes of the eight items are distinct
  have hinj : Function.Injective (fun j : Fin 8 =>
      (⟨4 * isVf j + 2 * slabf j + hhf j, by
        have := hVf j; have := hSf j; have := hHf j; omega⟩ : Fin 8)) := by
    intro j j' hjj
    simp only [Fin.mk.injEq] at hjj
    have := hVf j; have := hSf j; have := hHf j
    have := hVf j'; have := hSf j'; have := hHf j'
    have e1 : isVf j = isVf j' := by omega
    have e2 : slabf j = slabf j' := by omega
    have e3 : hhf j = hhf j' := by omega
    have hw : ∀ j : Fin 8, TensorCopy.writeLoc (o j).spec 0 0 0 = some ⟨.shared, gm / L.block,
        kvAddr L.sharedBase (i % 3) (isVf j) (64 * slabf j) (64 * hhf j) 0⟩ := by
      intro j
      rw [hspec j]
      exact box_loc hsb (hSf j) (hHf j)
    have hcov : ∀ j : Fin 8, AsyncCovers X (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block)
        (i % 3) (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3))
        (.write (.load 0 0 0)) ⟨.shared, gm / L.block,
          kvAddr L.sharedBase (i % 3) (isVf j) (64 * slabf j) (64 * hhf j) 0⟩ :=
      fun j => ⟨{ loc := _, size := 1 }, true, ⟨rfl, (o j).spec, al j, hTI j, hw j, rfl⟩,
        ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
    have hmo : ∀ (j : Fin 8) pc a sp, X.get (Ring.Kv.opF X (Lp.slotOf Q L X (gm / L.block)
        (i % 3) (G.cm (gm / L.block)) pArr pCp) ⟨j.val + 1, by omega⟩ (i / 3)) =
        some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReady L (gm / L.block) (i % 3) := by
      intro j pc a sp he
      obtain ⟨pc0, he0⟩ := hTI j
      rw [he0] at he
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he
      rw [← he.2.2]
      exact hmb j
    have hcov' := hcov j'
    rw [← e1, ← e2, ← e3] at hcov'
    obtain ⟨heq, -⟩ := Sx.copy_same_use hpre hX hf hR hp hs3 hP (G.cm (gm / L.block)) (hcov j)
      hcov' (hmo j) (hmo j') ((huse j).trans (huse j').symm)
    have hk := item_inj H (hx j) (hx j') (by simp) (by simp) heq
    simp only [Fin.mk.injEq] at hk
    exact Fin.ext (by omega)
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hinj)
    ⟨4 * isV + 2 * slab + hh, by omega⟩
  simp only [Fin.mk.injEq] at hj
  have := hVf j; have := hSf j; have := hHf j
  have e1 : isVf j = isV := by omega
  have e2 : slabf j = slab := by omega
  have e3 : hhf j = hh := by omega
  refine ⟨_, o j, al j, col j, row j, bar j, hTI j, hobs j, hcb j, ?_⟩
  rw [hspec j, e1, e2, e3]

end
end PTX.Kernels.InklingRelDecode.Proof.Wz
