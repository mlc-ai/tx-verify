-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemLifeBar
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Protocol.RegionRead

@[expose] public section

/-! # The Tensor Memory base word

Each CTA's base word (`+328`, four bytes) holds the Tensor Memory address its warp 12 allocated.
Only threads access it (`base_thread`: the other proxies' shared accesses are past the staging
buffers or tensor-store source reads of them, `async_shared`). Its one writer is lane 0 of warp
12, right after its allocation and before its first event on barrier 2 (`OlderFacts.base_write`);
its readers are threads of warp 12 after their `bar.sync 2` of ordinal 0
(`OlderFacts.base_read`). Every thread of warps 0-12 of the CTA, lane 0 included, has its event
of ordinal 0 on barrier 2 once a reader passed its `bar.sync` (`TmemLife.member`), so the write
happens before every read (`write_baseCausality_read`, `TmemLife.bar2_baseCausality`), and two
writes are one thread's, in program order. So the base word's conflicts are ordered (`baseOrdered`).

A read of the base word by warp 12 returns the bytes of lane 0's write (`baseRead`): the write
exists before lane 0's first event on barrier 2 (`OlderFacts.base_written`), it is visible to the
read, and it is the only write of the word (a thread allocates once, `TmemFacts.event`), so it is
the read's latest visible write at each byte (`ConflictsOrdered.read_byte`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

namespace BaseWord

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A byte of a CTA's base word. -/
def InBaseWord (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 328 ≤ l.addr ∧ l.addr < L.sharedBase + 332

/-- Only threads access the base word. -/
theorem base_thread {K : Kernel} {A : List Assumption} (hX : Consistent L K A mem0 X)
    (hr : RingFacts L X) (hout : OutputFacts L X) (htm : TmemFacts L X)
    (hmma : MmaReadsRings L X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc}
    (h : X.Intent ref a w) (hc : a.Covers l) (hl : InBaseWord L l) :
    ∃ e, ref = .thread e ∧ X.Access e a w := by
  rcases ref with e | ⟨i, p⟩
  · exact ⟨e, rfl, h⟩
  · exfalso
    obtain ⟨hs, -, h2⟩ := hl
    rcases async_shared hX hr hout htm hmma h hc hs with h3 | ⟨-, -, h3, -⟩ <;> omega

/-- The thread of a lane-0 index of a CTA is that CTA's lane 0 of warp 12. -/
theorem lane0_of {g : Nat} (h : g % L.block = 384) : g = TmemAlloc.lane0 L (ctaOf L g) := by
  have := Nat.div_add_mod g L.block
  unfold TmemAlloc.lane0 ctaOf
  rw [Nat.mul_comm]
  omega

/-- A byte covered by an access is in the access's CTA. -/
theorem cta_of_covers {a : Acc} {l : Loc} (h : a.Covers l) : l.cta = a.loc.cta := h.2.1

/-- **The base word's write happens before every read of it.** -/
theorem write_baseCausality_read (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (hl : TmemLifeFacts L X) (has : AsyncFacts P L X)
    (ho : OlderFacts P L X) {gw kw gr kr : Nat} {aw ar : Acc} {bw : List Byte}
    {br : List (Option Byte)} {l : Loc} (hw : X.Writes (gw, kw) aw bw) (hcw : aw.Covers l)
    (hr : X.Reads (gr, kr) ar br) (hcr : ar.Covers l) (hlb : InBaseWord L l) :
    baseCausality L X (gw, kw) (gr, kr) := by
  obtain ⟨hs, h1, h2⟩ := hlb
  obtain ⟨h384, hloc, -, -, hord, -⟩ := ho.base_write hw hcw h1 h2
  obtain ⟨-, b, hbk, hsync⟩ := ho.base_read hr hcr h1 h2
  have hcr' : ar.loc.cta = ctaOf L gr :=
    has.access_own (.inl ⟨br, hr, rfl⟩) (by rw [← hcr.1]; exact hs)
  have hcta : ctaOf L gw = ctaOf L gr := by
    rw [← hcr', ← cta_of_covers hcr, cta_of_covers hcw, hloc]
    rfl
  obtain ⟨pcr, hgr⟩ := hr
  obtain ⟨pcw, hgw⟩ := hw
  have hlen := len_of_get hgr
  have hww : warpOf L gw < 13 := by unfold warpOf; omega
  obtain ⟨i, pci, mi, hi, hio⟩ := TmemLife.member hpre hX hst hl hsync hbk hlen (by decide)
    hcta hww
  have hki : kw < i := by
    rcases Nat.lt_trichotomy kw i with hlt | rfl | hgt
    · exact hlt
    · rw [hgw] at hi
      cases hi
    · have := Stats.barOrd_lt hi hgt
      omega
  exact TmemLife.bar2_baseCausality hpre hX hst hl hi hio hsync hcta hki hbk hlen

/-- **The base word's conflicts are ordered.** -/
theorem baseOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hout : OutputFacts L X) (htm : TmemFacts L X)
    (hmma : MmaReadsRings L X) (hst : StatsFacts L X) (hl : TmemLifeFacts L X)
    (has : AsyncFacts P L X) (ho : OlderFacts P L X) : ConflictsOrdered L X (InBaseWord L) := by
  intro e f a b l hcon ha hb' hlb
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hcon
  obtain ⟨⟨g, k⟩, rfl, hae⟩ := base_thread hX hr hout htm hmma he ha hlb
  obtain ⟨⟨g', k'⟩, rfl, haf⟩ := base_thread hX hr hout htm hmma hf hb' hlb
  rcases hae with ⟨bs, hre, rfl⟩ | ⟨bs, hwe, rfl⟩ | ⟨o, n, pc, hge⟩ <;>
    rcases haf with ⟨bs', hrf, rfl⟩ | ⟨bs', hwf, rfl⟩ | ⟨o', n', pc', hgf⟩
  any_goals exact (htm.no_rmw hge).elim
  any_goals exact (htm.no_rmw hgf).elim
  · rcases hw with h | h <;> cases h
  · exact .inr (.inl (write_baseCausality_read hpre hX hst hl has ho hwf hb' hre ha hlb))
  · exact .inl (.inl (write_baseCausality_read hpre hX hst hl has ho hwe ha hrf hb' hlb))
  · obtain ⟨-, h1, h2⟩ := hlb
    obtain ⟨h384, hloc, -⟩ := ho.base_write hwe ha h1 h2
    obtain ⟨h384', hloc', -⟩ := ho.base_write hwf hb' h1 h2
    have hcta : ctaOf L g = ctaOf L g' := by
      have e1 := cta_of_covers ha
      have e2 := cta_of_covers hb'
      rw [hloc] at e1
      rw [hloc'] at e2
      exact e1.symm.trans e2
    have hg : g = g' := by rw [lane0_of h384, lane0_of h384', hcta]
    subst hg
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hkk with hlt | hlt
    · exact .inl (.inl (.single (.inl (po_of_overlap (.inr (.inl ⟨bs, hwe, rfl⟩))
        (.inr (.inl ⟨bs', hwf, rfl⟩)) rfl hlt hov))))
    · exact .inr (.inl (.single (.inl (po_of_overlap (.inr (.inl ⟨bs', hwf, rfl⟩))
        (.inr (.inl ⟨bs, hwe, rfl⟩)) rfl hlt hov.symm))))

/-- An allocation is its thread's first resource operation. -/
theorem alloc_first (htm : TmemFacts L X) {g j pc n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (hg : g < L.threads) (h : X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) :
    Tmem.Pair.tmemOps ((X.tr g).take j) = 0 := by
  obtain ⟨-, -, hs, -⟩ := htm.event hg h
  have := Tmem.Pair.actIdx_of_shape hs
  simp only [Tmem.Pair.actIdx] at this
  exact this.symm

/-- **A thread allocates once.** -/
theorem alloc_unique (htm : TmemFacts L X) {g j j' pc pc' n n' : Nat} {grp grp' : CtaGroup}
    {dst dst' : Option Loc} (hg : g < L.threads)
    (h : X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (h' : X.get (g, j') = some ⟨pc', .tc (.resource grp' dst' (.alloc n'))⟩) : j = j' := by
  have step : ∀ {j j' pc pc' n n' : Nat} {grp grp' : CtaGroup} {dst dst' : Option Loc},
      X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
      X.get (g, j') = some ⟨pc', .tc (.resource grp' dst' (.alloc n'))⟩ → ¬ j < j' := by
    intro j j' pc pc' n n' grp grp' dst dst' h h' hlt
    have e1 := Stats.countP_take_succ (p := Tmem.Pair.isTmemOp) (show (X.tr g)[j]? = _ from h)
    have e2 := (List.take_sublist_take_left (l := X.tr g) (show j + 1 ≤ j' by omega)).countP_le
      (p := Tmem.Pair.isTmemOp)
    have z' := alloc_first htm hg h'
    simp only [Tmem.Pair.isTmemOp, ↓reduceIte] at e1
    unfold Tmem.Pair.tmemOps at z'
    omega
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact (step h h' hlt).elim
  · exact heq
  · exact (step h' h hgt).elim

/-- **A read of the base word by warp 12 returns lane 0's write.** -/
theorem baseRead (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (htm : TmemFacts L X) (hl : TmemLifeFacts L X)
    (has : AsyncFacts P L X) (ho : OlderFacts P L X) (hr : RingFacts L X)
    (hout : OutputFacts L X) (hmma : MmaReadsRings L X)
    (hord : ConflictsOrdered L X (InBaseWord L)) : TmemAlloc.BaseRead L X := by
  intro g k pc a bs hg hget hloc hsz hw12
  have hrd : X.Reads (g, k) a bs := ⟨pc, hget⟩
  have hl0 : InBaseWord L (a.loc.at 0) := by
    rw [hloc]
    exact ⟨rfl, by simp [Loc.at, baseLoc], by simp [Loc.at, baseLoc]⟩
  have hc0 : a.Covers (a.loc.at 0) := Acc.covers_at (by omega)
  obtain ⟨-, b, hbk, hsync⟩ := ho.base_read hrd hc0 hl0.2.1 hl0.2.2
  -- lane 0's first event on barrier 2, and its write before it
  set z := TmemAlloc.lane0 L (ctaOf L g) with hz
  have hzm : z % L.block = 384 := by
    rw [hz]
    unfold TmemAlloc.lane0
    rw [hpre.block]
    omega
  have hzc : ctaOf L z = ctaOf L g := by
    rw [hz]
    unfold TmemAlloc.lane0 ctaOf
    rw [hpre.block]
    omega
  have hzw : warpOf L z < 13 := by unfold warpOf; omega
  obtain ⟨i, pci, mi, hi, -⟩ := TmemLife.member hpre hX hst hl hsync hbk (len_of_get hget)
    (by decide) hzc hzw
  have hzt : z < L.threads := Frame.lt_of_get hX hi
  obtain ⟨kw, -, wa, wbs, hwr, hwloc, hwsz⟩ := ho.base_written hzt hzm hi
  have hsame : wa.loc = a.loc := by rw [hwloc, hloc, hzc]
  have hcov : ∀ q < 4, wa.Covers (a.loc.at q) := fun q hq => by
    have := Acc.covers_at (a := wa) (k := q) (by omega)
    rwa [hsame] at this
  obtain ⟨-, -, -, hwlen, -, j, pca, grp, dst, n, rfl, hal⟩ :=
    ho.base_write hwr (hcov 0 (by decide)) hl0.2.1 hl0.2.2
  obtain ⟨pcw, hwget⟩ := hwr
  have hwr : X.Writes (z, j + 1) wa wbs := ⟨pcw, hwget⟩
  refine ⟨j, pca, grp, dst, n, pcw, wa, wbs, hal, hwget, ?_⟩
  have hbl : bs.length = 4 := by
    have := (hX.rf (.thread (g, k)) a bs (show X.MemReads (.thread (g, k)) a bs from .inl hrd)).1
    omega
  apply List.ext_getElem?
  intro q
  by_cases hq : q < 4
  · have hlq : InBaseWord L (a.loc.at q) := by
      rw [hloc]
      exact ⟨rfl, by simp [Loc.at, baseLoc], by simp only [Loc.at, baseLoc]; omega⟩
    have hcq : a.Covers (a.loc.at q) := Acc.covers_at (by omega)
    have hlast : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at q) →
        modelCausality L X (a.loc.at q) w' (.thread (g, k)) →
          w' = .thread (z, j + 1) ∨ modelCausality L X (a.loc.at q) w' (.thread (z, j + 1)) := by
      intro w' dst' bytes hm hc' _
      obtain ⟨⟨g', k'⟩, rfl, -⟩ := base_thread hX hr hout htm hmma hm.intent hc' hlq
      have hw' : X.Writes (g', k') dst' bytes :=
        (Execution.memWrites_thread_iff_of_not_rmw fun _ _ _ _ h => htm.no_rmw h).mp hm
      obtain ⟨h384, hloc', -, -, -, j', pc', grp', dst'', n', rfl, hal'⟩ :=
        ho.base_write hw' hc' hlq.2.1 hlq.2.2
      have hc1 := cta_of_covers hc'
      have hc2 : (a.loc.at q).cta = ctaOf L g := by rw [hloc]; rfl
      rw [hloc'] at hc1
      have hgz : g' = z := by
        rw [lane0_of h384, hz]
        exact congrArg _ (hc1.symm.trans hc2)
      subst hgz
      rw [alloc_unique htm hzt hal' hal]
      exact .inl rfl
    rw [hord.read_byte hX (e := .thread (g, k)) (w := .thread (z, j + 1))
      (show X.MemReads (.thread (g, k)) a bs from .inl hrd) (by omega)
      (fun _ _ _ _ ⟨_, _, h⟩ => htm.no_rmw h) hlq
      (show X.MemWrites (.thread (z, j + 1)) wa wbs from .inl hwr) (hcov q hq)
      (.inl (write_baseCausality_read hpre hX hst hl has ho hwr (hcov q hq) hrd hcq hlq)) hlast]
    simp only [wbyte, hsame, Loc.at, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show q < wbs.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end BaseWord

end
end PTX.Kernels.FlashAttn4Fwd.Proof
