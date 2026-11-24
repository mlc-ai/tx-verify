-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.ResourceTmem

@[expose] public section

/-! # The `tcgen05` clauses of `AlignedMismatch`, from the interface

A warp-collective `tcgen05` event is at a position of its warp's sequence (`ThreadFacts.tc_coll`):
a tile's load or wait, counted by the thread's tiles (its successful response polls), or one of
warp 0's paired operations. Two lanes of a warp at the same count agree on the position unless one
has more tiles than the other has at its exit operations; then the one with more tiles read, after
the other's latest poll, the response the other read (`AllResponsesAgree`), which claims no CTA,
yet went on polling (`fails_bound`). So the lanes agree on the source line and on the operands
(the deallocations' bases are the CTA's allocation column, `BaseValue`). A consumer exits after all
of its collective events (`ThreadFacts.tc_exit`), as many as its tiles give; a lane of its warp
with more collective events has more tiles, again against the response (`no_tc_unsafe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A list's prefix of a prefix. -/
theorem respPolls_take_take {L : Launch} {g : Nat} {es : List Event} {j k : Nat} (h : j ≤ k) :
    respPolls L g ((es.take k).take j) = respPolls L g (es.take j) := by
  rw [List.take_take, Nat.min_eq_left h]

/-- **A lane with more tiles than another lane of its CTA had at its latest, non-claiming
response read** contradicts the response: it read the same response after its own poll of that
number, and every non-claiming read is after its own latest poll. -/
theorem fails_bound (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hagree : AllResponsesAgree L X) {g h kg kh : Nat} {ev : Event}
    (hcta : g / L.block = h / L.block) (hev : X.get (g, kg) = some ev)
    (hnr : ∀ pcr src bs, ev ≠ ⟨pcr, .rd src bs⟩)
    (hlast : NcLast L g ((X.tr g).take kg)) (hread : NcRead L h ((X.tr h).take kh))
    (hlt : respPolls L h ((X.tr h).take kh) < respPolls L g ((X.tr g).take kg)) : False := by
  have hg : g < L.threads := Frame.lt_of_get hX hev
  have hkg : kg < (X.tr g).length := len_of_get hev
  obtain ⟨jh, rr, ⟨pch, ph, acqh, sch, pcrh, srch, bsh, hph, hrh, hfh, hrr⟩, hjh, hnc⟩ := hread
  have hjhk : jh + 1 < kh := by
    have := (List.getElem?_eq_some_iff.mp hrh).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt (by omega)] at hph
  rw [List.getElem?_take_of_lt hjhk] at hrh
  rw [respPolls_take_take (by omega)] at hjh
  -- the poll of g with as many polls before it
  obtain ⟨jg, hjg, hjgl, hpoll, hcnt⟩ := Tmem.Pair.countP_take_occ
    (okPoll (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)) (X.tr g) kg
    (respPolls L h ((X.tr h).take jh)) (by simp only [respPolls, okPolls] at hjh hlt ⊢; omega)
  obtain ⟨pg, acqg, scg, hkind⟩ := okPoll_wait_form hpoll
  have hpg : X.get (g, jg) =
      some ⟨(X.tr g)[jg].pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) pg true acqg scg⟩ := by
    rw [← hkind]
    exact List.getElem?_eq_getElem hjgl
  obtain ⟨pcrg, srcg, bsg, hrg, hfg⟩ := ht.poll_read hg hpg (by omega)
  have hjgk : jg + 1 < kg := by
    rcases Nat.lt_or_ge (jg + 1) kg with h1 | h1
    · exact h1
    · have : jg + 1 = kg := by omega
      subst this
      rw [hrg] at hev
      exact absurd (Option.some.inj hev).symm (hnr _ _ _)
  have hbs := hagree (h / L.block / 2) g h jg jh _ pch pg ph pcrg pcrh acqg acqh scg sch srcg srch
    bsg bsh (by rw [hcta]) rfl hpg hph (by simpa only [respPolls, okPolls] using hcnt) hrg hfg hrh
    hfh
  subst hbs
  have h1 := hlast jg rr ⟨_, pg, acqg, scg, pcrg, srcg, bsg,
    by rw [List.getElem?_take_of_lt (by omega)]; exact hpg,
    by rw [List.getElem?_take_of_lt hjgk]; exact hrg, hfg, hrr⟩ hnc
  rw [respPolls_take_take (by omega)] at h1
  simp only [respPolls, okPolls] at h1 hcnt hjh hlt
  omega

/-- A position's operands bound it. -/
theorem kind_le {L : Launch} {g p : Nat} {kd : TcKind} (h : TcCollKind L g p kd) : p ≤ 34 := by
  unfold TcCollKind at h
  split_ifs at h with h1 h2 h3 <;> omega

/-- **Two lanes of a warp agree on a position's operands**; the deallocations free the column of
their CTA's allocation. -/
theorem kind_eq (ht : ThreadFacts L X) (hbv : BaseValue L X) {g h p kg kh pcg pch : Nat}
    {ke kf : TcKind} (hw : SameWarp L g h) (hge : X.get (g, kg) = some ⟨pcg, .tc ke⟩)
    (hhe : X.get (h, kh) = some ⟨pch, .tc kf⟩) (hke : TcCollKind L g p ke)
    (hkf : TcCollKind L h p kf) : tcStatic ke = tcStatic kf := by
  obtain ⟨⟨hg, hh, hcta⟩, hwarp⟩ := hw
  unfold TcCollKind at hke hkf
  split_ifs at hke hkf with h1 h2 h3 h4
  · obtain ⟨v, rfl⟩ := hke
    obtain ⟨v', rfl⟩ := hkf
    simp [tcStatic, hwarp]
  · rw [hke, hkf]
  · rw [hke, hkf]
    simp [hcta]
  · rw [hke, hkf]
  · obtain ⟨-, a, rfl⟩ := hke
    obtain ⟨-, a', rfl⟩ := hkf
    obtain ⟨-, pcr, ra, bs, hrd, hloc, hsz, hcol⟩ := ht.dealloc_base hg hge
    obtain ⟨pca, pcw, col, hal, h21, -, hbs⟩ := hbv _ _ _ _ _ hrd hloc hsz
    obtain ⟨-, pcr', ra', bs', hrd', hloc', hsz', hcol'⟩ := ht.dealloc_base hh hhe
    obtain ⟨pca', pcw', col', hal', h21', -, hbs'⟩ := hbv _ _ _ _ _ hrd' hloc' hsz'
    rw [← hcta, h21] at h21'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at h21'
    have hc : PTX.Proof.b32 col = PTX.Proof.b32 col' := by
      have h0 := congrArg List.head? h21'.2.2
      simp only [Value.toBytes, Value.bytes, PTX.Proof.b32, List.head?_map,
        show (List.range 4).head? = some 0 from rfl, Option.map_some, Option.some.injEq,
        Value.byteAt, Prod.mk.injEq, and_true] at h0
      exact h0
    rw [← hc] at hbs'
    simp [tcStatic, hcol col hbs, hcol' col hbs']

/-- **Two lanes of a warp at the same count are at the same position.** -/
theorem pos_eq (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hagree : AllResponsesAgree L X) {g h kg kh pcg pch pg ph : Nat} {ke kf : TcKind}
    (hw : SameWarp L g h) (hge : X.get (g, kg) = some ⟨pcg, .tc ke⟩)
    (hhe : X.get (h, kh) = some ⟨pch, .tc kf⟩) (hag : TcCollAt L g pg ((X.tr g).take kg))
    (hah : TcCollAt L h ph ((X.tr h).take kh)) (hpg : pg ≤ 34) (hph : ph ≤ 34)
    (hn : ((X.tr g).take kg).countP isTcColl = ((X.tr h).take kh).countP isTcColl) :
    pg = ph := by
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hw
  obtain ⟨gl, g32, g0, g33, gnl⟩ := hag
  obtain ⟨hl, h32, h0, h33, hnl⟩ := hah
  rw [hwarp] at gl g32
  have hbg := fails_bound (h := h) (kh := kh) hX ht hagree hcta hge (by intro _ _ _ h; cases h)
  have hbh := fails_bound (h := g) (kh := kg) hX ht hagree hcta.symm hhe
    (by intro _ _ _ h; cases h)
  rcases Nat.lt_or_ge pg 32 with hpg32 | hpg32 <;> rcases Nat.lt_or_ge ph 32 with hph32 | hph32
  · have := gl hpg32
    have := hl hph32
    omega
  · rcases Nat.lt_or_ge ph 33 with hph33 | hph33
    · have h0' := h0 (by omega)
      have := gl hpg32
      simp only [h32 hph32, ↓reduceIte] at this
      omega
    · obtain ⟨h1, hrd⟩ := h33 hph33
      have := gl hpg32
      simp only [h32 hph32, ↓reduceIte] at this
      exact (hbg (gnl (by omega)) hrd (by omega)).elim
  · rcases Nat.lt_or_ge pg 33 with hpg33 | hpg33
    · have g0' := g0 (by omega)
      have := hl hph32
      simp only [g32 hpg32, ↓reduceIte] at this
      omega
    · obtain ⟨g1, grd⟩ := g33 hpg33
      have := hl hph32
      simp only [g32 hpg32, ↓reduceIte] at this
      exact (hbh (hnl (by omega)) grd (by omega)).elim
  · rcases Nat.lt_or_ge pg 33 with hpg33 | hpg33 <;>
      rcases Nat.lt_or_ge ph 33 with hph33 | hph33
    · omega
    · have := g0 (by omega)
      have := (h33 hph33).1
      omega
    · have := h0 (by omega)
      have := (g33 hpg33).1
      omega
    · have := (g33 hpg33).1
      have := (h33 hph33).1
      omega

/-- **A lane's collective event is before the exit of every lane of its warp**: the exit follows
as many collective events as the exiting lane's tiles give. -/
theorem exit_after (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hagree : AllResponsesAgree L X) {g h kg kh pcg pg : Nat} {ke : TcKind}
    (hw : SameWarp L g h) (hge : X.get (g, kg) = some ⟨pcg, .tc ke⟩)
    (hag : TcCollAt L g pg ((X.tr g).take kg)) (hpg : pg ≤ 34)
    (hex : TcExitAt L h ((X.tr h).take kh))
    (hle : ((X.tr h).take kh).countP isTcColl ≤ ((X.tr g).take kg).countP isTcColl) : False := by
  obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hw
  obtain ⟨gl, g32, g0, g33, gnl⟩ := hag
  obtain ⟨hcnt, hrd⟩ := hex
  rw [← hwarp] at hcnt
  have hb := fails_bound (h := h) (kh := kh) hX ht hagree hcta hge (by intro _ _ _ h; cases h)
    (gnl ?_) hrd
  rotate_left
  · intro h32
    have h0 := g32 (by omega)
    rw [g0 h32] at hle
    simp only [h0, ↓reduceIte] at hcnt
    omega
  rcases Nat.lt_or_ge pg 32 with hpg32 | hpg32
  · have := gl hpg32
    by_cases h0 : g % L.block / 32 = 0 <;> simp only [h0, ↓reduceIte] at this hcnt <;>
      exact hb (by omega)
  · have h0 := g32 hpg32
    simp only [h0, ↓reduceIte] at hcnt
    rcases Nat.lt_or_ge pg 33 with hpg33 | hpg33
    · rw [g0 (by omega)] at hle
      omega
    · have := (g33 hpg33).1
      exact hb (by omega)

/-- **No warp-collective `tcgen05` mismatch**: two lanes of a warp at the same collective count
make the same instruction with the same operands, and no lane exits before a collective event of
another lane of its warp. -/
theorem no_tc_unsafe (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hagree : AllResponsesAgree L X) (hbv : BaseValue L X) :
    ¬ AlignedClass.tc.Divergent L kernel X ∧ ¬ AlignedClass.tc.Exited L kernel X := by
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨⟨g, kg⟩, ⟨h, kh⟩, k, pcg, pch, ke, kf, hw, ⟨⟨evg, hevg, hcg⟩, hgk⟩,
      ⟨⟨evh, hevh, hch⟩, hhk⟩, hge, hhe, hne⟩ := (AlignedClass.divergent_tc_iff L).mp hd
    rw [hge] at hevg
    rw [hhe] at hevh
    cases hevg
    cases hevh
    obtain ⟨-, pg, hpcg, hkg, hag⟩ := ht.tc_coll (Frame.lt_of_get hX hge) hge hcg
    obtain ⟨-, ph, hpch, hkh, hah⟩ := ht.tc_coll (Frame.lt_of_get hX hhe) hhe hch
    have hp := pos_eq hX ht hagree hw hge hhe hag hah (kind_le hkg) (kind_le hkh)
      (hgk.trans hhk.symm)
    subst hp
    rcases hne with hne | hne
    · exact hne (hpcg.trans hpch.symm)
    · exact hne (by rw [kind_eq ht hbv hw hge hhe hkg hkh])
  · obtain ⟨⟨g, kg⟩, ⟨h, kh⟩, k, hw, ⟨⟨ev, hev, hcoll⟩, hgk⟩, ⟨⟨pcx, hhx⟩, hle⟩⟩ :=
      (AlignedClass.exited_tc_iff L).mp hd
    obtain ⟨pc', kd, rfl⟩ : ∃ pc' kd, ev = ⟨pc', .tc kd⟩ := by
      obtain ⟨pc', kind⟩ := ev
      cases kind <;> simp [isTcColl] at hcoll
      exact ⟨pc', _, rfl⟩
    obtain ⟨hw8, pg, -, hkg, hag⟩ := ht.tc_coll (Frame.lt_of_get hX hev) hev hcoll
    have hw8h : h % L.block / 32 < 8 := hw.2 ▸ hw8
    have hex := ht.tc_exit (Frame.lt_of_get hX hhx) hw8h hhx
    exact exit_after hX ht hagree hw hev hag (kind_le hkg) hex
      (((List.take_sublist _ _).countP_le).trans (hle.trans hgk.ge))

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
