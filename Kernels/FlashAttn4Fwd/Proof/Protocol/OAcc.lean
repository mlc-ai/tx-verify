-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Lemmas.Tcgen05.AccumulateStored

@[expose] public section

/-! # The output accumulator

Stage `st`'s output accumulator `O` (Tensor Memory columns `256 + 128 st …`, `InO`) of a pair is
written by the PV MMAs of each tile `u` (`pPolls = u + 1`: after the MMA thread's poll of phase `u`
of the P-ready object) and by the correction threads' rescale stores, and loaded by the correction
threads. The correction's load or store of credit `q` (`pArr = q`) lies between the PV MMAs of tiles
`q - 1` and `q`: its arrival of credit `q` is in phase `q` of the P-ready object (`PReadyHandoff`),
which the PV MMAs of tile `q` wait for.

**OReady** (`OReady`): every PV MMA of a tile before `q` is done before a correction load of credit
`q` of its stage. For a rescale this is the softmax's poll of score tile `q` (whose commit tracks
the PV MMAs of tile `q - 1`, `Score.sfull_observes`) followed by the statistics barrier to the
correction's `bar.sync`; for the final pass it is the correction's poll of the O-full object
(+192 + 8 st). Both chains go through the statistics and O-full protocols; it is a premise here
(derived in `OAccReady`, `oready`, from SFull, the O-full handoff and the loads' routes).

Exports:
* **OSource** (`o_loadStable`, `o_readSource`): a correction load of credit `q` reads, at each
  cell, the last PV MMA of tile `q - 1` writing it (`src`): an earlier PV MMA is pipelined before
  `src`, a later one waits for the load's implicit `wait::ld` through the correction's arrival of
  credit `q`; an earlier store of the thread is done before `src` (`wait::st`, arrival, poll), a
  later one follows the load (ld→st pipeline).
* **The rescale** (`o_accSource_store`): a correction store of credit `q` is the accumulator source
  of the first PV MMA of tile `q` at its cell (Core `accumulateStored`); `o_rescale_result` is the
  value chain load → `F` → store → accumulate (`TcMma.Result.of_rescale`), with `F` the thread's
  multiplication by `α`, supplied by the Result layer.
* **ORescaleSkip** (`o_accSource_skip`, `o_skip_result`): when no store of credit `q` writes the
  cell (the warp's ballot was zero), the last PV MMA of tile `q - 1` is the accumulator source of
  the first PV MMA of tile `q`, and the value is carried unchanged into the accumulation.

These are the hooks of the max-agnostic value invariant `O = Σ_t 2^(x_t − m_ref) V_t` of the Result
layer: each PV MMA accumulates onto either the previous tile's result or its rescaled copy. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace OAcc
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- **OReady**: every PV MMA of stage `st` of a tile before `q` is done before a correction load of
credit `q` of the stage. -/
def OReady (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a st : Nat} {vals : List Value} {x : EvId}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b →
    (∀ j < vals.length, InO st (tcDataCell32 L h a j)) →
    IsMma X x → (∃ cell, X.MmaCell x cell ∧ InO st cell) → ctaOf L x.1 = leadCta (ctaOf L h) →
    pPolls L X x.1 st x.2 ≤ pArr L X h st i → DoneBefore L X x (h, i)

/-- A correction thread is a producer of every stage's P-ready object. -/
theorem corr_prod {h st : Nat} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) : pProd L (leadCta (ctaOf L h)) st h :=
  ⟨hh, rfl, .inr ⟨h8, h12⟩⟩

/-- An MMA writing a cell of a correction thread's row of an accumulator is in its pair. -/
theorem mma_cta (ht : ScoreFacts L X) {x : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} {st : Nat} (hx : X.MmaIssue x d s acc mask)
    (hc : X.MmaCell x cell) (hO : InO st cell) : ctaOf L x.1 = leadCta cell.cta :=
  ((mma_o ht hx hc hO _ hc).2).symm

/-- A store of a cell of an accumulator is a correction thread's, of the cell's stage. -/
theorem store_corr (hpre : Pre P L mem0) (ht : ScoreFacts L X)
    {h a j st : Nat} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) (hO : InO st (tcDataCell32 L h a j)) (hst : st < 2) {other : EvId}
    (hwo : StoreCell L X other (tcDataCell32 L h a j)) :
    other.1 = h ∧ ∃ a' vals' j', X.TSt other a' vals' .s32x32b ∧ j' < vals'.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h a' j' := by
  obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hwo
  obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
  by_cases hc8 : 8 ≤ warpOf L other.1
  · have hthr := corr_cell_thread hpre h8 h12 hc8 hgw hceq
    subst hthr
    exact ⟨rfl, a', vals', j', hst', hj', hceq⟩
  · have := (ht.soft_st hgl (by omega) hst').1 j' hj'
    rw [← hceq] at this
    unfold InP at this
    unfold InO at hO
    omega

/-- The stage of a correction store's cell. -/
theorem st_stage (ho : OAccFacts L X) {h k a j st : Nat} {vals : List Value}
    (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hs : X.TSt (h, k) a vals .s32x32b) (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L h a j)) :
    1 ≤ pArr L X h st k ∧
      (∃ i' a' vals', i' < k ∧ X.TLd (h, i') a' vals' .s32x32b ∧
        (∀ j < vals'.length, InO st (tcDataCell32 L h a' j)) ∧ pArr L X h st i' = pArr L X h st k) ∧
      ∀ e, NonTcAfter X h k e →
        ∃ w pc, k < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
          pArr L X h st w = pArr L X h st k := by
  obtain ⟨st', -, hc, h1, hld, hw⟩ := ho.corr_st hh h8 h12 hs
  have := hc j hj
  have hs : st' = st := by
    unfold InO at this hO
    omega
  subst hs
  exact ⟨h1, hld, hw⟩

/-- A correction store of credit `q` is done before every MMA of its pair after the poll of
phase `q`. -/
theorem store_done (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    {h k a j st : Nat} {vals : List Value} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) (hst : st < 2) (hs : X.TSt (h, k) a vals .s32x32b)
    (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L h a j)) {f : EvId} (hf : IsMma X f)
    (hc : ctaOf L f.1 = leadCta (ctaOf L h)) (hu : pArr L X h st k + 1 ≤ pPolls L X f.1 st f.2) :
    StoreDoneBefore L X (h, k) f := by
  obtain ⟨-, -, hwait⟩ := st_stage ho hh h8 h12 hs hj hO
  obtain ⟨pcs, hsget⟩ := id hs
  obtain ⟨e, hne, -⟩ := gate_after ht hP hst (corr_prod hh h8 h12) hsget
    (u := pArr L X h st k) le_rfl hf hc hu
  obtain ⟨w, pc, hkw, -, hw, hwk⟩ := hwait e hne
  exact ⟨⟨a, vals, _, hs⟩, .inl ⟨(h, w), ⟨pc, hw⟩, rfl, hkw, .inl
    (overwrite_gate ht hP hst (corr_prod hh h8 h12) (u := pArr L X h st k) hwk.le hf hc hu)⟩⟩

/-- A correction store of credit `q` comes after an MMA that is done before the correction's loads
of credit `q`. -/
theorem done_store (ho : OAccFacts L X) (hR : OReady L X) {h k a j st : Nat}
    {vals : List Value} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hs : X.TSt (h, k) a vals .s32x32b) (hj : j < vals.length) (hO : InO st (tcDataCell32 L h a j))
    {x : EvId} (hx : IsMma X x) (hxc : ∃ cell, X.MmaCell x cell ∧ InO st cell)
    (hc : ctaOf L x.1 = leadCta (ctaOf L h)) (hu : pPolls L X x.1 st x.2 ≤ pArr L X h st k) :
    DoneBefore L X x (h, k) := by
  obtain ⟨-, ⟨i', a', vals', hik, ⟨pc, hld⟩, hcells, heq⟩, -⟩ := st_stage ho hh h8 h12 hs hj hO
  refine DoneBefore.of_po (hR hh h8 h12 ⟨pc, hld⟩ hcells hx hxc hc (by omega))
    (po_of_source_not_access rfl hik (TSt.lt hs) (by rw [hld]; rfl))

/-- **OSource: stability.** A correction load of credit `q` reads, at each of its cells, the last
PV MMA of tile `q - 1` writing the cell (`hlast`), stably. -/
theorem o_loadStable (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) {h i a j st : Nat} {vals : List Value} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (hld : X.TLd (h, i) a vals .s32x32b)
    (hj : j < vals.length) (hO : InO st (tcDataCell32 L h a j)) {src : EvId} (hsrc : IsMma X src)
    (hsc : X.MmaCell src (tcDataCell32 L h a j))
    (hcnt : pPolls L X src.1 st src.2 = pArr L X h st i)
    (hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      pPolls L X x.1 st x.2 ≤ pPolls L X src.1 st src.2 → x = src ∨ x.2 < src.2) :
    ∀ other, TmemWrite L X other (tcDataCell32 L h a j) →
      other = src ∨ WriteBefore L X other src ∨ ReadBefore L X .ld (h, i) other := by
  obtain ⟨st', hst', hcells, hwait, -⟩ := ho.corr_ld hh h8 h12 hld
  have hst : st < 2 := by
    have := hcells j hj
    unfold InO at this hO
    omega
  obtain ⟨d', s', acc', mask', hsi⟩ := hsrc
  have hcs := mma_cta ht hsi hsc hO
  obtain ⟨pcl, hldget⟩ := hld
  intro other hwo
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d, s, acc, mask, -, -, hoi, -⟩ := id hm
    have hco := mma_cta ht hoi hm hO
    have hthr : other.1 = src.1 := ht.tc_one ⟨_, _, _, _, hoi⟩ (.inl ⟨_, _, _, _, hsi⟩)
      (by rw [hco, hcs])
    by_cases hle : pPolls L X other.1 st other.2 ≤ pPolls L X src.1 st src.2
    · rcases hlast other ⟨_, _, _, _, hoi⟩ hm hle with rfl | hlt
      · exact .inl rfl
      · exact .inr (.inl (.inl (mma_writeBefore ht hoi hsi hthr hlt
          (ht.mma_acc hoi hsi hm hsc rfl (.inr ⟨hO, hO⟩)))))
    · obtain ⟨e, hne, -⟩ := gate_after ht hP hst (corr_prod hh h8 h12) hldget
        (u := pArr L X h st i) le_rfl ⟨_, _, _, _, hoi⟩ hco (by omega)
      obtain ⟨pcw, hwait⟩ := hwait hne.succ_lt
      refine .inr (.inr (ReadBefore.of_waitLd hwait rfl (Nat.lt_succ_self i) (.inl ?_)))
      exact overwrite_gate ht hP hst (corr_prod hh h8 h12) (u := pArr L X h st i)
        (by rw [pArr_succ_tc hldget]) ⟨_, _, _, _, hoi⟩ hco (by omega)
  · obtain ⟨hthr, a', vals', j', hst', hj', hceq⟩ := store_corr hpre ht hh h8 h12 hO hst hstc
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    obtain ⟨pcs, hsget⟩ := id hst'
    rcases Nat.lt_trichotomy k i with hlt | rfl | hlt
    · have hle := countP_take_mono (arrivesOn (pReadyBar L (leadCta (ctaOf L g)) st)) (X.tr g)
        hlt.le
      have hne : pArr L X g st k ≠ pArr L X g st i := fun he =>
        absurd (ho.corr_ld_st hh h8 h12 ⟨pcl, hldget⟩ hst' hj hj' hceq hO he.symm) (by omega)
      have hO' : InO st (tcDataCell32 L g a' j') := hceq ▸ hO
      refine .inr (.inl (.inr (.inl (store_done ht ho hP hh h8 h12 hst hst' hj' hO'
        ⟨_, _, _, _, hsi⟩ hcs ?_))))
      unfold pArr arrivals at hne hcnt ⊢
      omega
    · rw [hldget] at hsget
      cases hsget
    · exact .inr (.inr (.inr ⟨⟨⟨hh, hh, rfl⟩, rfl⟩,
        .inl (baseCausality_tc hldget rfl hlt (len_of_get hsget)), ⟨a, vals, _, pcl, hldget⟩,
        a', vals', _, pcs, hsget⟩))

/-- **OSource.** A correction load of credit `q` reads, at each of its cells, the last PV MMA of
tile `q - 1` writing the cell, given that the allocation keeps it live. -/
theorem o_readSource (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) (hR : OReady L X) {h i a j st : Nat} {vals : List Value}
    (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length) (hO : InO st (tcDataCell32 L h a j))
    {src : EvId} (hsrc : IsMma X src) (hsc : X.MmaCell src (tcDataCell32 L h a j))
    (hcnt : pPolls L X src.1 st src.2 = pArr L X h st i)
    (hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      pPolls L X x.1 st x.2 ≤ pPolls L X src.1 st src.2 → x = src ∨ x.2 < src.2)
    (hlive : SourceLive L X src (h, i) (tcDataCell32 L h a j)) :
    ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) := by
  obtain ⟨st', -, hcells, -, -⟩ := ho.corr_ld hh h8 h12 hld
  have hst : st' = st := by
    have := hcells j hj
    unfold InO at this hO
    omega
  subst hst
  obtain ⟨d, s, acc, mask, hsi⟩ := hsrc
  have hcs : ctaOf L src.1 = leadCta (ctaOf L h) := mma_cta ht hsi hsc hO
  have hne : src ≠ (h, i) := by
    rintro rfl
    obtain ⟨pc, hp⟩ := hsi
    obtain ⟨pc', hp'⟩ := hld
    rw [hp] at hp'
    cases hp'
  exact ⟨hne, .inl hsc,
    WriteBefore.of_done (hR hh h8 h12 hld hcells ⟨_, _, _, _, hsi⟩ ⟨_, hsc, hO⟩ hcs hcnt.le),
    o_loadStable hpre ht ho hP hh h8 h12 hld hj hO ⟨_, _, _, _, hsi⟩ hsc hcnt hlast, hlive⟩

/-- **The rescale.** A correction store of credit `q` is the accumulator source of the first PV
MMA of tile `q` writing its cell (`hfirst`). -/
theorem o_accSource_store (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) (hR : OReady L X) {h i a j st : Nat} {vals : List Value}
    (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12)
    (hs : X.TSt (h, i) a vals .s32x32b) (hj : j < vals.length) (hO : InO st (tcDataCell32 L h a j))
    {c : EvId} (hc : IsMma X c) (hcc : X.MmaCell c (tcDataCell32 L h a j))
    (hcnt : pPolls L X c.1 st c.2 = pArr L X h st i + 1)
    (hfirst : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      pArr L X h st i + 1 ≤ pPolls L X x.1 st x.2 → x = c ∨ c.2 < x.2)
    (hlive : SourceLive L X (h, i) c (tcDataCell32 L h a j)) :
    ReadSource L X .acc (h, i) c (tcDataCell32 L h a j) := by
  have hst : st < 2 := by
    obtain ⟨st', hst', hcells, -⟩ := ho.corr_st hh h8 h12 hs
    have := hcells j hj
    unfold InO at this hO
    omega
  obtain ⟨dc, sc, accc, maskc, hci⟩ := hc
  have hcs := mma_cta ht hci hcc hO
  obtain ⟨pcs, hsget⟩ := id hs
  have hne : (h, i) ≠ c := by
    rintro rfl
    obtain ⟨pc', hp⟩ := hci
    rw [hsget] at hp
    cases hp
  refine readSource_acc.mpr ⟨hne, .inr (.inl (storeCell32 hs hj)),
    .inr (.inl (store_done ht ho hP hh h8 h12 hst hs hj hO ⟨_, _, _, _, hci⟩ hcs (by omega))),
    fun other hwo => ?_, hlive⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d, s, acc, mask, -, -, hoi, -⟩ := id hm
    have hco := mma_cta ht hoi hm hO
    have hthr : c.1 = other.1 := ht.tc_one ⟨_, _, _, _, hci⟩ (.inl ⟨_, _, _, _, hoi⟩)
      (by rw [hco, hcs])
    by_cases hle : pPolls L X other.1 st other.2 ≤ pArr L X h st i
    · exact .inr (.inr (.inl (.inl (.inl (done_store ho hR hh h8 h12 hs hj hO
        ⟨_, _, _, _, hoi⟩ ⟨_, hm, hO⟩ hco hle)))))
    · rcases hfirst other ⟨_, _, _, _, hoi⟩ hm (by omega) with rfl | hlt
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr (mma_writeBefore ht hci hoi hthr hlt
          (ht.mma_acc hci hoi hcc hm rfl (.inr ⟨hO, hO⟩)))))
  · obtain ⟨hthr, a', vals', j', hst', hj', hceq⟩ := store_corr hpre ht hh h8 h12 hO hst hstc
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    have hO' : InO st (tcDataCell32 L g a' j') := hceq ▸ hO
    rcases Nat.lt_trichotomy (pArr L X g st k) (pArr L X g st i) with hlt | heq | hgt
    · have hki : k < i := lt_of_count_lt hlt
      obtain ⟨pck, hkget⟩ := id hst'
      exact .inr (.inr (.inl (WriteBefore.of_pipe hst' ⟨⟨hh, hh, rfl⟩, rfl⟩
        (.inl (baseCausality_tc hkget rfl hki (TSt.lt hs))) (.inr ⟨a, vals, _, hs⟩))))
    · exact .inl (by rw [ho.corr_st_one hh h8 h12 hst' hs hj' hj hceq.symm hO' heq])
    · exact .inr (.inr (.inr (.inl (done_store ho hR hh h8 h12 hst' hj' hO' ⟨_, _, _, _, hci⟩
        ⟨_, hcc, hO⟩ hcs (by omega)))))

/-- **ORescaleSkip.** When no store of credit `q` writes a cell of stage `st`'s accumulator, the
last PV MMA of tile `q - 1` writing it (`src`) is the accumulator source of the first PV MMA of
tile `q` writing it (`c`). -/
theorem o_accSource_skip (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) (hR : OReady L X) {st : Nat} {cell : Cell} (hO : InO st cell)
    (hst : st < 2) {src c : EvId} (hsrc : IsMma X src) (hsc : X.MmaCell src cell)
    (hc : IsMma X c) (hcc : X.MmaCell c cell)
    (hcnt : pPolls L X c.1 st c.2 = pPolls L X src.1 st src.2 + 1)
    (hlast : ∀ x, IsMma X x → X.MmaCell x cell →
      pPolls L X x.1 st x.2 ≤ pPolls L X src.1 st src.2 → x = src ∨ x.2 < src.2)
    (hfirst : ∀ x, IsMma X x → X.MmaCell x cell →
      pPolls L X src.1 st src.2 + 1 ≤ pPolls L X x.1 st x.2 → x = c ∨ c.2 < x.2)
    (hskip : ∀ g k a j : Nat, ∀ vals : List Value, X.TSt (g, k) a vals .s32x32b → j < vals.length →
      tcDataCell32 L g a j = cell → pArr L X g st k ≠ pPolls L X src.1 st src.2)
    (hlive : SourceLive L X src c cell) : ReadSource L X .acc src c cell := by
  obtain ⟨ds, ss, accs, masks, hsi⟩ := hsrc
  obtain ⟨dc, sc, accc, maskc, hci⟩ := hc
  have hcs := mma_cta ht hsi hsc hO
  have hcc' := mma_cta ht hci hcc hO
  have hthr : src.1 = c.1 := ht.tc_one ⟨_, _, _, _, hsi⟩ (.inl ⟨_, _, _, _, hci⟩)
    (by rw [hcs, hcc'])
  have hsrc_c : src.2 < c.2 := by
    have : pPolls L X src.1 st src.2 < pPolls L X c.1 st c.2 := by omega
    rw [hthr] at this
    unfold pPolls okPolls at this
    exact lt_of_count_lt this
  have hacc := ht.mma_acc hsi hci hsc hcc rfl (.inr ⟨hO, hO⟩)
  refine readSource_acc.mpr ⟨fun he => by rw [he] at hsrc_c; omega, .inl hsc,
    .inl (mma_writeBefore ht hsi hci hthr hsrc_c hacc), fun other hwo => ?_, hlive⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d, s, acc, mask, -, -, hoi, -⟩ := id hm
    have hco := mma_cta ht hoi hm hO
    by_cases hle : pPolls L X other.1 st other.2 ≤ pPolls L X src.1 st src.2
    · have hthr' : other.1 = src.1 := ht.tc_one ⟨_, _, _, _, hoi⟩ (.inl ⟨_, _, _, _, hsi⟩)
        (by rw [hco, hcs])
      rcases hlast other ⟨_, _, _, _, hoi⟩ hm hle with rfl | hlt
      · exact .inl rfl
      · exact .inr (.inr (.inl (.inl (mma_writeBefore ht hoi hsi hthr' hlt
          (ht.mma_acc hoi hsi hm hsc rfl (.inr ⟨hO, hO⟩))))))
    · have hthr' : c.1 = other.1 := ht.tc_one ⟨_, _, _, _, hci⟩ (.inl ⟨_, _, _, _, hoi⟩)
        (by rw [hco, hcc'])
      rcases hfirst other ⟨_, _, _, _, hoi⟩ hm (by omega) with rfl | hlt
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr (mma_writeBefore ht hci hoi hthr' hlt
          (ht.mma_acc hci hoi hcc hm rfl (.inr ⟨hO, hO⟩)))))
  · obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    by_cases h8 : 8 ≤ warpOf L other.1
    · have hO' : InO st (tcDataCell32 L other.1 a' j') := hceq ▸ hO
      have hcta : cell.cta = ctaOf L other.1 := by rw [hceq]; rfl
      have hq := hskip other.1 other.2 a' j' vals' hst' hj' hceq.symm
      rcases Nat.lt_or_gt_of_ne hq with hlt | hgt
      · exact .inr (.inr (.inl (.inr (.inl (store_done ht ho hP hgl h8 hgw hst hst' hj' hO'
          ⟨_, _, _, _, hsi⟩ (by rw [hcs, hcta]) (by omega))))))
      · exact .inr (.inr (.inr (.inl (done_store ho hR hgl h8 hgw hst' hj' hO'
          ⟨_, _, _, _, hci⟩ ⟨_, hcc, hO⟩ (by rw [hcc', hcta]) (by omega)))))
    · have := (ht.soft_st hgl (by omega) hst').1 j' hj'
      rw [← hceq] at this
      unfold InP at this
      unfold InO at hO
      omega

/-! ## Value hooks -/

end OAcc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
