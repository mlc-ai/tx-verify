-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ClcOwner
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Values
public import Kernels.Fp16Gemm8192.Proof.Support.Addresses

@[expose] public section

/-! # Distinct tensor stores write distinct output bytes

A tensor store is a warp group's first thread's TMA store of a slice of its task's tile
(`ThreadFacts.store_tile`), through the output map, so it writes the element bytes of its slice's
columns and its group's rows of that tile (`store_loc`). A consumer's task is its cluster's own
tile, or the tile of the task the cluster's request numbered `E - 1` was answered with
(`Consumer.TileAt`, `ReaderValues`, `request_task`): the tile of a cluster task `t < 512`
(`tile_task`). The tile fixes the task, and the task fixes the cluster and the request: a launched
task is answered by no request, and two requests answered with one task are one
(`Clc.Owned`). So two stores writing one byte are one CTA's, one warp group's, of one task and one
slice, hence one event (`outputUnique`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy TensorDescriptor

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The tile of cluster task `t`, as the consumers compute it from the task's first CTA. -/
def tileOf (t : Nat) : Nat × Nat := (t / 256 % 2 * 8 + t % 8, t / 8 % 32)

theorem tileOf_inj {t t' : Nat} (ht : t < 512) (ht' : t' < 512) (h : tileOf t = tileOf t') :
    t = t' := by
  simp only [tileOf, Prod.mk.injEq] at h
  omega

/-- The arbitration state's responses name valid tasks of distinct requests. -/
theorem owned (hX : Consistent L kernel Prod mem0 X) : Clc.Owned (Clc.ValidTask L) X.clcState :=
  Clc.owned_of_reachable hX.clc.1

/-- **The task a request is answered with.** A request whose response names a first CTA `x` was
answered with the cluster task `t = x / 2 < 512`. -/
theorem request_task (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {i : EvId}
    {s : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i s tg) {r : ClcResponse}
    (hr : (X.clc i).resolved = some r)
    (hx : (r.firstCta.map fun c => c.1.toNat).getD Loader.none32 ≠ Loader.none32) :
    ∃ t, t < 512 ∧ X.clcState.response (Clc.requestId i) = some (some t) ∧
      (r.firstCta.map fun c => c.1.toNat).getD Loader.none32 = 2 * t := by
  obtain ⟨task, htask, rfl⟩ := (hX.clc.2.2.2.1 i s tg hi).1.result r hr
  rcases task with _ | t
  · exact absurd (by simp [Clc.responseOf]) hx
  have hv := (owned hX).response_valid _ t htask
  have ht : t < 512 := by
    obtain ⟨-, h1, -⟩ := hv
    rw [hpre.oneDimLaunch.1.2.2.2.1, hpre.grid, hpre.cluster] at h1
    omega
  refine ⟨t, ht, htask, ?_⟩
  simp only [Clc.responseOf, Option.map_some, Option.getD_some, BitVec.toNat_ofNat,
    Launch.oneDim_ctaidOf hpre.oneDimLaunch.1, clusterStart_eq hpre]
  omega

/-- The tile of a consumer's task is the tile of a cluster task: its cluster's own for the first
task, the answer of its cluster's request numbered `E - 1` for task `E > 0`. -/
theorem tile_task (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) {g k E m n : Nat} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (h : Consumer.TileAt L g ((X.tr g).take k) E m n) :
    ∃ t, t < 512 ∧ (m, n) = tileOf t ∧
      ((E = 0 ∧ t = g / L.block / 2) ∨
        (0 < E ∧ ∃ i s tg, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * (g / L.block / 2) ∧
          issuesBefore L X (g / L.block / 2) i.1 i.2 = E - 1 ∧
          X.clcState.response (Clc.requestId i) = some (some t))) := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hC : g / L.block < 1024 := by
    rw [← hgrid]
    exact (Nat.div_lt_iff_lt_mul (by rw [hblock]; decide)).mpr hg
  rcases h with
    ⟨rfl, rfl, rfl⟩ | ⟨x, hE, ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, hcj, hj1, hrr, hxe⟩,
      hx, rfl, rfl⟩
  · refine ⟨g / L.block / 2, by omega, ?_, .inl ⟨rfl, rfl⟩⟩
    simp only [tileOf, Loader.claimM, Loader.claimN, Prod.mk.injEq]
    split_ifs <;> omega
  · have hj1l : j + 1 < k := by
      have := (List.getElem?_eq_some_iff.mp hj1).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt (by omega)] at hj
    rw [List.getElem?_take_of_lt hj1l] at hj1
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcj
    have hjg : X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq
        sc⟩ := hj
    have hjg1 : X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ := hj1
    obtain ⟨i, s, tg, r, hi, hic, -, hcnt, hobs, hres, hread⟩ :=
      hv (g / L.block / 2) g j pc p acq sc rfl hjg
    obtain ⟨pcr', a', bs', hget', hfoot⟩ := ht.poll_read hg hjg (len_of_get hjg1)
    rw [hjg1] at hget'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hget'
    obtain ⟨-, rfl, rfl⟩ := hget'
    have hbs := hread pcr a bs hjg1 hfoot
    subst hbs
    rw [responseOf_clc] at hrr
    cases hrr
    obtain ⟨t, htl, htask, hxt⟩ := request_task hpre hX hi hres (hxe ▸ hx)
    refine ⟨t, htl, ?_, .inr ⟨hE, i, s, tg, hi, hic, ?_, htask⟩⟩
    · rw [hxe, hxt]
      simp only [tileOf, Loader.claimM, Loader.claimN, Prod.mk.injEq]
      split_ifs <;> omega
    · simp only [issuesBefore]
      rw [hcnt, hcj]

/-- A store's slot is in the box of the output map. -/
theorem store_slot {b : Nat} {cls : AllocationClass} {origin : Fin 2 → Int} {sb : Loc}
    {x y z : Nat} {l : Loc}
    (h : TensorStore.writeLoc ⟨⟨1, Fp16Gemm8192.mapD b cls, origin, sb, none⟩, none⟩ x y z =
      some l) :
    x < 32 ∧ y < 128 ∧ z < 2 := by
  unfold TensorStore.writeLoc TensorTransfer.slotAt at h
  split_ifs at h with hx hy hz
  · simp only [Fp16Gemm8192.mapD, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
      TensorTile.rowsOf, Format.bytes] at hx hy hz
    simp at hx hy hz
    omega
  all_goals simp at h

/-- **Where a tensor store writes**: the element byte of its slice's column `x` and its group's row
`y` of its task's tile. -/
theorem store_loc (hpre : Pre P L mem0) (ht : ThreadFacts L X) {g k pc a : Nat}
    {sp : TensorStore.Spec} {c : Consumer.D} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) {x y z : Nat} {l : Loc}
    (hl : TensorStore.writeLoc sp x y z = some l) :
    ∃ s : Fin 8, c.site = .tma s ∧ Consumer.first L g = true ∧ c.m < 16 ∧ c.n < 32 ∧ x < 32 ∧
      y < 128 ∧ z < 2 ∧
      l = (elementLoc P.dBase (outputRow c.m (g / L.block % 2) (Consumer.tidOf L g / 32 / 4) y)
        (outputCol c.n s x)).at z ∧
      Consumer.TileAt L g ((X.tr g).take k) (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        ((X.tr g).take k) - 1) c.m c.n := by
  obtain ⟨s, hs, hfirst, hm, hn, hrows, hred, horig, htile⟩ := ht.store_tile hg he hσ
  obtain ⟨hp, hmap⟩ := ht.store_map hg he hσ rfl
  rw [hpre.paramD] at hp
  obtain rfl : P.dMap = a := (Prod.mk.inj (Option.some.inj hp)).2
  rw [hpre.mapD] at hmap
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := sp
  simp only at hrows hred horig hmap hl
  subst hrows hred
  simp only [Option.some.injEq, Sigma.mk.injEq] at hmap
  obtain ⟨rfl, hdesc⟩ := hmap
  cases hdesc
  have hq : Consumer.tidOf L g / 32 / 4 < 2 := by
    have := ht.role_warp hg (len_of_get he).le hσ
    simp only [roleWarp] at this
    show g % L.block / 32 / 4 < 2
    omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have horigin : origin = outputOrigin (taskOfTile c.m c.n) (g / L.block % 2)
      (Consumer.tidOf L g / 32 / 4) s.val := by
    funext i
    rw [horig i]
    simp only [outputOrigin, tensorOrigin, tileM_taskOfTile _ hn, tileN_taskOfTile _ hn,
      outputCol, outputRow]
    split_ifs <;> push_cast <;> omega
  subst horigin
  obtain ⟨hx, hy, hz⟩ := store_slot hl
  have hw := output_writeLoc (base := P.dBase) (cls := P.dClass) (shared := sb)
    (taskOfTile_lt hm hn) hr hq s.isLt hx hy hz
  rw [hw, tileM_taskOfTile _ hn, tileN_taskOfTile _ hn] at hl
  exact ⟨s, hs, hfirst, hm, hn, hx, hy, hz, (Option.some.inj hl).symm, htile⟩

theorem countP_take_le {α : Type} {xs : List α} {p : α → Bool} {m n : Nat} (h : m ≤ n) :
    (xs.take m).countP p ≤ (xs.take n).countP p :=
  List.Sublist.countP_le (List.take_sublist_take_left h)

/-- A consumer's TMA store of slice `s` has made `16 E + 2 s + 2` output barrier arrivals, for its
`E + 1` successful response polls. -/
theorem tma_outBars (ht : ThreadFacts L X) {g k : Nat} {e : Event} {c : Consumer.D} {s : Fin 8}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) (hs : c.site = .tma s) :
    Consumer.outBars L g ((X.tr g).take k) + 16 =
      16 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + 2 * s.val + 2 ∧
    1 ≤ Consumer.outBars L g ((X.tr g).take k) := by
  obtain ⟨q, h1, h2⟩ := ht.cons_bar_phase hg hσ
  have h3 := ht.cons_clc hg he hσ
  obtain ⟨h2k, ⟨pcb, hbar⟩, -⟩ := ht.cons_tma_prev hg (len_of_get he) hσ hs
  have hm := countP_take_le (xs := X.tr g) (p := Consumer.isOutBar L g)
    (show k - 2 + 1 ≤ k by omega)
  have hstep : ((X.tr g).take (k - 2 + 1)).countP (Consumer.isOutBar L g) =
      ((X.tr g).take (k - 2)).countP (Consumer.isOutBar L g) + 1 := by
    have hbar' : (X.tr g)[k - 2]? = some ⟨pcb, .bar (Consumer.outId L g) (some 128)⟩ := hbar
    rw [List.take_add_one, hbar', Option.toList_some, List.countP_append]
    simp [Consumer.isOutBar]
  simp only [Consumer.D.clcHold, Consumer.tileOpen, Consumer.D.inEpi, Consumer.D.outPhase, hs]
    at h1 h2 h3
  unfold Consumer.outBars at h2 ⊢
  omega

/-- Two TMA stores of one slice by one thread, after equally many successful response polls, are
one event: an output barrier arrival comes between two of them. -/
theorem tma_inj (ht : ThreadFacts L X) {g k k' : Nat} {pc pc' a a' : Nat}
    {sp sp' : TensorStore.Spec} {c c' : Consumer.D} {s : Fin 8} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (he' : X.get (g, k') = some ⟨pc', .tensorStore a' sp'⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c))))
    (hσ' : Frame.stateAt (code L) X g k' = some (some (.inr (.cons c')))) (hs : c.site = .tma s)
    (hs' : c'.site = .tma s)
    (hp : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k')) : k = k' := by
  have hb := (tma_outBars ht hg he hσ hs).1
  have hb' := (tma_outBars ht hg he' hσ' hs').1
  have key : ∀ {k k' : Nat} {pc a : Nat} {sp : TensorStore.Spec} {c' : Consumer.D},
      X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ →
      Frame.stateAt (code L) X g k' = some (some (.inr (.cons c'))) → c'.site = .tma s → k < k' →
      k' < (X.tr g).length →
      Consumer.outBars L g ((X.tr g).take k) < Consumer.outBars L g ((X.tr g).take k') := by
    intro k k' pc a sp c' he hσ' hs' hlt hk'
    obtain ⟨h2, ⟨pcb, hbar⟩, ⟨pcf, hfen⟩⟩ := ht.cons_tma_prev hg hk' hσ' hs'
    have hne1 : k ≠ k' - 1 := by
      rintro rfl
      rw [he] at hfen
      cases hfen
    have hne2 : k ≠ k' - 2 := by
      rintro rfl
      rw [he] at hbar
      cases hbar
    have hm1 := countP_take_le (xs := X.tr g) (p := Consumer.isOutBar L g)
      (show k ≤ k' - 2 by omega)
    have hm2 := countP_take_le (xs := X.tr g) (p := Consumer.isOutBar L g)
      (show k' - 2 + 1 ≤ k' by omega)
    have hstep : ((X.tr g).take (k' - 2 + 1)).countP (Consumer.isOutBar L g) =
        ((X.tr g).take (k' - 2)).countP (Consumer.isOutBar L g) + 1 := by
      have hbar' : (X.tr g)[k' - 2]? = some ⟨pcb, .bar (Consumer.outId L g) (some 128)⟩ := hbar
      rw [List.take_add_one, hbar', Option.toList_some, List.countP_append]
      simp [Consumer.isOutBar]
    unfold Consumer.outBars
    omega
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := key he hσ' hs' h (len_of_get he')
    omega
  · exact h
  · have := key he' hσ hs h (len_of_get he)
    omega

/-- **Distinct tensor stores write distinct output bytes.** -/
theorem outputUnique (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) : OutputUnique X := by
  intro i j a a' s s' x y z x' y' z' l hi hj hl hl'
  have hblock := hpre.block
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := j
  obtain ⟨pci, hei⟩ := hi
  obtain ⟨pcj, hej⟩ := hj
  have hg := Frame.lt_of_get hX hei
  have hg' := Frame.lt_of_get hX hej
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hei (by simp)
  obtain ⟨c, rfl⟩ := (ht.access_region hg hei hσ).2.2 a s rfl
  obtain ⟨d', hσ'⟩ := Frame.event_state ht.sound hX ht.tracked hej (by simp)
  obtain ⟨c', rfl⟩ := (ht.access_region hg' hej hσ').2.2 a' s' rfl
  obtain ⟨s0, hs0, hf0, hm0, hn0, hx0, hy0, hz0, hl0, htile⟩ := store_loc hpre ht hg hei hσ hl
  obtain ⟨s1, hs1, hf1, hm1, hn1, hx1, hy1, hz1, hl1, htile'⟩ := store_loc hpre ht hg' hej hσ' hl'
  -- the byte fixes the tile, the CTA rank, the warp group, the slice and the slot
  have ha := congrArg Loc.addr (hl0.symm.trans hl1)
  simp only [elementLoc, Loc.at, outputRow, outputCol] at ha
  have hs0l := s0.isLt
  have hs1l := s1.isLt
  have hr0 : g / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hr1 : g' / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hq0 : Consumer.tidOf L g / 32 / 4 < 2 := by
    have := ht.role_warp hg (len_of_get hei).le hσ
    simp only [roleWarp] at this
    show g % L.block / 32 / 4 < 2
    omega
  have hq1 : Consumer.tidOf L g' / 32 / 4 < 2 := by
    have := ht.role_warp hg' (len_of_get hej).le hσ'
    simp only [roleWarp] at this
    show g' % L.block / 32 / 4 < 2
    omega
  have hcol : 256 * c.n + 32 * s0.val + x = 256 * c'.n + 32 * s1.val + x' ∧ z = z' ∧
      512 * c.m + 256 * (g / L.block % 2) + 128 * (Consumer.tidOf L g / 32 / 4) + y =
        512 * c'.m + 256 * (g' / L.block % 2) + 128 * (Consumer.tidOf L g' / 32 / 4) + y' := by
    omega
  obtain ⟨hcol, rfl, hrow⟩ := hcol
  obtain ⟨hm, hr, hq, rfl⟩ := outputRow_injective hr0 hq0 hy0 hr1 hq1 hy1
    (by simp only [outputRow]; omega)
  obtain ⟨hn, hs, rfl⟩ := outputCol_injective hs0l hx0 hs1l hx1 (by simp only [outputCol]; omega)
  have hs01 : s0 = s1 := Fin.ext hs
  subst hs01
  -- the tile fixes the cluster task, hence the cluster and the task's number
  obtain ⟨t, htl, htt, hcase⟩ := tile_task hpre hX ht hv hg (len_of_get hei).le htile
  obtain ⟨t', htl', htt', hcase'⟩ := tile_task hpre hX ht hv hg' (len_of_get hej).le htile'
  have htt0 : t = t' := tileOf_inj htl htl' (by rw [← htt, ← htt', hm, hn])
  subst htt0
  have hlaunch : ∀ {h : Nat} {i : EvId} {s : Clc.Spec} {tg : List Nat}, h < L.threads →
      X.tr h ≠ [] → X.ClcIssue i s tg → h / L.block / 2 = t →
      X.clcState.response (Clc.requestId i) = some (some t) → False := by
    intro h i s tg hh hne hi hct hres
    have hown := hX.clc.2.2.2.2 ⟨i, s, tg, hi⟩ h hh hne
    simp only [clusterOfCta_eq hpre] at hown
    rw [hct] at hown
    exact (owned hX).response_not_launched hres hown
  have hne : ∀ {h kk : Nat} {e : Event}, X.get (h, kk) = some e → X.tr h ≠ [] := by
    intro h kk e he hn
    have := len_of_get he
    simp only [hn, List.length_nil] at this
    omega
  have hcl : g / L.block / 2 = g' / L.block / 2 ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) - 1 =
        okPolls (Bar.loc L (g' / L.block) ⟨.clc, 0, true⟩) ((X.tr g').take k') - 1 := by
    rcases hcase with ⟨hE, hct⟩ | ⟨hE, i1, t1, tg1, hi1, hic1, hcnt1, hres1⟩ <;>
      rcases hcase' with ⟨hE', hct'⟩ | ⟨hE', i2, t2, tg2, hi2, hic2, hcnt2, hres2⟩
    · exact ⟨hct.symm.trans hct', hE.trans hE'.symm⟩
    · exact (hlaunch hg (hne hei) hi2 hct.symm hres2).elim
    · exact (hlaunch hg' (hne hej) hi1 hct'.symm hres1).elim
    · have hreq := (owned hX).response_inj hres1 hres2
      simp only [Clc.requestId, Nat.pair_eq_pair] at hreq
      obtain ⟨hi12, hk12⟩ := hreq
      have hcc : g / L.block / 2 = g' / L.block / 2 := by
        rw [hi12] at hic1
        omega
      refine ⟨hcc, ?_⟩
      rw [hcc, hi12, hk12] at hcnt1
      omega
  obtain ⟨hcc, hE⟩ := hcl
  -- the thread: the CTA of the cluster by its rank, the group's first thread
  have hgg : g = g' := by
    have hcta : g / L.block = g' / L.block := by omega
    simp only [Consumer.first, decide_eq_true_eq, Nat.or_eq_zero_iff] at hf0 hf1
    have h1 := Nat.div_add_mod g L.block
    have h2 := Nat.div_add_mod g' L.block
    simp only [Consumer.tidOf] at hq hf0 hf1
    rw [hcta] at h1
    omega
  subst hgg
  obtain ⟨hb, hb1⟩ := tma_outBars ht hg hei hσ hs0
  obtain ⟨hb', hb1'⟩ := tma_outBars ht hg hej hσ' hs1
  have hkk := tma_inj ht hg hei hej hσ hσ' hs0 hs1 (by omega)
  subst hkk
  exact ⟨rfl, rfl, rfl, rfl⟩

end ClcRing

end

end PTX.Kernels.Fp16Gemm8192.Proof
