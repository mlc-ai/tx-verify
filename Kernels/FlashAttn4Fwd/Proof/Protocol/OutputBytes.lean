-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputStaging
public import Lemmas.TensorStore.SourceBytes

@[expose] public section

/-! # The 32 store lanes write the same bytes

Every lane of the store warp issues the stage's tensor stores: the 32 stores of one instruction
execution have one specification, so they read each slot at one shared
byte `l` of the stage, of one item. That byte's source is one write (`item_source`): the last
write of `l`, in the item, of `l`'s row's correction thread (`rowThread`), which exists because at
its staged arrival of the item the thread has written its whole lines (`OutputFacts.corr_cover`),
and that arrival is what each lane's poll of the item observes (`OutputHandoff`). It is visible to
every store of the item (`publish_vis`), and every other write of `l` is that thread's: of an
earlier item or earlier in the item, before it in program order, or of a later item, after the
stores' reads (`release_vis`); the other proxies do not write staging bytes (`hasync`). So two
stores of one item with one specification read the same byte at a slot and write it
(`item_bytes_eq`): their writes of an element of O are writes of the same bytes with the same value,
which ERR-DATA-RACE does not count as a race (`SameValueWrites`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Output

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- The offset of a staging byte from the first staging byte. -/
def stagingOff (L : Launch) (l : Loc) : Nat := l.addr - (L.sharedBase + 3072)

/-- The row of a staging byte. -/
def rowAt (L : Launch) (l : Loc) : Nat := stagingOff L l % 16384 / 128

/-- The correction thread of row `rowAt l` in the CTA of `l`. -/
def rowThread (L : Launch) (l : Loc) : Nat := l.cta * L.block + (256 + rowAt L l)

theorem rowThread_facts (hpre : Pre P L mem0) {c st : Nat} {l : Loc} (hc : c < L.grid)
    (hl : InStage L c st l) :
    Stats.corrIn L c (rowThread L l) ∧ rowOf L (rowThread L l) = rowAt L l ∧
      lineBase L st (stagingOff L l % 32768 / 16384) (rowAt L l) ≤ l.addr ∧
      l.addr < lineBase L st (stagingOff L l % 32768 / 16384) (rowAt L l) + 128 ∧
      stagingOff L l % 32768 / 16384 < 2 := by
  obtain ⟨-, hlc, h1, h2⟩ := hl
  have hb := hpre.block
  subst hlc
  have h3 : (l.cta + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hc
  unfold rowThread rowOf rowAt stagingOff lineBase Stats.corrIn ctaOf warpOf Launch.threads
  rw [hb] at *
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩

variable (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (hH : OutputHandoff L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k))
include hpre hX ht hH hasync

/-- **The ordered source of a staging byte of an item**: one write of the byte's row thread, the
same for every tensor store of the item that reads the byte. -/
theorem item_source {c st jj : Nat} {l : Loc} (hst : st < 2) (hl : InStage L c st l) {e0 : EvId}
    {s0 : Nat × Nat × Nat} (hr0 : rd L X c st jj e0 s0) :
    ∃ n dst bs, gen L X c st jj (rowThread L l, n) ∧
      X.MemWrites (.thread (rowThread L l, n)) dst bs ∧
      ∀ e x y k pc addr s, rd L X c st jj e (x, y, k) →
      X.get e = some ⟨pc, .tensorStore addr s⟩ → TensorStore.readLoc s x y k = some l →
      SourceOrdered L X (.async e (.read (.store x y k))) l (.thread (rowThread L l, n)) dst
        bs := by
  have hc : c < L.grid := by
    have := hr0.1
    exact this.2.1 ▸ cta_lt this.1
  obtain ⟨hcorr, hrow, hlb1, hlb2, hh2⟩ := rowThread_facts hpre hc hl
  set g := rowThread L l
  set hh := stagingOff L l % 32768 / 16384
  -- the row thread's staged arrival of item `jj`
  obtain ⟨hst0, ⟨pc0, addr0, sp0, hget0, -, -, hpoll0, -⟩, hj0⟩ := hr0
  rw [hst0.2.1, hj0] at hpoll0
  obtain ⟨w0, pcw, par, acq, sc, -, hwget, hwq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := stagedBar L c st) (h := e0.1) (f := e0.2)
      (c := jj) (by omega)
  obtain ⟨x, hx, rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ :=
    (hH c st hst).1 e0.1 w0 pcw par acq sc jj hst0 hwget hwq g hcorr
  -- the last write of `l` in the item
  have accOf : ∀ {e : EvId} {a : Acc} {bs : List Byte}, X.MemWrites (.thread e) a bs →
      X.Access e a true := fun h =>
    h.elim (fun hw => hw.access) (fun ⟨o, hr⟩ => .inr (.inr ⟨o, _, hr⟩))
  let Pw : Nat → Prop := fun i => ∃ a bs, X.MemWrites (.thread (g, i)) a bs ∧ a.Covers l ∧
    arrivals (stagedBar L c st) ((X.tr g).take i) = jj
  have := Classical.decPred Pw
  have hxl := len_of_get hxget
  have hex : ∃ i, i ≤ (X.tr g).length ∧ Pw i := by
    have hcg := hcorr.2.1
    rw [← hcg] at hxget
    obtain ⟨i, a, bs, hix, hw, hcov, harr⟩ :=
      ht.corr_cover hcorr.1 hcorr.2.2.1 hcorr.2.2.2 hst hxget hh hh2 l hl.1
        (by rw [hcg]; exact hl.2.1) (by rw [hrow]; exact hlb1) (by rw [hrow]; exact hlb2)
    rw [hcg, hx] at harr
    exact ⟨i, by simp only at hxl; omega, a, bs, .inl hw, hcov, harr⟩
  obtain ⟨i1, hi1, hpi1⟩ := hex
  set imax := Nat.findGreatest Pw (X.tr g).length
  have hspec : Pw imax := Nat.findGreatest_spec hi1 hpi1
  obtain ⟨dst, bs, hwmax, hcovmax, harrmax⟩ := hspec
  have hacc : X.Access (g, imax) dst true := accOf hwmax
  have hgen : gen L X c st jj (g, imax) := by
    refine ⟨hcorr, ⟨dst, hacc, ?_⟩, harrmax⟩
    obtain ⟨h8, h12, -, st', hst', hcs⟩ :=
      ht.staging_access hcorr.1 hacc hcovmax (by
        obtain ⟨h1, -, h3, h4⟩ := hl
        exact ⟨h1, by omega, by omega⟩)
    obtain ⟨hh', hh2', hline⟩ := hcs.1
    obtain ⟨hl', -⟩ := line_stage hh2' (rowOf_lt L g) hline hcovmax
    have : st' = st := by
      obtain ⟨-, -, h1, h2⟩ := hl
      obtain ⟨-, -, h3, h4⟩ := hl'
      omega
    rw [← this]
    exact hcs
  refine ⟨imax, dst, bs, hgen, hwmax, ?_⟩
  intro e x' y' k' pc addr s hr hget hloc
  have hcov : AsyncCovers X e (.read (.store x' y' k')) l :=
    ⟨⟨l, 1, false, false, .cta, 0, false⟩, false, ⟨rfl, s, addr, ⟨pc, hget⟩, hloc, rfl⟩,
      rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
  refine ⟨hwmax, hcovmax, .direct (publish_vis hH hst hgen hr le_rfl hcov hl), ?_⟩
  intro other fp bs' hmw hfp
  have hstg : InStaging L l := by
    obtain ⟨h1, -, h3, h4⟩ := hl
    exact ⟨h1, by omega, by omega⟩
  cases other with
  | async ip p =>
    obtain ⟨x2, y2, k2, rfl⟩ := hasync ip p fp true l hmw.intent hfp hstg
    exact absurd hmw.intent.1 (by simp [AsyncCopy.Part.writes])
  | thread o =>
    have hoa : X.Access o fp true := accOf hmw
    have ho := access_thread_lt hX hoa
    obtain ⟨h8, h12, -, st', hst', hcs⟩ := ht.staging_access ho hoa hfp hstg
    obtain ⟨hh', hh2', hline⟩ := hcs.1
    obtain ⟨hl', hb1, hb2⟩ := line_stage hh2' (rowOf_lt L o.1) hline hfp
    have hco : ctaOf L o.1 = c ∧ st' = st ∧ rowOf L o.1 = rowAt L l := by
      obtain ⟨-, hc1, h1, h2⟩ := hl
      obtain ⟨-, hc2, h3, h4⟩ := hl'
      refine ⟨hc2.symm.trans hc1, by omega, ?_⟩
      unfold lineBase at hb1 hb2 hlb1 hlb2
      have := rowOf_lt L o.1
      have := rowOf_lt L g
      omega
    obtain ⟨hco1, hss, hρ⟩ := hco
    rw [hss] at hcs
    have hog : o.1 = g := corr_unique hpre (hco1.trans hcorr.2.1.symm) h8 h12 hcorr.2.2.1
      hcorr.2.2.2 (hρ.trans hrow.symm)
    obtain ⟨og, oi⟩ := o
    simp only at hog
    subst hog
    have hgen' : gen L X c st (arrivals (stagedBar L c st) ((X.tr g).take oi)) (g, oi) :=
      ⟨hcorr, ⟨fp, hoa, hcs⟩, rfl⟩
    rcases Nat.lt_trichotomy (arrivals (stagedBar L c st) ((X.tr g).take oi)) jj with
      hlt | heq | hgt
    · have hoi : oi < imax := by
        by_contra hge
        have := arrivals_mono (X := X) (stagedBar L c st) g (Nat.le_of_not_lt hge)
        omega
      exact .inr (.inl (.direct (modelCausality.of_base L
        (.single (.inl (po_of_overlap hoa hacc rfl hoi ⟨l, hfp, hcovmax⟩))))))
    · have hle : oi ≤ imax := Nat.le_findGreatest hoa.lt.le ⟨fp, bs', hmw, hfp, heq⟩
      rcases Nat.lt_or_eq_of_le hle with hoi | hoi
      · exact .inr (.inl (.direct (modelCausality.of_base L
          (.single (.inl (po_of_overlap hoa hacc rfl hoi ⟨l, hfp, hcovmax⟩))))))
      · exact .inl (by rw [hoi])
    · exact .inr (.inr (.direct (release_vis hX hH hst hr hgen' hgt hoa hcov)))

/-- **Two stores of one item with one specification write the same byte at a slot**: their
source reads of the slot read the slot's ordered source write (`item_source`). -/
theorem item_bytes_eq {c st jj : Nat} (hst : st < 2) {i j : EvId} {x y k pc addr : Nat}
    {s : TensorStore.Spec} {o o' : TensorStore.Observation} {b b' : Byte}
    (hri : rd L X c st jj i (x, y, k)) (hrj : rd L X c st jj j (x, y, k))
    (hgi : X.get i = some ⟨pc, .tensorStore addr s⟩)
    (hgj : X.get j = some ⟨pc, .tensorStore addr s⟩) (ho : X.tensorStores i = some o)
    (ho' : X.tensorStores j = some o') (hb : TensorStore.writeByte o x y k = some b)
    (hb' : TensorStore.writeByte o' x y k = some b') : b = b' := by
  have hspec : ∀ {i : EvId} {o : TensorStore.Observation},
      X.get i = some ⟨pc, .tensorStore addr s⟩ → X.tensorStores i = some o → o.spec = s := by
    intro i o hg ho
    obtain ⟨⟨addr', pc', hg'⟩, -⟩ := hX.store i o ho
    rw [hg] at hg'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hg'
    exact hg'.2.2.symm
  have hs := hspec hgi ho
  have hs' := hspec hgj ho'
  have hsrc : StoreSrc L X i.1 i.2 pc s st := by
    obtain ⟨-, ⟨pc1, addr1, s1, hg1, hsrc⟩, -⟩ := hri
    rw [hgi] at hg1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hg1
    obtain ⟨rfl, -, rfl⟩ := hg1
    exact hsrc
  have hred : o.spec.reduce = none := by rw [hs]; exact hsrc.1
  have hred' : o'.spec.reduce = none := by rw [hs']; exact hsrc.1
  obtain ⟨-, l, hl⟩ := TensorStore.writeByte_read (hX.store i o ho).2.2 hred hb
  rw [hs] at hl
  have hli : InStage L c st l := hri.1.2.1 ▸ hsrc.2.1 x y k l hl
  obtain ⟨n, dst, bs, -, -, hw⟩ := item_source hpre hX ht hH hasync hst hli hri
  have hv := hX.store_read_byte ho hred hb (by rw [hs]; exact hl) (hw i x y k pc addr s hri hgi hl)
  have hv' := hX.store_read_byte ho' hred' hb' (by rw [hs']; exact hl)
    (hw j x y k pc addr s hrj hgj hl)
  exact Option.some.inj (hv.trans hv'.symm)

end Output

end
end PTX.Kernels.FlashAttn4Fwd.Proof
