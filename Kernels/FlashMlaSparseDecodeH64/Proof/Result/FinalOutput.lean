-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputCoverage
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputPayload
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Post
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0LseTrace

public section

/-! # The final output bytes are the bytes of the actual tile writes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel's two-dimensional batch/query coordinates identify a launched CTA. -/
private theorem ctaOf_row (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    ctaOf L g = eOf L g * P.s_q + qOf L g := by
  have hg' := NamedBar.cta_lt hg
  change ctaOf L g < L.grid at hg'
  rw [hpre.grid] at hg'
  have hb : ctaOf L g / P.s_q < P.b :=
    (Nat.div_lt_iff_lt_mul hpre.sqPos).2 (by rwa [Nat.mul_comm])
  change ctaOf L g = Wg1Mma.batchOf L g * P.s_q + Wg1Mma.queryOf L g
  rw [Wg1Mma.batchOf_eq hpre, Wg1Mma.queryOf_eq hpre]
  change ctaOf L g = (ctaOf L g / P.s_q % P.b) * P.s_q + ctaOf L g % P.s_q
  rw [Nat.mod_eq_of_lt hb, Nat.mul_comm]
  exact (Nat.div_add_mod (ctaOf L g) P.s_q).symm

private theorem covers_one {a : Acc} {l : Loc} (hs : a.size = 1) (hc : a.Covers l) :
    a.loc = l := by
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hc
  rw [hs] at hhi
  have ha : a.loc.addr = l.addr := by omega
  cases hloc : a.loc with
  | mk s c n =>
    cases l with
    | mk s' c' n' =>
      rw [hloc] at hsp hcta ha
      cases hsp
      cases hcta
      cases ha
      rfl

private theorem column_split {j j' : Fin 4} {w w' x x' : Nat} (hw : w < 2) (hw' : w' < 2)
    (hx : x < 64) (hx' : x' < 64) (h : tmaX j.val w + x = tmaX j'.val w' + x') :
    j = j' ∧ w = w' ∧ x = x' := by
  have he : outputColumn (j, ⟨w, hw⟩, ⟨x, hx⟩) = outputColumn (j', ⟨w', hw'⟩, ⟨x', hx'⟩) :=
    Fin.ext h
  obtain ⟨hj, h⟩ := Prod.mk.inj (outputColumn_bijective.1 he)
  obtain ⟨hwarp, hx⟩ := Prod.mk.inj h
  exact ⟨hj, congrArg Fin.val hwarp, congrArg Fin.val hx⟩

variable (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hs hX ht

/-- A byte of an output tile is reserved by at most one asynchronous store slot. -/
theorem output_destination_unique {i i' : EvId} {addr addr' x y k x' y' k' : Nat}
    {s s' : TensorStore.Spec} {l : Loc} (hi : X.TensorStoreIssue i addr s)
    (hi' : X.TensorStoreIssue i' addr' s') (hc : TensorStore.writeLoc s x y k = some l)
    (hc' : TensorStore.writeLoc s' x' y' k' = some l) :
    i = i' ∧ x = x' ∧ y = y' ∧ k = k' := by
  obtain ⟨d, j, hd, hj, hw, hx, hy, hk, hl⟩ := output_destination hpre hs hX ht hi hc
  obtain ⟨d', j', hd', hj', hw', hx', hy', hk', hl'⟩ := output_destination hpre hs hX ht hi' hc'
  have hsame := hl.symm.trans hl'
  obtain ⟨_, he⟩ := hi
  obtain ⟨_, he'⟩ := hi'
  have hg := Frame.lt_of_get hX he
  have hg' := Frame.lt_of_get hX he'
  obtain ⟨heq, hq, hh, hcol, hbyte⟩ :=
    outputByte_injective (Wg1Mma.queryOf_lt hpre hg) (Wg1Mma.queryOf_lt hpre hg')
      hy hy' (outputColumn_lt j hw hx) (outputColumn_lt j' hw' hx') hk hk' hsame
  obtain ⟨rfl, hwarp, hxx⟩ := column_split hw hw' hx hx' hcol
  have hcta : ctaOf L i.1 = ctaOf L i'.1 := by
    change qOf L i.1 = qOf L i'.1 at hq
    rw [ctaOf_row hpre hg, ctaOf_row hpre hg', heq, hq]
  have hiSame := Wg0OutputCoverage.tileUnique hpre hX (fun _ hg => (hs _ hg).machine)
    he he' hcta hwarp hd hd' hj hj'
  exact ⟨hiSame, hxx, hh, hbyte⟩

/-- A byte of an output tile has at most one performed asynchronous write stage. -/
theorem output_writer_unique {i i' : EvId} {x y k x' y' k' : Nat} {a a' : Acc} {bs bs' : List Byte}
    {l : Loc} (hm : X.MemWrites (.async i (.write (.store x y k))) a bs)
    (hm' : X.MemWrites (.async i' (.write (.store x' y' k'))) a' bs') (hc : a.Covers l)
    (hc' : a'.Covers l) :
    i = i' ∧ x = x' ∧ y = y' ∧ k = k' := by
  obtain ⟨_, _, _, _, hi, hLoc, _, hSize, _⟩ := hm
  obtain ⟨_, _, _, _, hi', hLoc', _, hSize', _⟩ := hm'
  exact output_destination_unique hpre hs hX ht hi hi'
    (by rwa [covers_one hSize hc] at hLoc) (by rwa [covers_one hSize' hc'] at hLoc')

/-- Any performed tensor store byte is the final byte at its destination. -/
theorem output_final_of_write {m : FinalMem} (hm : IsFinal L mem0 X m) {i : EvId} {x y k : Nat}
    {a : Acc} {bs : List Byte} (hw : X.MemWrites (.async i (.write (.store x y k))) a bs) :
    m a.loc = some bs[0]? := by
  obtain ⟨_, j, _, _, hwarp, hx, hy, hk, hsize, hloc⟩ := output_writer hpre hs hX ht hw
  have hsizes : a.Covers a.loc :=
    ⟨rfl, rfl, le_rfl, by rw [hsize]; omega⟩
  have hspace : a.loc.space = .global := by rw [hloc]; rfl
  have hissue := hw
  obtain ⟨_, _, _, _, hi, _⟩ := hissue
  obtain ⟨_, he⟩ := hi
  have hgi := Frame.lt_of_get hX he
  have houtr := outputRange (e := eOf L i.1) (q := qOf L i.1) (l := a.loc)
    (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hgi)
    hy (outputColumn_lt j hwarp hx) hk (by
      change a.loc.InRange a.size a.loc at hsizes
      rw [← hloc, ← hsize]
      exact hsizes)
  obtain ⟨co, _, hfin⟩ := hm
  have hfinal := (hfin a.loc).1 (.async i (.write (.store x y k))) a bs hw hsizes
  rw [hfinal ?_]
  · simp [wbyte]
  · intro w a' bs' hw' hc'
    have hspace' : a'.loc.space = .global := hc'.1.symm.trans hspace
    cases w with
    | thread i' =>
      rcases hw' with he' | ⟨_, hr⟩
      · obtain ⟨_, _, _, hl', hsz', _⟩ := GlobalWrites.lse_write hpre hs hX ht he' hspace'
        have hg' := Frame.lt_of_get hX (Exists.choose_spec he')
        change a'.loc.InRange a'.size a.loc at hc'
        rw [hl', hsz'] at hc'
        have hlsr := lseRange (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg')
          (head_lt L i'.1) hc'
        rcases hpre.outApartLse with hapart | hapart <;> omega
      · exact (GlobalWrites.no_rmw hX hr).elim
    | async i' part =>
      cases part <;> try contradiction
      case writeCopy =>
        obtain ⟨_, hcopy, _⟩ := hw'
        exact (GlobalWrites.no_copy hX hcopy).elim
      case writeElem =>
        obtain ⟨_, hcopy, _⟩ := hw'
        exact (GlobalWrites.no_copy hX hcopy).elim
      case writeCta =>
        obtain ⟨_, _, hclc, _⟩ := hw'
        exact (GlobalWrites.no_clc hX hclc).elim
      case writeLoad => exact Space.noConfusion ((tensorLoad_shared hX hw').symm.trans hspace')
      case writeStore =>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := output_writer_unique hpre hs hX ht hw hw' hsizes hc'
        exact .inl rfl

/-- A final O byte is the normalized value of its actual Tensor Memory word at the indicated
logical query, head and column. -/
theorem complete_output_payload (hd : Complete L X) {g : Nat} (hg : g < L.threads) {m : FinalMem}
    (hm : IsFinal L mem0 X m) (h : Fin 64) (column : Fin 512) (byte : Fin 2) :
    let l := (oLoc P (eOf L g) (qOf L g) h.val column.val).at byte.val
    ∃ (w i : Nat) (d : D) (tile : Fin 4) (sub : Fin 64) (e : Event) (words : List Value),
      ctaOf L w = ctaOf L g ∧ head L w = h.val ∧
      tmaX tile.val (half L w) + sub.val = column.val ∧
      Frame.stateAt (Machine.code P L) X w i = some (some (.wg0 d)) ∧ d.site = .oLoad tile ∧
      X.get (w, i) = some e ∧ e.kind = .tc (.ld (64 * tile.val) words .s32x32b) ∧
      words.length = 64 ∧
      m l = some (some (.float .bf16 (oScale P L w d * outputReal words sub.val), byte.val)) := by
  have hSound (i : Nat) (hi : i < L.threads) := (hs i hi).machine
  obtain ⟨issuer, i, d, tile, address, sp, s, out, hi, hst, hsite, hhead, hbyte,
      hcta, hcolumn, _, hwrite⟩ := Protocol.OutputCoverage.byteWritten hpre hX hd hSound ht hg
        h column byte
  obtain ⟨w, j, dw, e, words, hwCta, hwHead, hwHalf, hwState, hwSite, hwEvent,
      hwKind, hwLength, hval⟩ := OutputPayload.of_write hpre hX hd hs ht
        hi hst hsite s hwrite
  have hfinal := output_final_of_write hpre hs hX ht hm hwrite
  exact ⟨w, j, dw, tile, s.1, e, words, hwCta.trans hcta, hhead ▸ hwHead,
    hwHalf.symm ▸ hcolumn, hwState, hwSite, hwEvent, hwKind, hwLength,
    by
      rw [hfinal, hval, hbyte]
      rfl⟩

omit hpre hs hX ht in
private theorem lse_thread_row (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) (hw : warpOf L g < 2) :
    (lseLocOf P L g).addr = P.lseBase + 4 * (ctaOf L g * 64 + g % 384) ∧ g % 384 < 64 := by
  have ht : g % 384 < 64 := by
    change tidOf L g / 32 < 2 at hw
    rw [tidOf_eq hpre] at hw
    omega
  have hh : head L g = g % 384 := by
    unfold head
    rw [tidOf_eq hpre, Nat.mod_eq_of_lt ht]
  exact ⟨by simp only [lseLocOf, lseLoc, ← ctaOf_row hpre hg, hh], ht⟩

/-- Two ordinary writes covering one LSE byte are the same event. -/
theorem lse_writer_unique {i i' : EvId} {a a' : Acc} {bs bs' : List Byte} {l : Loc}
    (hl : l.space = .global) (hw : X.Writes i a bs) (hw' : X.Writes i' a' bs') (hc : a.Covers l)
    (hc' : a'.Covers l) :
    i = i' := by
  obtain ⟨d, hd, hsite, ha, ha_sz, _⟩ :=
    GlobalWrites.lse_write hpre hs hX ht hw (hc.1.symm.trans hl)
  obtain ⟨d', hd', hsite', ha', ha_sz', _⟩ :=
    GlobalWrites.lse_write hpre hs hX ht hw' (hc'.1.symm.trans hl)
  have hget := Exists.choose_spec hw
  have hget' := Exists.choose_spec hw'
  have hg := Frame.lt_of_get hX hget
  have hg' := Frame.lt_of_get hX hget'
  obtain ⟨haddr, htid⟩ := lse_thread_row hpre hg (Wg0LseTrace.writer_warp hX hs hg hd hsite)
  obtain ⟨haddr', htid'⟩ :=
    lse_thread_row hpre hg' (Wg0LseTrace.writer_warp hX hs hg' hd' hsite')
  have hlo := hc.2.2.1
  have hhi := hc.2.2.2
  have hlo' := hc'.2.2.1
  have hhi' := hc'.2.2.2
  rw [ha, haddr] at hlo hhi
  rw [ha', haddr'] at hlo' hhi'
  rw [ha_sz] at hhi
  rw [ha_sz'] at hhi'
  have hthread : i.1 = i'.1 := by
    simp only [ctaOf, hpre.block] at hlo hhi hlo' hhi'
    have hdiv := Nat.div_add_mod i.1 384
    have hdiv' := Nat.div_add_mod i'.1 384
    omega
  obtain ⟨g, k⟩ := i
  obtain ⟨g', j⟩ := i'
  change g = g' at hthread
  subst g'
  have hk : k < (X.tr g).length := List.getElem?_eq_some_iff.mp hget |>.choose
  have hj : j < (X.tr g).length := List.getElem?_eq_some_iff.mp hget' |>.choose
  rw [Wg0LseTrace.store_unique hX hs hg hk hj hd hd' hsite hsite']

/-- An actual global LSE write supplies the final bytes of its row. -/
theorem lse_final_of_write {m : FinalMem} (hm : IsFinal L mem0 X m) {i : EvId} {a : Acc}
    {bs : List Byte} {l : Loc} (hw : X.Writes i a bs) (hc : a.Covers l) (hsp : l.space = .global) :
    m l = some (wbyte a bs l) := by
  obtain ⟨_, _, _, ha, hsz, _⟩ := GlobalWrites.lse_write hpre hs hX ht hw (hc.1.symm.trans hsp)
  have hg := Frame.lt_of_get hX (Exists.choose_spec hw)
  have hlse := lseRange (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg) (head_lt L i.1) (by
    change a.loc.InRange a.size l at hc
    rwa [ha, hsz] at hc)
  obtain ⟨_, _, hfin⟩ := hm
  apply (hfin l).1 (.thread i) a bs (.inl hw) hc
  intro w a' bs' hw' hc'
  cases w with
  | thread j =>
    rcases hw' with hwrite | ⟨_, hRmw⟩
    · exact .inl
        (congrArg AsyncCopy.Ref.thread (lse_writer_unique hpre hs hX ht hsp hwrite hw hc' hc))
    · exact (GlobalWrites.no_rmw hX hRmw).elim
  | async j part =>
    cases part <;> try contradiction
    case writeCopy =>
      obtain ⟨_, hcopy, _⟩ := hw'
      exact (GlobalWrites.no_copy hX hcopy).elim
    case writeElem =>
      obtain ⟨_, hcopy, _⟩ := hw'
      exact (GlobalWrites.no_copy hX hcopy).elim
    case writeCta =>
      obtain ⟨_, _, hclc, _⟩ := hw'
      exact (GlobalWrites.no_clc hX hclc).elim
    case writeLoad =>
      exact Space.noConfusion ((tensorLoad_shared hX hw').symm.trans (hc'.1.symm.trans hsp))
    case writeStore =>
      obtain ⟨_, tile, _, _, hwg, hx, hy, hk, hsize, hloc⟩ := output_writer hpre hs hX ht hw'
      obtain ⟨_, _, _, _, ⟨_, he⟩, _⟩ := hw'
      have hg' := Frame.lt_of_get hX he
      change a'.loc.InRange a'.size l at hc'
      rw [hloc, hsize] at hc'
      have ho := outputRange (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg') hy
        (outputColumn_lt tile hwg hx) hk hc'
      rcases hpre.outApartLse with hapart | hapart <;> omega

/-- Every LSE row of a complete followed trace has its actual LSE register in final memory. -/
theorem complete_lse_byte (hd : Complete L X) {g : Nat} (hg : g < L.threads) {m : FinalMem}
    (hm : IsFinal L mem0 X m) (headIndex : Fin 64) (byte : Fin 4) :
    let l := (lseLoc P (eOf L g) (qOf L g) headIndex.val).at byte.val
    ∃ j i d a, Frame.stateAt (Machine.code P L) X j i = some (some (.wg0 d)) ∧
      d.site = .lseStore ∧ X.Writes (j, i) a (lseReg d).toBytes ∧
      a.loc = lseLoc P (eOf L g) (qOf L g) headIndex.val ∧
      ctaOf L j = ctaOf L g ∧ head L j = headIndex.val ∧
      m l = some (lseReg d).toBytes[byte.val]? := by
  let j := ctaOf L g * 384 + headIndex.val
  have hh : headIndex.val < 64 := headIndex.isLt
  have hcta : ctaOf L j = ctaOf L g := by
    change (ctaOf L g * 384 + headIndex.val) / L.block = ctaOf L g
    rw [hpre.block]
    omega
  have hj : j < L.threads := by
    have h := NamedBar.cta_lt hg
    change ctaOf L g < L.grid at h
    change ctaOf L g * 384 + headIndex.val < L.grid * L.block
    rw [hpre.block]
    omega
  have htid : tidOf L j = headIndex.val := by
    rw [tidOf_eq hpre]
    change (ctaOf L g * 384 + headIndex.val) % 384 = headIndex.val
    omega
  have hwarp : warpOf L j < 2 := by
    change tidOf L j / 32 < 2
    rw [htid]
    omega
  obtain ⟨i, d, a, hst, hsite, hwrite, haloc, hasize⟩ :=
    Wg0LseTrace.complete_lse_write hpre hX hd hs ht hj hwarp
  have hhead : head L j = headIndex.val := by
    unfold head
    rw [htid, Nat.mod_eq_of_lt hh]
  have heq : a.loc = lseLoc P (eOf L g) (qOf L g) headIndex.val := by
    rw [haloc, lseLocOf, hhead]
    change lseLoc P (Wg1Mma.batchOf L j) (Wg1Mma.queryOf L j) headIndex.val = _
    change _ = lseLoc P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) headIndex.val
    change j / L.block = g / L.block at hcta
    simp only [Wg1Mma.batchOf_eq hpre, Wg1Mma.queryOf_eq hpre, hcta]
  have hc : a.Covers (a.loc.at byte.val) := by
    have hb := byte.isLt
    exact ⟨rfl, rfl, Nat.le_add_right _ _, by change _ + byte.val < _; omega⟩
  have hfinal := lse_final_of_write hpre hs hX ht hm hwrite hc (by rw [heq]; rfl)
  exact ⟨j, i, d, a, hst, hsite, hwrite, heq, hcta, hhead, by
    rw [← heq]
    simpa [wbyte, Loc.at] using hfinal⟩

omit hpre hs hX ht in
private theorem thread_for_output (hpre : Pre P L mem0) {e q : Nat}
    (he : e < P.b) (hq : q < P.s_q) :
    ∃ g < L.threads, eOf L g = e ∧ qOf L g = q := by
  let cta := e * P.s_q + q
  let g := cta * L.block
  have hblk : 0 < L.block := by rw [hpre.block]; decide
  have hcta : cta < L.grid := by
    have hstep : (e + 1) * P.s_q ≤ P.b * P.s_q :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    rw [hpre.grid, Nat.mul_comm P.s_q P.b]
    dsimp [cta]
    omega
  have hdiv : g / L.block = cta := Nat.mul_div_cancel _ hblk
  have hbatch : cta / P.s_q = e := by
    change (e * P.s_q + q) / P.s_q = e
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpre.sqPos, Nat.div_eq_of_lt hq, Nat.zero_add]
  have hquery : cta % P.s_q = q := by
    change (e * P.s_q + q) % P.s_q = q
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  refine ⟨g, Nat.mul_lt_mul_of_pos_right hcta hblk, ?_, ?_⟩
  · change Wg1Mma.batchOf L g = e
    rw [Wg1Mma.batchOf_eq hpre, hdiv, hbatch, Nat.mod_eq_of_lt he]
  · change Wg1Mma.queryOf L g = q
    rw [Wg1Mma.queryOf_eq hpre, hdiv, hquery]

/-- The result proof reduces to the values of actual epilogue loads and LSE stores. -/
theorem post_of_complete_payloads (hd : Complete L X) {m : FinalMem} (hm : IsFinal L mem0 X m)
    (hout : ∀ w i d (tile : Fin 4) (sub : Fin 64) event words,
      Frame.stateAt (Machine.code P L) X w i = some (some (.wg0 d)) →
      d.site = .oLoad tile → X.get (w, i) = some event →
      event.kind = .tc (.ld (64 * tile.val) words .s32x32b) →
      oScale P L w d * outputReal words sub.val =
        attn P (eOf L w) (qOf L w) (head L w) (tmaX tile.val (half L w) + sub.val))
    (hlse : ∀ w i d a, Frame.stateAt (Machine.code P L) X w i = some (some (.wg0 d)) →
      d.site = .lseStore → X.Writes (w, i) a (lseReg d).toBytes → ∀ k : Fin 4,
      (lseReg d).toBytes[k.val]? =
        some (if rowSum P (eOf L w) (qOf L w) (head L w) = 0 then infByte k.val
          else (Value.float .f32 (lse P (eOf L w) (qOf L w) (head L w))).byteAt k.val)) :
    Post P mem0 m := by
  have hrow (e q h : Nat) (he : e < P.b) (hq : q < P.s_q) (hh : h < 64) (k : Fin 4) :
      m ((lseLoc P e q h).at k.val) =
        some (some (if rowSum P e q h = 0 then infByte k.val
          else (Value.float .f32 (lse P e q h)).byteAt k.val)) := by
    obtain ⟨g, hg, heg, hqg⟩ := thread_for_output hpre he hq
    obtain ⟨w, i, d, a, hst, hsite, hw, _, hcta, hhead, hf⟩ :=
      complete_lse_byte hpre hs hX ht hd hg hm ⟨h, hh⟩ k
    have hew : eOf L w = e := (by simp only [eOf, ctaidY, hcta] : eOf L w = eOf L g).trans heg
    have hqw : qOf L w = q := (by simp only [qOf, ctaidX, hcta] : qOf L w = qOf L g).trans hqg
    rw [heg, hqg, hlse w i d a hst hsite hw k, hew, hqw, hhead] at hf
    exact hf
  apply post_of_bytes
  refine ⟨?_, ?_, ?_, fun _ => global_frame hpre hs hX ht hm⟩
  · intro e he q hq h hh col hcol k hk
    obtain ⟨g, hg, heg, hqg⟩ := thread_for_output hpre he hq
    obtain ⟨w, i, d, tile, sub, event, words, hcta, hhead, hcolumn,
      hstate, hsite, hevent, hkind, _, hfinal⟩ :=
      complete_output_payload hpre hs hX ht hd hg hm ⟨h, hh⟩ ⟨col, hcol⟩ ⟨k, hk⟩
    have hew : eOf L w = e := (by simp only [eOf, ctaidY, hcta] : eOf L w = eOf L g).trans heg
    have hqw : qOf L w = q := (by simp only [qOf, ctaidX, hcta] : qOf L w = qOf L g).trans hqg
    rw [heg, hqg, hout w i d tile sub event words hstate hsite hevent hkind,
      hew, hqw, hhead, hcolumn] at hfinal
    exact hfinal
  · intro e he q hq h hh hn k hk
    simpa only [ite_eq_right hn] using hrow e q h he hq hh ⟨k, hk⟩
  · intro e he q hq h hh hz k hk
    simpa only [ite_eq_left hz] using hrow e q h he hq hh ⟨k, hk⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
