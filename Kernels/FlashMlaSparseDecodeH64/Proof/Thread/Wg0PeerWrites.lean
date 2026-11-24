-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPvWait

public section

/-! # Actual shared writes in the peer exchange window -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeerWrites

open PTX PTX.Flow PTX.Proof StageWriteClasses MachineTracking


variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At a followed ordinary write, the role determines its part of the exchange window. -/
theorem ordinary_at_followed {i : EvId} {a : Acc} {bs : List Byte} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {q : Machine.ThreadD} (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some q))
    (hw : X.Writes i a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 204800 ≤ l.addr) (hhi : l.addr < L.sharedBase + 221184) :
    a.loc.cta = ctaOf L i.1 ∧ ∃ d : Wg0.D,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      Wg0.Inv P L i.1 d ∧
      ((∃ j : Fin 8, d.site = .exchStore j ∧ a.size = 16 ∧
        a.loc = Wg0.shLoc L i.1 (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L i.1 ^^^ 2) +
          16 * laneOf L i.1 + Wg0.exchangeChunk * j.val)) ∨
        (∃ k : Fin 4, d.site = .pStore k)) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have haSpace : a.loc.space = .shared := hcover.1.symm.trans hshared
  have haLow : a.loc.addr ≤ l.addr := hcover.2.2.1
  have haHigh : l.addr < a.loc.addr + a.size := hcover.2.2.2
  have excludeLow {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : fp.loc.addr + fp.size ≤ L.sharedBase + 204800) : False := by
    rw [(Kind.wr.inj hk).1] at haHigh
    omega
  have excludeHigh {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : L.sharedBase + 221184 ≤ fp.loc.addr) : False := by
    rw [(Kind.wr.inj hk).1] at haLow
    omega
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX he hd
  have hrole := StageWriteClasses.of_write hX hs hw hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    cases q with
    | wg0 d =>
      simp only [writeRole] at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg0.Inv P L i.1 d := hinv
      cases hrole with
      | stage j k =>
        change kernel.code[d.site.pc]? = some ins at hcode
        rw [hsite] at hcode
        obtain rfl := Option.some.inj (hcode.symm.trans (Wg0.stage_code j k))
        rw [Wg0.event_oStage hpre hg hat hv hsite] at hf
        have hshape := congrArg Event.kind hf.1
        have hsub : t.sub < 4 := by
          rw [(show t.sub = d.sub from hat.2.1)]
          simpa only [hsite, Wg0.Site.elems] using hv.subLt
        have hhalf := Wg0.halfLt hv.warpLt
        have hplane := (by decide : ∀ j : Fin 4, Wg0.planeAdd j.val ≤ 5) j
        have hxor := Wg0.xor_lt_eight k.isLt (Nat.mod_lt (tidOf L i.1 % 64) (by decide))
        exact (excludeLow hshape (by
          simp only [Wg0.shLoc, Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes]
          omega)).elim
      | exchange j =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_exchangeStore hpre j hsite hat hv hcode hf
        have heq := (Kind.wr.inj hk).1
        simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
        have hAddr := (congrArg Acc.loc heq).trans hloc.symm
        exact ⟨congrArg Loc.cta hAddr, d, hd, hv, .inl ⟨j, hsite,
          (congrArg Acc.size heq).trans hsize, hAddr⟩⟩
      | probability k =>
        obtain ⟨fp, _, _, _, _, hk, hloc, _, _⟩ := Wg0.fires_pStore hpre hsite hat hv hcode hf
        have heq := (Kind.wr.inj hk).1
        simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
        have hAddr := (congrArg Acc.loc heq).trans hloc.symm
        exact ⟨congrArg Loc.cta hAddr, d, hd, hv, .inr ⟨k, hsite⟩⟩
      | rowMax =>
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_rowMax hpre hsite hat hv hcode hf
        exact (excludeHigh hk (by rw [hloc]; simp only [Wg0.shLoc, Wg0.rowMaxBase]; omega)).elim
      | lseStore0 =>
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore0 hpre hsite hat hv hcode hf
        exact (excludeHigh hk (by rw [hloc]; simp only [Wg0.shLoc, Wg0.rowMaxBase]; omega)).elim
      | lseStore =>
        have hb : Wg0.eOf L i.1 < P.b := Wg1Mma.batchOf_lt hpre hg
        have hq : Wg0.qOf L i.1 < P.s_q := Wg1Mma.queryOf_lt hpre hg
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore hpre hb hq hsite hat hv hcode hf
        rw [(Kind.wr.inj hk).1, hloc, Wg0.lseLocOf_eq] at haSpace
        cases haSpace
    | wg2 d =>
      simp only [writeRole] at hrole
      obtain ⟨r, s, hsite⟩ := hrole
      have hInv : Wg2.Inv P L i.1 d := hinv
      have hFired :
          (Wg2.machine P L i.1).Fired (some (.inr d)) ⟨hw.choose, .wr a bs⟩ (some u) := by
        refine ⟨t, ⟨hat, hinv⟩, ?_⟩
        change Fires t.pc (match kernel.code[d.site.pc]? with
          | some ins' => eventTmpl Assumptions.all L i.1 t ins'.op
          | none => .ub .pcOutOfRange) _ (some u)
        have hpc : t.pc = d.site.pc := hat.1
        change kernel.code[d.site.pc]? = some ins at hcode
        rw [hpc, hcode]
        exact hf
      obtain ⟨fp, hk, hloc, hsize⟩ := Wg2.fired_store_event hpre hsite hFired
      have hfit := hInv.tileFit r.val r.isLt
      have hs := s.isLt
      have hbuf := hInv.bufLt
      exact (excludeLow hk (by
        rw [hloc, hsize]
        simp only [Wg2.numSteps, Wg2.dequantBytes, Wg2.tileOff, Wg2.topkBlock,
          Wg2.tileBase] at hfit ⊢
        omega)).elim
    | index d =>
      simp only [writeRole] at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg1Index.Inv P L i.1 d := hinv
      cases hrole with
      | coordinate extra high =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_extra hpre hsite hv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.coordOff]; omega)).elim
      | validity extra =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_extra hpre hsite hv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.validOff]; omega)).elim
    | prologue d =>
      obtain ⟨w, hthread, hw', halloc⟩ :=
        PrologueAllocation.write_at_allocStore hX hs (w := .thread i) (.inl hw) ⟨d, hd⟩
      obtain rfl := AsyncCopy.Ref.thread.inj hthread
      obtain ⟨hloc, _⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hw' halloc
      rw [hloc] at haLow
      change L.sharedBase + 222752 ≤ l.addr at haLow
      omega
    | head | done | idle _ | mma _ | tma _ => simp [writeRole] at hrole

/-- Only softmax exchange and probability stores can cover the peer exchange window. -/
theorem covered_write {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) (hw : X.MemWrites w a bs) (hcover : a.Covers l)
    (hshared : l.space = .shared) (hlo : L.sharedBase + 204800 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 221184) :
    ∃ (i : EvId) (d : Wg0.D), w = .thread i ∧ X.Writes i a bs ∧
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      Wg0.Inv P L i.1 d ∧
      ((∃ j : Fin 8, d.site = .exchStore j ∧ a.size = 16 ∧
        a.loc = Wg0.shLoc L i.1 (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L i.1 ^^^ 2) +
          16 * laneOf L i.1 + Wg0.exchangeChunk * j.val)) ∨
        (∃ k : Fin 4, d.site = .pStore k)) := by
  rcases Wg2.raw_read_competing_kinds hX hw hcover hshared with
    ⟨i, rfl, hwr⟩ | ⟨i, x, y, b, rfl⟩
  · obtain ⟨d, hd⟩ := Frame.event_state hs hX ht hwr.choose_spec (by simp)
    obtain ⟨_, d, hd, hi, hsite⟩ :=
      ordinary_at_followed hpre hX hs hd hwr hcover hshared hlo hhi
    exact ⟨i, d, rfl, hwr, hd, hi, hsite⟩
  · obtain ⟨_, _, hwindow, _⟩ := TensorSharedBounds.written_byte_windows hpre hX hs ht hw hcover
    rcases hwindow with ⟨_, hh⟩ | ⟨_, hh⟩ <;> omega

/-- Actual writers covering the peer exchange have either the exchange vector's footprint
and its balanced barrier counts, or an even number of warpgroup barriers at a probability
store. This classification also holds past an earlier dismissal of the writer. -/
theorem actual_covered_write {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : X.MemWrites w a bs) (hcover : a.Covers l)
    (hshared : l.space = .shared) (hlo : L.sharedBase + 204800 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 221184) :
    ∃ g i, w = .thread (g, i) ∧ X.Writes (g, i) a bs ∧
      l.cta = ctaOf L g ∧ wgOf L g = 0 ∧ warpOf L g < 4 ∧
      ((∃ j : Fin 8, a.size = 16 ∧
        a.loc = Wg0.shLoc L g (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L g ^^^ 2) +
          16 * laneOf L g + Wg0.exchangeChunk * j.val) ∧
        ((X.tr g).take i).countP (Execution.isBarId 9) =
          2 * ((X.tr g).take i).countP (Execution.isBarId (10 + warpOf L g % 2)) + 1) ∨
        ∃ m, ((X.tr g).take i).countP (Execution.isBarId 9) = 2 * m) := by
  rcases Wg2.raw_read_competing_kinds hX hw hcover hshared with
    ⟨⟨g, i⟩, hRef, hwOrd⟩ | ⟨⟨g, i⟩, x, y, b, hRef⟩
  · have he := hwOrd.choose_spec
    have hg := Frame.lt_of_get hX he
    by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
    · obtain ⟨start, hLe, d, hMask, hZero, hState⟩ :=
        mask_anchor_after_dismissal hpre hX hs he hDismiss
      have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      have hWarp : warpOf L g < 4 := by unfold warpOf wgOf at *; omega
      rcases softmax_actual_write_extent hpre hX hs hWg hState hMask hLe hwOrd with
        ⟨hSpace, _⟩ | ⟨_, _, hEnd, _⟩ | ⟨_, _, _, tag, he', hShape⟩
      · have hSpace' := hcover.1.trans hSpace
        rw [hshared] at hSpace'
        cases hSpace'
      · have hAddr := hcover.2.2.2
        omega
      rcases hShape with ⟨j, hTag, hSize, hLoc⟩ | ⟨j, hTag, hCta, _⟩ | ⟨_, _, hRow⟩
      · refine ⟨g, i, hRef, hwOrd, hcover.2.1.trans (congrArg Loc.cta hLoc), hWg,
          hWarp, .inl ⟨j, hSize, hLoc, ?_⟩⟩
        exact actual_exchange_barrier_counts hpre hX hs he' hLe ⟨d, hMask, hZero, hState⟩ hTag
      · have hCount :=
          actual_probability_barrier_counts hpre hX hs he' hLe ⟨d, hMask, hZero, hState⟩ hTag
        exact ⟨g, i, hRef, hwOrd, hcover.2.1.trans hCta, hWg, hWarp, .inr ⟨_, hCount⟩⟩
      · have hAddr := hcover.2.2.1
        rw [hRow] at hAddr
        simp only [Wg0.shLoc, Wg0.rowMaxBase] at hAddr
        omega
    obtain ⟨q, _, hState, _⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
    obtain ⟨hc, d, hd, hInv, hShape⟩ :=
      ordinary_at_followed (i := (g, i)) hpre hX hs hState hwOrd hcover hshared hlo hhi
    refine ⟨g, i, hRef, hwOrd, hcover.2.1.trans hc, hInv.wg, hInv.warpLt, ?_⟩
    rcases hShape with ⟨j, hSite, hSize, hLoc⟩ | ⟨j, hSite⟩
    · refine .inl ⟨j, hSize, hLoc, ?_⟩
      rw [Wg0BarrierCount.peerCount hpre hX (hs g hg).machine he hd (.inr hSite),
        Wg0PeerTrace.exchangeOrdinal hpre hX (hs g hg).machine he hd hSite]
    · exact .inr ⟨d.block + 1, by
        rw [Wg0BarrierCount.probabilityCount hpre hX (hs g hg).machine he hd hSite]
        omega⟩
  · have hTensor := hRef ▸ hw
    have hExtract := hTensor
    obtain ⟨_, _, _, _, hi, _, _, _, _⟩ := hExtract
    have hFollow := actual_tensor_issue_followed hpre hX hs hi.choose_spec rfl
    obtain ⟨_, _, hwindow, _⟩ :=
      TensorSharedBounds.written_byte_windows_at_followed hpre hX hs hTensor hcover hFollow
    rcases hwindow with ⟨_, hh⟩ | ⟨_, hh⟩ <;> omega

/-- No exchange or probability byte can be written after a followed epilogue state. -/
theorem body_write_before_epilogue {g i j : Nat} {q : Wg0.D} {l : Loc} {a : Acc} {bytes : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : X.Writes (g, i) a bytes) (hCover : a.Covers l)
    (hSpace : l.space = .shared) (hLo : L.sharedBase + 204800 ≤ l.addr)
    (hHi : l.addr < L.sharedBase + 221184)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hEpi : q.site.inEpilogue = true) : i < j := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  obtain ⟨start, hLe, d, hMask, _, hState⟩ :=
    MachineTracking.mask_anchor_after_dismissal hpre hX hs he hDismiss
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  rcases MachineTracking.softmax_actual_write_extent hpre hX hs hWg hState hMask hLe
      ⟨tag, he⟩ with
    ⟨hGlobal, _⟩ | ⟨_, _, hEnd, _⟩ | ⟨_, _, _, wtag, hGet, hShape⟩
  · have h := hCover.1.trans hGlobal
    rw [hSpace] at h
    cases h
  · have h := hCover.2.2.2
    omega
  · apply MachineTracking.body_event_before_followed_epilogue hX hs hq hEpi hGet
    change wtag < 1147
    rcases hShape with ⟨k, hTag, _, _⟩ | ⟨k, hTag, _, _⟩ | ⟨_, _, hRow⟩
    · rw [hTag]
      fin_cases k <;> decide
    · rw [hTag]
      fin_cases k <;> decide
    · have h := hCover.2.2.1
      rw [hRow] at h
      simp only [Wg0.shLoc, Wg0.rowMaxBase] at h
      omega

/-- An actual peer read has its indexed eight-byte footprint in the exchange region. -/
theorem read_geometry {g i : Nat} {d : Wg0.D} {j : Fin 8} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hr : X.Reads (g, i) a bs)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hj : d.site = .peerRead j)
    :
    a.loc = Wg0.shLoc L g (Wg0.exchangeBase + Wg0.exchangeQuad * warpOf L g +
      16 * laneOf L g + Wg0.exchangeChunk * j.val + 8 * d.sub) ∧ a.size = 8 ∧
      Wg0.Inv P L g d ∧ d.sub < 2 := by
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX hr.choose_spec hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    obtain ⟨ac, _, hk, hloc, hz, _⟩ :=
      Wg0.fires_peerRead_at hpre hj hinv hat hcode hf
    have heq := (Kind.rd.inj hk).1
    have hi : Wg0.Inv P L g d := hinv
    simp only [Wg0.siteLoc, hj, Option.some.injEq] at hloc
    refine ⟨(congrArg Acc.loc heq).trans hloc.symm, ?_, hi, ?_⟩
    · rw [heq, hz, hj]
      rfl
    · simpa only [hj, Wg0.Site.elems] using hi.subLt

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0PeerWrites
