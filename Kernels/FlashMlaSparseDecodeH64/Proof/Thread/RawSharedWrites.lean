-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events

public section

/-! # Ordinary stores leave the raw gather buffers untouched -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RawSharedWrites

open PTX PTX.Flow PTX.Proof StageWriteClasses

theorem ordinary_window_regions_of_state
    {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d))
    (hw : X.Writes i a bs) (hcover : a.Covers l) :
    l.space = .global ∨ (l.space = .shared ∧
      (L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes) ∧
      (((l.addr < L.sharedBase + 131072 ∧ l.cta = ctaOf L i.1 ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧ d.site = .store r s) ∨
    (L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072 ∧ l.cta = ctaOf L i.1 ∧
      ∃ (d : Wg0.D) (tile : Fin 4) (chunk : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
          d.site = .oStage tile chunk) ∨
    L.sharedBase + 204800 ≤ l.addr) ∧
      (l.addr < L.sharedBase + 222752 ∨ Frame.stateAt (Machine.code P L) X i.1 i.2 =
        some (some (.prologue .allocStore))))) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have haLow : a.loc.addr ≤ l.addr := hcover.2.2.1
  have haHigh : l.addr < a.loc.addr + a.size := hcover.2.2.2
  have upper {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : fp.loc.addr + fp.size ≤ L.sharedBase + 131072) : l.addr < L.sharedBase + 131072 := by
    rw [(Kind.wr.inj hk).1] at haHigh
    omega
  have lower {fp : Acc} {bytes : List Byte} {off : Nat} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : L.sharedBase + off ≤ fp.loc.addr) : L.sharedBase + off ≤ l.addr := by
    rw [(Kind.wr.inj hk).1] at haLow
    omega
  have byte_space {fp : Acc} {bytes : List Byte} {sp : Space}
      (hk : Kind.wr a bs = .wr fp bytes) (hSp : fp.loc.space = sp) : l.space = sp :=
    hcover.1.trans (congrArg (fun acc : Acc => acc.loc.space) (Kind.wr.inj hk).1 |>.trans hSp)
  have window {fp : Acc} {bytes : List Byte} {off : Nat} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : fp.loc = ⟨.shared, ctaOf L i.1, L.sharedBase + off⟩)
      (hEnd : off + fp.size ≤ sharedBytes) :
      L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
    rw [(Kind.wr.inj hk).1, haddr] at haLow haHigh
    dsimp only at haLow haHigh
    omega
  have upperWindow {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (hLo : L.sharedBase ≤ fp.loc.addr) (hHi : fp.loc.addr + fp.size ≤ L.sharedBase + 131072) :
      L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
    have hlo := lower (off := 0) hk (by simpa only [Nat.add_zero] using hLo)
    have hhi := upper hk hHi
    dsimp only [sharedBytes]
    omega
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX he hd
  have hrole := StageWriteClasses.of_write hX hs hw hd
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    cases d with
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
        let fp : Acc :=
          { loc := Wg0.shLoc L i.1 (Wg0.stageWrite L i.1 j.val k.val t.sub)
            size := 4, elem := t.sub }
        have hlo : L.sharedBase + 65536 ≤ fp.loc.addr := by
          simp only [fp, Wg0.shLoc, Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes]
          omega
        have hhi : fp.loc.addr + fp.size ≤ L.sharedBase + 131072 := by
          simp only [fp, Wg0.shLoc, Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes]
          omega
        have hcta : l.cta = ctaOf L i.1 := by
          rw [(Kind.wr.inj hshape).1] at hcover
          exact hcover.2.1
        exact .inr ⟨byte_space hshape rfl, upperWindow hshape (Nat.le_trans (by omega) hlo) hhi,
          .inr (.inl ⟨lower hshape hlo, upper hshape hhi, hcta, d, j, k, hd, hsite⟩),
          .inl (by have := upper hshape hhi; omega)⟩
      | exchange j =>
        obtain ⟨fp, hk, hloc, hSize, _⟩ := Wg0.fires_exchangeStore hpre j hsite hat hv hcode hf
        simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
        have hWarp : warpOf L i.1 ^^^ 2 < 4 :=
          Nat.xor_lt_two_pow (n := 2) hv.warpLt (by decide)
        have hLane := hv.laneLt
        have hJ := j.isLt
        refine .inr ⟨byte_space hk (congrArg Loc.space hloc.symm), window hk hloc.symm ?_,
          .inr (.inr (lower hk ?_)), .inl ?_⟩
        · simp only [hSize, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk, sharedBytes]
          omega
        · rw [← hloc]
          simp only [Wg0.shLoc, Wg0.exchangeBase]
          omega
        · rw [(Kind.wr.inj hk).1, ← hloc, hSize] at haHigh
          simp only [Wg0.shLoc, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk] at haHigh
          omega
      | probability k =>
        obtain ⟨fp, _, _, _, _, hk, hloc, hSize, _⟩ := Wg0.fires_pStore hpre hsite hat hv hcode hf
        simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
        have hHalf := Wg0.halfLt hv.warpLt
        have hLane := hv.laneLt
        have hK := k.isLt
        have hSub := hv.subLt
        simp only [hsite, Wg0.Site.elems] at hSub
        refine .inr ⟨byte_space hk (congrArg Loc.space hloc.symm), window hk hloc.symm ?_,
          .inr (.inr (lower hk ?_)), .inl ?_⟩
        · simp only [hSize, Wg0.pTileBase, Wg0.pChunkStride, sharedBytes]
          omega
        · rw [← hloc]
          simp only [Wg0.shLoc, Wg0.pTileBase]
          omega
        · rw [(Kind.wr.inj hk).1, ← hloc, hSize] at haHigh
          simp only [Wg0.shLoc, Wg0.pTileBase, Wg0.pChunkStride] at haHigh
          omega
      | rowMax | lseStore0 =>
        first
        | obtain ⟨fp, hk, hloc, hSize, _⟩ := Wg0.fires_rowMax hpre hsite hat hv hcode hf
        | obtain ⟨fp, hk, hloc, hSize, _⟩ := Wg0.fires_lseStore0 hpre hsite hat hv hcode hf
        refine .inr ⟨byte_space hk (congrArg Loc.space hloc), window hk hloc ?_,
          .inr (.inr (lower hk ?_)), .inl ?_⟩
        · simp only [hSize, Wg0.rowMaxBase, sharedBytes]
          omega
        · rw [hloc]
          simp only [Wg0.shLoc, Wg0.rowMaxBase]
          omega
        · rw [(Kind.wr.inj hk).1, hloc, hSize] at haHigh
          simp only [Wg0.shLoc, Wg0.rowMaxBase] at haHigh
          omega
      | lseStore =>
        have hb : Wg0.eOf L i.1 < P.b := Wg1Mma.batchOf_lt hpre hg
        have hq : Wg0.qOf L i.1 < P.s_q := Wg1Mma.queryOf_lt hpre hg
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore hpre hb hq hsite hat hv hcode hf
        exact .inl (byte_space hk (by rw [hloc, Wg0.lseLocOf_eq]))
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
      have hCta : l.cta = ctaOf L i.1 := by
        have h := hcover.2.1
        rw [(Kind.wr.inj hk).1, hloc] at h
        exact h
      have hLo : L.sharedBase ≤ fp.loc.addr := by
        rw [hloc]
        dsimp only
        omega
      have hHi : fp.loc.addr + fp.size ≤ L.sharedBase + 131072 := by
        rw [hloc, hsize]
        simp only [Wg2.numSteps, Wg2.dequantBytes, Wg2.tileOff, Wg2.topkBlock,
          Wg2.tileBase] at hfit ⊢
        omega
      exact .inr ⟨byte_space hk (congrArg Loc.space hloc), upperWindow hk hLo hHi,
        .inl ⟨upper hk hHi, hCta, d, r, s, hd, hsite⟩,
        .inl (by have := upper hk hHi; omega)⟩
    | index d =>
      simp only [writeRole] at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg1Index.Inv P L i.1 d := hinv
      have hPhase := hv.phase
      have hLane : laneOf L i.1 < 32 := Nat.mod_lt _ (by decide)
      cases hrole with
      | coordinate extra high =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, hSize, _⟩ :=
              Wg1Index.fires_coord_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, hSize, _⟩ :=
              Wg1Index.fires_coord_extra hpre hsite hv hat hcode hf
        all_goals
          have hsub : d.site.sub < 2 := by rw [hsite]; cases high <;> decide
          refine .inr ⟨byte_space hk (congrArg Loc.space hloc),
            window (off := Wg1Index.coordOff L i.1 d.phase + 4 * d.site.sub) hk
              (by simpa only [Nat.add_assoc] using hloc) ?_,
            .inr (.inr (lower hk ?_)), .inl ?_⟩
          · simp only [Wg1Index.coordOff, hSize, sharedBytes]
            omega
          · rw [hloc]
            simp only [Wg1Index.coordOff]
            omega
          · rw [(Kind.wr.inj hk).1, hloc, hSize] at haHigh
            simp only [Wg1Index.coordOff] at haHigh
            omega
      | validity extra =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, hSize, _⟩ :=
              Wg1Index.fires_valid_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, hSize, _⟩ :=
              Wg1Index.fires_valid_extra hpre hsite hv hat hcode hf
        all_goals
          refine .inr ⟨byte_space hk (congrArg Loc.space hloc), window hk hloc ?_,
          .inr (.inr (lower hk ?_)), .inl ?_⟩
          · simp only [Wg1Index.validOff, hSize, sharedBytes]
            omega
          · rw [hloc]
            simp only [Wg1Index.validOff]
            omega
          · rw [(Kind.wr.inj hk).1, hloc, hSize] at haHigh
            simp only [Wg1Index.validOff] at haHigh
            omega
    | prologue d =>
      obtain ⟨w, hthread, hw', halloc⟩ :=
        PrologueAllocation.write_at_allocStore hX hs (w := .thread i) (.inl hw) ⟨d, hd⟩
      obtain rfl := AsyncCopy.Ref.thread.inj hthread
      obtain ⟨hloc, hSize⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hw' halloc
      rw [hloc] at haLow haHigh
      change L.sharedBase + 222752 ≤ l.addr at haLow
      rw [hSize] at haHigh
      change l.addr < L.sharedBase + 222752 + 4 at haHigh
      have hSpace : l.space = .shared := hcover.1.trans (congrArg Loc.space hloc)
      exact .inr ⟨hSpace, ⟨by omega, by dsimp only [sharedBytes]; omega⟩, .inr (.inr (by omega)),
        .inr halloc⟩
    | head | done | idle _ | mma _ | tma _ => simp [writeRole] at hrole

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId} {a : Acc}
    {bs : List Byte} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) (hw : X.Writes i a bs) (hcover : a.Covers l)
include hpre hX hs ht hw hcover

private theorem ordinary_window_regions :
    l.space = .global ∨ (l.space = .shared ∧
      (L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes) ∧
      (((l.addr < L.sharedBase + 131072 ∧ l.cta = ctaOf L i.1 ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧ d.site = .store r s) ∨
    (L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072 ∧ l.cta = ctaOf L i.1 ∧
      ∃ (d : Wg0.D) (tile : Fin 4) (chunk : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
          d.site = .oStage tile chunk) ∨
    L.sharedBase + 204800 ≤ l.addr) ∧
      (l.addr < L.sharedBase + 222752 ∨ Frame.stateAt (Machine.code P L) X i.1 i.2 =
        some (some (.prologue .allocStore))))) := by
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht hw.choose_spec (by simp)
  exact ordinary_window_regions_of_state hpre hX hs hd hw hcover

omit hpre hX hs ht hw hcover in
/-- The raw buffers have no ordinary writer at a followed event. -/
theorem no_ordinary_at_followed {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {a : Acc} {bs : List Byte} {l : Loc} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d))
    (hw : X.Writes i a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 131072 ≤ l.addr) (hhi : l.addr < L.sharedBase + 204800) : False := by
  obtain h | ⟨_, _, h, _⟩ := ordinary_window_regions_of_state hpre hX hs hd hw hcover
  · exact Space.noConfusion (h.symm.trans hshared)
  · rcases h with ⟨h, _⟩ | ⟨_, h, _⟩ | h <;> omega

/-- The shared bytes touched by ordinary writes are in the dequantized tile, output staging,
or the higher protocol storage. The dequantized case identifies the actual role visit. -/
theorem ordinary_regions (hshared : l.space = .shared) :
    (l.addr < L.sharedBase + 131072 ∧ l.cta = ctaOf L i.1 ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧ d.site = .store r s) ∨
    (L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072) ∨
    L.sharedBase + 204800 ≤ l.addr :=
  (((ordinary_window_regions hpre hX hs ht hw hcover).resolve_left
    (fun h => Space.noConfusion (h.symm.trans hshared))).2.2.1).imp_right
      (fun h => h.imp_left (fun h => ⟨h.1, h.2.1⟩))

/-- A shared write below the raw storage comes from a dequantization or staging site.
The state and coordinates are those of the actual event. -/
theorem tile_writer_role (hshared : l.space = .shared) (hhi : l.addr < L.sharedBase + 131072) :
    l.cta = ctaOf L i.1 ∧
      ((∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧ d.site = .store r s) ∨
      (L.sharedBase + 65536 ≤ l.addr ∧
        ∃ (d : Wg0.D) (tile : Fin 4) (chunk : Fin 8),
          Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
            d.site = .oStage tile chunk)) := by
  have hr := ((ordinary_window_regions hpre hX hs ht hw hcover).resolve_left
    (fun h => Space.noConfusion (h.symm.trans hshared))).2.2.1
  rcases hr with ⟨_, hc, h⟩ | ⟨hlo, _, hc, h⟩ | h
  · exact ⟨hc, .inl h⟩
  · exact ⟨hc, .inr ⟨hlo, h⟩⟩
  · omega

/-- An ordinary store covers a global byte or a byte in the launch’s shared window. -/
theorem ordinary_window :
    l.space = .global ∨
      (l.space = .shared ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes) :=
  (ordinary_window_regions hpre hX hs ht hw hcover).imp id (fun h => ⟨h.1, h.2.1⟩)

/-- Only tensor writes can write a byte in the raw buffers of a tracked execution. -/
theorem no_ordinary (hshared : l.space = .shared) (hlo : L.sharedBase + 131072 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 204800) : False := by
  rcases ordinary_regions hpre hX hs ht hw hcover hshared with ⟨h, _⟩ | ⟨_, h⟩ | h <;> omega

/-- The allocator result is the only ordinary write reaching the shared tail. -/
theorem alloc_store_of_cover (hshared : l.space = .shared) (hlo : L.sharedBase + 222752 ≤ l.addr) :
    Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue .allocStore)) := by
  have h := ((ordinary_window_regions hpre hX hs ht hw hcover).resolve_left
    (fun h => Space.noConfusion (h.symm.trans hshared))).2.2.2
  exact h.resolve_left (Nat.not_lt_of_ge hlo)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RawSharedWrites
