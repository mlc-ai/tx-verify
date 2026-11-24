-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RoleSharedWrites
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
import Lemmas.Flow.Final
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

public section

/-! # Ordinary writes that overlap the shared output staging region -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.StageWriteClasses

open PTX PTX.Flow PTX.Proof

private def writeSites : List Nat :=
  [Flow.tmemAlloc_0, Wg0.Site.rowMax.pc, Wg0.Site.lseStore0.pc, Wg0.Site.lseStore.pc] ++
    (List.finRange 8).map (Wg0.Site.exchStore · |>.pc) ++
    (List.finRange 4).map (Wg0.Site.pStore · |>.pc) ++
    (List.finRange 4).flatMap (fun j => (List.finRange 8).map (Wg0.Site.oStage j · |>.pc)) ++
    [Wg1Index.Site.coord false false, .coord true false, .valid false, .valid true].map
      Wg1Index.Site.pc ++
    (List.finRange 4).flatMap (fun r => (List.finRange 8).map (Wg2.Site.store r · |>.pc))

set_option maxRecDepth 100000 in
private theorem write_sites_cover : OpPcsFast kernel.code writeOp writeSites = true := by
  decide +kernel

/-- The abstract softmax sites that can produce an ordinary write. -/
inductive SoftmaxWriteSite : Wg0.Site → Prop
  | stage (j : Fin 4) (k : Fin 8) : SoftmaxWriteSite (.oStage j k)
  | exchange (j : Fin 8) : SoftmaxWriteSite (.exchStore j)
  | probability (j : Fin 4) : SoftmaxWriteSite (.pStore j)
  | rowMax : SoftmaxWriteSite .rowMax
  | lseStore0 : SoftmaxWriteSite .lseStore0
  | lseStore : SoftmaxWriteSite .lseStore

/-- The abstract index sites that can produce an ordinary write. -/
inductive IndexWriteSite : Wg1Index.Site → Prop
  | coordinate (extra high : Bool) : IndexWriteSite (.coord extra high)
  | validity (extra : Bool) : IndexWriteSite (.valid extra)

/-- The classifications of ordinary writes in the composed thread machine. -/
@[expose] def writeRole : Machine.ThreadD → Prop
  | .wg0 d => SoftmaxWriteSite d.site
  | .wg2 d => ∃ r s, d.site = .store r s
  | .index d => IndexWriteSite d.site
  | .prologue _ => True
  | _ => False

local macro "exclude_write_site " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

private theorem write_role {P : Params} {L : Launch} {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ writeSites) : writeRole d := by
  cases d with
  | wg0 d =>
    change d.site.pc ∈ writeSites at h
    change SoftmaxWriteSite d.site
    generalize d.site = s at h ⊢
    clear d
    cases s with
    | oStage j k => exact .stage j k
    | exchStore j => exact .exchange j
    | pStore j => exact .probability j
    | rowMax => exact .rowMax
    | lseStore0 => exact .lseStore0
    | lseStore => exact .lseStore
    | _ => all_goals exclude_write_site h
  | wg2 d =>
    change d.site.pc ∈ writeSites at h
    change ∃ r s, d.site = .store r s
    generalize d.site = site at h ⊢
    clear d
    cases site with
    | store r s => exact ⟨r, s, rfl⟩
    | _ => all_goals exclude_write_site h
  | index d =>
    change d.site.pc ∈ writeSites at h
    change IndexWriteSite d.site
    generalize d.site = site at h ⊢
    clear d
    cases site with
    | coord extra high => exact .coordinate extra high
    | valid extra => exact .validity extra
    | _ => all_goals exclude_write_site h
  | prologue _ => trivial
  | head => exact absurd h (by change 1843 ∉ writeSites; decide)
  | done => exact absurd h (by change 3611 ∉ writeSites; decide)
  | idle d =>
    change d.pc ∈ writeSites at h
    cases d <;> exclude_write_site h
  | mma d =>
    change False
    change d.site.pc ∈ writeSites at h
    generalize d.site = site at h
    clear d
    cases site <;> exclude_write_site h
  | tma d =>
    change False
    change d.site.pc ∈ writeSites at h
    generalize d.site = site at h
    clear d
    cases site <;> exclude_write_site h

/-- Identify the role of an actual ordinary write at its tracked state. -/
theorem of_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {i : EvId} {a : Acc} {bs : List Byte}
    {d : Machine.ThreadD} (hw : X.Writes i a bs)
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d)) :
    writeRole d := by
  obtain ⟨_, _, _, _, _, hcode, hf⟩ := Frame.fired_site hs hX hw.choose_spec hd
  exact write_role (OpPcsFast.mem write_sites_cover hcode (fires_write_op hf rfl))

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {i : EvId} {a : Acc}
    {bs : List Byte} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
include hpre hX hs

/-- An ordinary write covering the staging region is either a staging write or a
dequantization store in slot one. The latter also records the executed store and its invariant. -/
theorem from_covered_write (ht : Frame.Tracked (Machine.code P L) X) (hw : X.Writes i a bs)
    (hcover : a.Covers l) (hshared : l.space = .shared) (hlo : L.sharedBase + 65536 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 131072) :
    (∃ (d : Wg0.D) (j : Fin 4) (k : Fin 8),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
      d.site = .oStage j k) ∨
    ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8) (u : TState),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧
      d.site = .store r s ∧ d.buf = 1 ∧ Wg2.Inv P L i.1 d ∧
      (Wg2.machine P L i.1).Fired (some (.inr d)) ⟨hw.choose, .wr a bs⟩ (some u) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have haSpace : a.loc.space = .shared := hcover.1.symm.trans hshared
  have haLow : a.loc.addr ≤ l.addr := hcover.2.2.1
  have haHigh : l.addr < a.loc.addr + a.size := hcover.2.2.2
  have excludeHigh {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : L.sharedBase + 131072 ≤ fp.loc.addr) : False := by
    rw [(Kind.wr.inj hk).1] at haLow
    omega
  have excludeGlobal {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (hspace : fp.loc.space = .global) : False := by
    rw [(Kind.wr.inj hk).1, hspace] at haSpace
    cases haSpace
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX he hd
  have hrole := write_role (OpPcsFast.mem write_sites_cover hcode (fires_write_op hf rfl))
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    cases d with
    | wg0 d =>
      change SoftmaxWriteSite d.site at hrole
      generalize hsite : d.site = s at hrole
      cases hrole with
      | stage j k => exact .inl ⟨d, j, k, hd, hsite⟩
      | exchange j =>
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_exchangeStore hpre j hsite hat hinv hcode hf
        exact (excludeHigh hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc]
          simp only [Wg0.shLoc, Wg0.exchangeBase]
          omega)).elim
      | probability k =>
        obtain ⟨fp, _, _, _, _, hk, hloc, _⟩ := Wg0.fires_pStore hpre hsite hat hinv hcode hf
        exact (excludeHigh hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc]
          simp only [Wg0.shLoc, Wg0.pTileBase]
          omega)).elim
      | rowMax =>
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_rowMax hpre hsite hat hinv hcode hf
        exact (excludeHigh hk (by rw [hloc]; simp only [Wg0.shLoc, Wg0.rowMaxBase]; omega)).elim
      | lseStore0 =>
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore0 hpre hsite hat hinv hcode hf
        exact (excludeHigh hk (by rw [hloc]; simp only [Wg0.shLoc, Wg0.rowMaxBase]; omega)).elim
      | lseStore =>
        have hb : Wg0.eOf L i.1 < P.b := Wg1Mma.batchOf_lt hpre hg
        have hq : Wg0.qOf L i.1 < P.s_q := Wg1Mma.queryOf_lt hpre hg
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore hpre hb hq hsite hat hinv hcode hf
        exact (excludeGlobal hk (by rw [hloc, Wg0.lseLocOf_eq])).elim
    | wg2 d =>
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
      have htile : Wg2.tileOff L i.1 r.val s.val + 16 ≤ 65536 := by
        simp only [Wg2.numSteps, Wg2.dequantBytes, Wg2.tileOff, Wg2.topkBlock] at hfit ⊢
        omega
      have hbuf : d.buf = 1 := by
        have hb := hInv.bufLt
        by_contra hne
        have hz : d.buf = 0 := by omega
        rw [(Kind.wr.inj hk).1, hloc, hsize, hz] at haHigh
        change l.addr < L.sharedBase + 0 + Wg2.tileOff L i.1 r.val s.val + 16 at haHigh
        omega
      exact .inr ⟨d, r, s, u, hd, hsite, hbuf, hInv, hFired⟩
    | index d =>
      change IndexWriteSite d.site at hrole
      generalize hsite : d.site = s at hrole
      cases hrole with
      | coordinate extra high =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_main hpre hsite hinv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_coord_extra hpre hsite hinv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.coordOff]; omega)).elim
      | validity extra =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_main hpre hsite hinv hat hcode hf
          | obtain ⟨fp, hk, hloc, _⟩ :=
              Wg1Index.fires_valid_extra hpre hsite hinv hat hcode hf
        all_goals exact (excludeHigh hk (by rw [hloc]; simp only [Wg1Index.validOff]; omega)).elim
    | prologue d =>
      obtain ⟨w, hthread, hw', halloc⟩ :=
        PrologueAllocation.write_at_allocStore hX hs (w := .thread i) (.inl hw) ⟨d, hd⟩
      obtain rfl := AsyncCopy.Ref.thread.inj hthread
      obtain ⟨hloc, _⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hw' halloc
      rw [hloc] at haLow
      change L.sharedBase + 222752 ≤ l.addr at haLow
      omega
    | head | done | idle _ | mma _ | tma _ => exact hrole.elim

private theorem index_from_packed_window {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d)) (hw : X.Writes i a bs)
    (hcover : a.Covers l) (hshared : l.space = .shared) (hlo : L.sharedBase + 221696 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 222752) :
    ∃ d : Wg1Index.D,
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.index d)) ∧
      Wg1Index.Inv P L i.1 d ∧
      ((∃ extra high, d.site = .coord extra high ∧
        a.loc = ⟨.shared, ctaOf L i.1, L.sharedBase + Wg1Index.coordOff L i.1 d.phase +
          4 * d.site.sub⟩ ∧ a.size = 4 ∧
        bs = (b32 (Wg1Index.coordValue P L i.1 d.block (laneOf L i.1) d.site.sub)).toBytes) ∨
      (∃ extra, d.site = .valid extra ∧
        a.loc = ⟨.shared, ctaOf L i.1, L.sharedBase + Wg1Index.validOff L i.1 d.phase⟩ ∧
        a.size = 1 ∧
        bs = (Value.bits 8 (BitVec.ofNat 64
          (Wg1Index.validWord P L i.1 d.block (laneOf L i.1) % 256))).toBytes)) := by
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have haSpace : a.loc.space = .shared := hcover.1.symm.trans hshared
  have haLow : a.loc.addr ≤ l.addr := hcover.2.2.1
  have haHigh : l.addr < a.loc.addr + a.size := hcover.2.2.2
  have excludeLow {fp : Acc} {bytes : List Byte} (hk : Kind.wr a bs = .wr fp bytes)
      (haddr : fp.loc.addr + fp.size ≤ L.sharedBase + 221696) : False := by
    rw [(Kind.wr.inj hk).1] at haHigh
    omega
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_site hs hX he hd
  have hrole := write_role (OpPcsFast.mem write_sites_cover hcode (fires_write_op hf rfl))
  cases o with
  | none => rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
  | some u =>
    cases d with
    | wg0 d =>
      change SoftmaxWriteSite d.site at hrole
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
        have hplane := Wg0.planeAdd_lt j.isLt
        have hxor := Wg0.xor_lt_eight k.isLt (Nat.mod_lt (tidOf L i.1 % 64) (by decide))
        exact (excludeLow hshape (by
          simp only [Wg0.shLoc, Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes]
          omega)).elim
      | exchange j =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_exchangeStore hpre j hsite hat hv hcode hf
        have hxor : ∀ w : Fin 4, w.val ^^^ 2 < 4 := by decide
        have hwarp : warpOf L i.1 ^^^ 2 < 4 := hxor ⟨warpOf L i.1, hv.warpLt⟩
        have hlane := hv.laneLt
        have hj := j.isLt
        exact (excludeLow hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc, hsize]
          simp only [Wg0.shLoc, Wg0.exchangeBase, Wg0.exchangeQuad, Wg0.exchangeChunk]
          omega)).elim
      | probability k =>
        obtain ⟨fp, _, _, _, _, hk, hloc, hsize, _⟩ :=
          Wg0.fires_pStore hpre hsite hat hv hcode hf
        have hhalf := Wg0.halfLt hv.warpLt
        have hlane := hv.laneLt
        have hklt := k.isLt
        have hsub : d.sub < 4 := by simpa only [hsite, Wg0.Site.elems] using hv.subLt
        exact (excludeLow hk (by
          simp only [Wg0.siteLoc, hsite, Option.some.injEq] at hloc
          rw [← hloc, hsize]
          simp only [Wg0.shLoc, Wg0.pTileBase, Wg0.pChunkStride]
          omega)).elim
      | rowMax =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_rowMax hpre hsite hat hv hcode hf
        exact (excludeLow hk (by
          rw [hloc, hsize]
          simp only [Wg0.shLoc, Wg0.rowMaxBase]
          omega)).elim
      | lseStore0 =>
        obtain ⟨fp, hk, hloc, hsize, _⟩ := Wg0.fires_lseStore0 hpre hsite hat hv hcode hf
        exact (excludeLow hk (by
          rw [hloc, hsize]
          simp only [Wg0.shLoc, Wg0.rowMaxBase]
          omega)).elim
      | lseStore =>
        have hb : Wg0.eOf L i.1 < P.b := Wg1Mma.batchOf_lt hpre hg
        have hq : Wg0.qOf L i.1 < P.s_q := Wg1Mma.queryOf_lt hpre hg
        obtain ⟨fp, hk, hloc, _⟩ := Wg0.fires_lseStore hpre hb hq hsite hat hv hcode hf
        rw [(Kind.wr.inj hk).1, hloc, Wg0.lseLocOf_eq] at haSpace
        cases haSpace
    | wg2 d =>
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
      change IndexWriteSite d.site at hrole
      generalize hsite : d.site = s at hrole
      have hv : Wg1Index.Inv P L i.1 d := hinv
      cases hrole with
      | coordinate extra high =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, hsize, _⟩ :=
              Wg1Index.fires_coord_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, hsize, _⟩ :=
              Wg1Index.fires_coord_extra hpre hsite hv hat hcode hf
        all_goals
          obtain ⟨ha, hbs⟩ := Kind.wr.inj hk
          exact ⟨d, hd, hv, .inl ⟨_, high, hsite, (congrArg Acc.loc ha).trans hloc,
            (congrArg Acc.size ha).trans hsize, hbs⟩⟩
      | validity extra =>
        cases extra <;> first
          | obtain ⟨fp, hk, hloc, hsize, _⟩ :=
              Wg1Index.fires_valid_main hpre hsite hv hat hcode hf
          | obtain ⟨fp, hk, hloc, hsize, _⟩ :=
              Wg1Index.fires_valid_extra hpre hsite hv hat hcode hf
        all_goals
          obtain ⟨ha, hbs⟩ := Kind.wr.inj hk
          exact ⟨d, hd, hv, .inr ⟨_, hsite, (congrArg Acc.loc ha).trans hloc,
            (congrArg Acc.size ha).trans hsize, hbs⟩⟩
    | prologue d =>
      obtain ⟨w, hthread, hw', halloc⟩ :=
        PrologueAllocation.write_at_allocStore hX hs (w := .thread i) (.inl hw) ⟨d, hd⟩
      obtain rfl := AsyncCopy.Ref.thread.inj hthread
      obtain ⟨hloc, _⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hw' halloc
      rw [hloc] at haLow
      change L.sharedBase + 222752 ≤ l.addr at haLow
      omega
    | head | done | idle _ | mma _ | tma _ => exact hrole.elim

theorem coordinate_from_followed_write {state : Machine.ThreadD}
    (hState : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some state)) (hw : X.Writes i a bs)
    (hcover : a.Covers l) (hshared : l.space = .shared) (hlo : L.sharedBase + 221728 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 222752) :
    ∃ (d : Wg1Index.D) (extra high : Bool),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.index d)) ∧
      d.site = .coord extra high ∧ Wg1Index.Inv P L i.1 d ∧
      a.loc = ⟨.shared, ctaOf L i.1, L.sharedBase + Wg1Index.coordOff L i.1 d.phase +
        4 * d.site.sub⟩ ∧ a.size = 4 ∧
      bs = (b32 (Wg1Index.coordValue P L i.1 d.block (laneOf L i.1) d.site.sub)).toBytes := by
  obtain ⟨d, hd, hv, hcoord | hvalid⟩ :=
    index_from_packed_window hpre hX hs hState hw hcover hshared (by omega) hhi
  · obtain ⟨extra, high, hsite, hloc, hsize, hbytes⟩ := hcoord
    exact ⟨d, extra, high, hd, hsite, hv, hloc, hsize, hbytes⟩
  · obtain ⟨_, _, hloc, hsize, _⟩ := hvalid
    have hp := hv.phase
    have hl : laneOf L i.1 < 32 := Nat.mod_lt _ (by decide)
    have hb := hcover.2.2.2
    rw [hloc, hsize] at hb
    simp only [Wg1Index.validOff] at hb
    omega

/-- The packed coordinate array is disjoint from every other ordinary shared store.
Return the actual index state, exact four-byte footprint and encoded coordinate word. -/
theorem coordinate_from_covered_write (ht : Frame.Tracked (Machine.code P L) X)
    (hw : X.Writes i a bs) (hcover : a.Covers l) (hshared : l.space = .shared)
    (hlo : L.sharedBase + 221728 ≤ l.addr) (hhi : l.addr < L.sharedBase + 222752) :
    ∃ (d : Wg1Index.D) (extra high : Bool),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.index d)) ∧
      d.site = .coord extra high ∧ Wg1Index.Inv P L i.1 d ∧
      a.loc = ⟨.shared, ctaOf L i.1, L.sharedBase + Wg1Index.coordOff L i.1 d.phase +
        4 * d.site.sub⟩ ∧ a.size = 4 ∧
      bs = (b32 (Wg1Index.coordValue P L i.1 d.block (laneOf L i.1) d.site.sub)).toBytes := by
  obtain ⟨_, hState⟩ := Frame.event_state hs hX ht hw.choose_spec (by simp)
  exact coordinate_from_followed_write hpre hX hs hState hw hcover hshared hlo hhi

omit hpre hX hs in
private theorem index_next_valid_leader {P : Params} {L : Launch} {g : Nat}
    {p d : Wg1Index.D} {e : Event} {extra : Bool}
    (hn : Wg1Index.next P L g p e = some (some d)) (hd : d.site = .valid extra) :
    laneOf L g % 4 = 0 := by
  by_contra hLane
  cases hp : p.site <;> simp only [Wg1Index.next, Wg1Index.nextSite, hp, hLane] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [Wg1Index.afterPairFirst, Wg1Index.afterReady]
  all_goals split_ifs at hd

omit hpre hX hs in
private theorem next_valid_leader {P : Params} {L : Launch} {g : Nat}
    {p : Machine.ThreadD} {d : Wg1Index.D} {e : Event} {extra : Bool}
    (hn : Machine.next P L g p e = some (some (.index d))) (hd : d.site = .valid extra) :
    laneOf L g % 4 = 0 := by
  cases p
  case prologue p =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try cases hn
    all_goals rename_i w _ _
    all_goals fin_cases w <;> cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
    unfold Wg1Index.init Wg1Index.firstSite at hd
    split_ifs at hd
  case index p =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q hq
      cases hn
      exact index_next_valid_leader hq hd
    · split at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

omit hpre hX hs in
private theorem valid_leader_at {P : Params} {L : Launch} {X : Execution}
    {g i : Nat} {d : Wg1Index.D} {extra : Bool}
    (hlen : i ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hd : d.site = .valid extra) : laneOf L g % 4 = 0 := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hs
    cases hs
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
    have hz := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hs] at hz
    cases hp : Frame.stateAt (Machine.code P L) X g j with
    | none => rw [hp] at hz; cases hz
    | some p =>
      cases p with
      | none => rw [hp] at hz; cases hz
      | some p =>
        rw [hp] at hz
        exact next_valid_leader hz.symm hd

/-- A write covering the validity window is an actual one-byte write by its quad leader. -/
theorem validity_from_followed_write {s : Machine.ThreadD}
    (hState : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some s)) (hw : X.Writes i a bs)
    (hcover : a.Covers l) (hshared : l.space = .shared) (hlo : L.sharedBase + 221696 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 221728) :
    ∃ (d : Wg1Index.D) (extra : Bool) (quad : Fin 8),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.index d)) ∧
      d.site = .valid extra ∧ Wg1Index.Inv P L i.1 d ∧ laneOf L i.1 = 4 * quad.val ∧
      a.loc = l ∧ l = ⟨.shared, ctaOf L i.1, L.sharedBase + 221696 + 8 * d.phase + quad.val⟩ ∧
      a.size = 1 ∧
      bs = (Value.bits 8
        (BitVec.ofNat 64 (Wg1Index.quadByte P L i.1 d.block (4 * quad.val)))).toBytes := by
  obtain ⟨d, hd, hv, hcoord | hvalid⟩ :=
    index_from_packed_window hpre hX hs hState hw hcover hshared hlo (by omega)
  · obtain ⟨_, _, _, hloc, _, _⟩ := hcoord
    have hb := hcover.2.2.1
    rw [hloc] at hb
    simp only [Wg1Index.coordOff] at hb
    omega
  · obtain ⟨extra, hsite, hloc, hsize, hval⟩ := hvalid
    have hlane : laneOf L i.1 < 32 := Nat.mod_lt _ (by decide)
    have hleader := valid_leader_at (PTX.len_of_get hw.choose_spec).le hd hsite
    let quad : Fin 8 := ⟨laneOf L i.1 / 4, by omega⟩
    have hquad : laneOf L i.1 = 4 * quad.val := by
      change laneOf L i.1 = 4 * (laneOf L i.1 / 4)
      omega
    have haddr : a.loc.addr = l.addr := by
      have hlo := hcover.2.2.1
      have hhi := hcover.2.2.2
      omega
    have hl : a.loc = l := by
      have hsp := hcover.1.symm
      have hcta := hcover.2.1.symm
      cases hLoc : a.loc
      cases l
      simp only [Loc.mk.injEq]
      simpa only [hLoc] using And.intro hsp (And.intro hcta haddr)
    refine ⟨d, extra, quad, hd, hsite, hv, hquad, hl, ?_, hsize, ?_⟩
    · rw [← hl, hloc]
      have hq : laneOf L i.1 / 4 = quad.val := rfl
      simp only [Wg1Index.validOff, hq, Nat.add_assoc]
    · rw [hval, Wg1Index.validWord_leader _ _ _ _ _ hlane hleader, hquad]

/-- A write covering the validity window is an actual one-byte write by its quad leader. -/
theorem validity_from_covered_write (ht : Frame.Tracked (Machine.code P L) X) (hw : X.Writes i a bs)
    (hcover : a.Covers l) (hshared : l.space = .shared) (hlo : L.sharedBase + 221696 ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 221728) :
    ∃ (d : Wg1Index.D) (extra : Bool) (quad : Fin 8),
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.index d)) ∧
      d.site = .valid extra ∧ Wg1Index.Inv P L i.1 d ∧ laneOf L i.1 = 4 * quad.val ∧
      a.loc = l ∧ l = ⟨.shared, ctaOf L i.1, L.sharedBase + 221696 + 8 * d.phase + quad.val⟩ ∧
      a.size = 1 ∧
      bs = (Value.bits 8
        (BitVec.ofNat 64 (Wg1Index.quadByte P L i.1 d.block (4 * quad.val)))).toBytes := by
  obtain ⟨_, hState⟩ := Frame.event_state hs hX ht hw.choose_spec (by simp)
  exact validity_from_followed_write hpre hX hs hState hw hcover hshared hlo hhi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.StageWriteClasses
