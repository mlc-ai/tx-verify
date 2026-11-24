-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcPositions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceExitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace

public section

/-! # Warp agreement of actual Tensor Memory collectives -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveTrace

open PTX PTX.Flow TcCollectiveSites

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private noncomputable def finalRank (P : Params) (L : Launch) (X : Execution) (g : Nat) : Nat :=
  TcPrologueRank.setup L g + Wg0TcPositions.beforeBlock (Wg0TcSchedule.voteOf L X g)
    (Wg0.blocksOf P L g) + 8

private inductive At (P : Params) (L : Launch) (X : Execution) (g : Nat) :
    Nat → Nat → TcKind → Prop
  | alloc (hw : warpOf L g = 0) :
    At P L X g 0 Flow.tmemAlloc_0
      (.resource .one (some (PrologueAllocation.allocAddress L g)) (.alloc 512))
  | relinquish (hw : warpOf L g = 0) :
    At P L X g 1 Flow.tmemRelinquish_0 (.resource .one none .relinquish)
  | data (d : Wg0.D) {k : TcKind} (hInv : Wg0.Inv P L g d)
      (hs : Wg0TcRank.Scheduled (Wg0TcSchedule.voteOf L X g) d)
      (hd : DataSite d.site) (hk : some k = dataOperands d.site) :
    At P L X g (TcPrologueRank.setup L g + Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) d)
      d.site.pc k
  | dealloc (hw : warpOf L g = 0) :
    At P L X g (finalRank P L X g) Flow.tmemDealloc_0 (.resource .one none (.dealloc 0 512))

private theorem at_event (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {g i tag : Nat} {k : TcKind} (he : X.get (g, i) = some ⟨tag, .tc k⟩)
    (hk : isTcColl ⟨tag, .tc k⟩ = true) :
    At P L X g (((X.tr g).take i).countP isTcColl) tag (tcStatic k) := by
  have hg := Frame.lt_of_get hX he
  have hi := (PTX.len_of_get he).le
  obtain ⟨d, o, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have hag : (Machine.code P L g).AtD d (Exists.choose hf) := (Exists.choose_spec hf).1.1
  have htag : tag = (Machine.code P L g).pc d :=
    (fires_pc (Exists.choose_spec hf).2).trans hag.1
  rcases TcCollectiveSites.of_fired hpre hf hk with ⟨q, rfl, hsite⟩ | ⟨_, _, _, hKind, hRes⟩
  · have hInv : Wg0.Inv P L g q := (Exists.choose_spec hf).1.2
    obtain ⟨hScheduled, hRank⟩ := Wg0TcTrace.rank_at hpre hX (hs g hg).machine hg hi hd
    rw [hRank, htag]
    exact .data q hInv hScheduled hsite (data_operands hpre hf hsite rfl)
  · obtain rfl := Kind.tc.inj hKind
    cases hRes
    case alloc hGrp hDst hReq =>
      obtain ⟨hw, hCount⟩ := Wg0TcTrace.prologue_rank_at hpre hX (hs g hg).machine hg hi hd
      rw [hCount, htag, hGrp, hDst, hReq]
      exact .alloc hw
    case relinquish hGrp hDst hReq =>
      obtain ⟨hw, hCount⟩ := Wg0TcTrace.prologue_rank_at hpre hX (hs g hg).machine hg hi hd
      rw [hCount, htag, hGrp, hDst, hReq]
      exact .relinquish hw
    case dealloc d hsite hw hGrp hDst hReq =>
      have hInv : Wg0.Inv P L g d := (Exists.choose_spec hf).1.2
      have hLast := hInv.epilogueLast (by rw [hsite]; rfl)
      obtain ⟨hScheduled, hRank⟩ := Wg0TcTrace.rank_at hpre hX (hs g hg).machine hg hi hd
      rw [hRank, Wg0TcPositions.finished_data hScheduled (.inr hsite) hLast]
      change tag = d.site.pc at htag
      rw [htag, hsite, hGrp, hDst, hReq]
      exact .dealloc hw

private theorem same_warp_index (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) :
    warpOf L g = warpOf L h := by
  simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2

private theorem same_block_count {g h : Nat} (hw : SameWarp L g h) :
    Wg0.blocksOf P L g = Wg0.blocksOf P L h := by
  simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, ctaOf, hw.1.2.2]

private theorem final_rank_eq (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) :
    finalRank P L X g = finalRank P L X h := by
  simp only [finalRank, TcPrologueRank.setup, same_warp_index hpre hw,
    same_block_count (P := P) hw, Wg0TcSchedule.same_warp (X := X) hw]

private theorem dealloc_at_rank {g : Nat} {n tag : Nat}
    (ha : At P L X g n tag (.resource .one none (.dealloc 0 512))) :
    n = finalRank P L X g ∧ tag = Flow.tmemDealloc_0 := by
  cases ha
  · rename_i d hInv hs hSite hOp
    generalize d.site = site at hSite hOp
    cases hSite <;> simp [dataOperands] at hOp
  · exact ⟨rfl, rfl⟩

/-- Actual final deallocations of lanes of a warp share the collective ordinal and tag. -/
theorem dealloc_aligned (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {e f : EvId} {tag tag' : Nat} (hw : SameWarp L e.1 f.1)
    (he : X.get e = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    (hf : X.get f = some ⟨tag', .tc (.resource .one none (.dealloc 0 512))⟩) :
    tag = tag' ∧ ∀ k, X.TcK e k ↔ X.TcK f k := by
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  have ha := dealloc_at_rank (at_event hpre hX hs ht he rfl)
  have hb := dealloc_at_rank (at_event hpre hX hs ht hf rfl)
  refine ⟨ha.2.trans hb.2.symm, ?_⟩
  intro k
  have hn := ha.1.trans ((final_rank_eq hpre hw).trans hb.1.symm)
  exact ⟨fun hk => ⟨⟨_, hf, rfl⟩, hn.symm.trans hk.2⟩,
    fun hk => ⟨⟨_, he, rfl⟩, hn.trans hk.2⟩⟩

private theorem data_before_final {g : Nat} {d : Wg0.D}
    (hInv : Wg0.Inv P L g d) (hSched : Wg0TcRank.Scheduled (Wg0TcSchedule.voteOf L X g) d)
    (hData : DataSite d.site) :
    TcPrologueRank.setup L g + Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) d <
      finalRank P L X g := by
  have hlt := Wg0TcPositions.before_final hSched hData hInv.rescaleArm hInv.blockLt
  unfold finalRank
  omega

private theorem at_same_rank (hpre : Pre P L mem0) {g h n m tag tag' : Nat} {k k' : TcKind}
    (hw : SameWarp L g h) (he : At P L X g n tag k) (hf : At P L X h m tag' k')
    (hr : n = m) :
    tag = tag' ∧ k = k' := by
  have hWarp := same_warp_index hpre hw
  have hSetup : TcPrologueRank.setup L g = TcPrologueRank.setup L h := by
    simp only [TcPrologueRank.setup, hWarp]
  have hBlocks := same_block_count (P := P) hw
  have hVotes := Wg0TcSchedule.same_warp (X := X) hw
  have hFinal := final_rank_eq (X := X) hpre hw
  have hMinG : 8 ≤ finalRank P L X g := by unfold finalRank; omega
  have hMinH : 8 ≤ finalRank P L X h := by unfold finalRank; omega
  cases he <;> cases hf
  case alloc.alloc w w' =>
    have hAddr : PrologueAllocation.allocAddress L g = PrologueAllocation.allocAddress L h := by
      simp [PrologueAllocation.allocAddress, ctaOf, hw.1.2.2]
    simp [hAddr]
  case relinquish.relinquish => exact ⟨rfl, rfl⟩
  case dealloc.dealloc => exact ⟨rfl, rfl⟩
  case data.data d hi hs hData ho f hi' hs' hData' ho' =>
    have hRank : Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) d =
        Wg0TcRank.rank (Wg0TcSchedule.voteOf L X g) f := by
      rw [hSetup, hVotes] at hr
      rw [hVotes]
      exact Nat.add_left_cancel hr
    have ha : Wg0.arm L g = Wg0.arm L h := by simp [Wg0.arm, hWarp]
    have hs'' : Wg0TcRank.Scheduled (Wg0TcSchedule.voteOf L X g) f := by
      simpa only [hVotes] using hs'
    have he := Wg0TcPositions.same_site hi hi' hs hs'' hData hData' hBlocks ha hRank
    refine ⟨congrArg Wg0.Site.pc he, Option.some.inj ?_⟩
    exact ho.trans ((congrArg dataOperands he).trans ho'.symm)
  all_goals exfalso
  all_goals first
    | omega
    | (have hab := data_before_final (X := X) ‹Wg0.Inv P L g _› ‹_› ‹_›; omega)
    | (have hab := data_before_final (X := X) ‹Wg0.Inv P L h _› ‹_› ‹_›; omega)
    | (have hZero : warpOf L g = 0 := by assumption
       have h2 : TcPrologueRank.setup L g = 2 := by simp [TcPrologueRank.setup, hZero]
       omega)
    | (have hZero : warpOf L h = 0 := by assumption
       have h2 : TcPrologueRank.setup L h = 2 := by simp [TcPrologueRank.setup, hZero]
       omega)

/-- Actual equal-ordinal Tensor Memory events of a warp agree on source and static operands. -/
theorem agree (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {e f : EvId} {n tag tag' : Nat} {k k' : TcKind}
    (hw : SameWarp L e.1 f.1) (he : X.get e = some ⟨tag, .tc k⟩)
    (hf : X.get f = some ⟨tag', .tc k'⟩) (heK : X.TcK e n) (hfK : X.TcK f n) :
    tag = tag' ∧ tcStatic k = tcStatic k' := by
  obtain ⟨v, hv, hm⟩ := heK.1
  obtain ⟨w, hw', hm'⟩ := hfK.1
  cases Option.some.inj (he.symm.trans hv)
  cases Option.some.inj (hf.symm.trans hw')
  have ha := at_event hpre hX hs ht he hm
  have hb := at_event hpre hX hs ht hf hm'
  rw [heK.2] at ha
  rw [hfK.2] at hb
  exact at_same_rank hpre hw ha hb rfl

private theorem before_or_dealloc {g n tag : Nat} {k : TcKind} (ha : At P L X g n tag k) :
    n < finalRank P L X g ∨ (warpOf L g = 0 ∧ n = finalRank P L X g) := by
  cases ha
  case alloc | relinquish => left; unfold finalRank; omega
  case data d hi hs hd _ => exact .inl (data_before_final hi hs hd)
  case dealloc hw => exact .inr ⟨hw, rfl⟩

private theorem warp_lt {g n tag : Nat} {k : TcKind} (ha : At P L X g n tag k) :
    warpOf L g < 4 := by
  cases ha
  case alloc w | relinquish w | dealloc w => omega
  case data d hi hs hd ho => exact hi.warpLt

private theorem final_at (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {h i : Nat} {d : Wg0.D} {v : Event} (he : X.get (h, i) = some v)
    (hd : Frame.stateAt (Machine.code P L) X h i = some (some (.wg0 d)))
    (hsite : d.site = .commit ∨ d.site = .exit) :
    ((X.tr h).take i).countP isTcColl = finalRank P L X h := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, ⟨_, hInv⟩, _⟩ := ((hs h hg).machine.produces (hX.thr h hg)).fired_at he hd
  have hLast : d.block + 1 = Wg0.blocksOf P L h :=
    hInv.epilogueLast (by rcases hsite with hp | hp <;> rw [hp] <;> rfl)
  obtain ⟨hScheduled, hRank⟩ :=
    Wg0TcTrace.rank_at hpre hX (hs h hg).machine hg (PTX.len_of_get he).le hd
  rw [hRank, Wg0TcPositions.finished_data hScheduled hsite hLast]
  simp only [finalRank, Nat.add_assoc]

/-- A warp lane can exit only after all collective ranks observed by a peer. -/
theorem not_exited_short (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {e f : EvId} {n : Nat} (hw : SameWarp L e.1 f.1) (he : X.TcK e n) :
    ¬ X.ExitedShort isTcColl f n := by
  rintro ⟨⟨tag, hexit⟩, hShort⟩
  obtain ⟨⟨tag', kind⟩, hget, hk⟩ := he.1
  obtain ⟨k, rfl⟩ := isTcColl_kind hk
  have hAt := at_event hpre hX hs ht hget hk
  rw [he.2] at hAt
  have hWarp := same_warp_index hpre hw
  have hWLt := warp_lt hAt
  have hFin := final_rank_eq (X := X) hpre hw
  have hwg : wgOf L f.1 = 0 := by
    rw [hWarp] at hWLt
    unfold warpOf at hWLt
    unfold wgOf
    omega
  have hg := Frame.lt_of_get hX hexit
  have hDone := Wg0OutputVisits.doneAtExit hX (hs f.1 hg).machine ht hwg hexit rfl
  rcases before_or_dealloc hAt with hBefore | ⟨hZero, hLast⟩
  · obtain ⟨c, _, _, d, _, hev, _, hd, hsite, _, _⟩ :=
      Wg0OutputVisits.commitBeforeDone hX hg (hs f.1 hg).machine hwg hDone
    have hOrd := final_at hpre hX hs hev hd (.inl hsite)
    have hMono : ((X.tr f.1).take c).countP isTcColl ≤
        (X.tr f.1).countP isTcColl :=
      (List.take_sublist _ _).countP_le
    omega
  · have hZero' : warpOf L f.1 = 0 := hWarp.symm.trans hZero
    obtain ⟨c, _, evt, hdealloc⟩ :=
      ResourceEvents.dealloc_before_exit hpre hX (hs f.1 hg).machine ht hZero' hexit rfl
    obtain ⟨d, hd, hSite⟩ := ScoreReleaseTrace.dealloc_state hX hs ht hdealloc
    have hOrd := final_at hpre hX hs hdealloc hd (.inr hSite)
    have hSucc : ((X.tr f.1).take (c + 1)).countP isTcColl =
        ((X.tr f.1).take c).countP isTcColl + 1 := by
      have he' := hdealloc
      change (X.tr f.1)[c]? = _ at he'
      rw [List.take_add_one, he', Option.toList_some, List.countP_append]
      rfl
    have hMono : ((X.tr f.1).take (c + 1)).countP isTcColl ≤
        (X.tr f.1).countP isTcColl :=
      (List.take_sublist _ _).countP_le
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcCollectiveTrace
