-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.InputRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private theorem schedulerTau {l : Launch} {g pc : Nat} {t u : TState} {ins : Instr}
    (hpc : t.pc = pc) (hlo : 7755 ≤ pc) (hhi : pc ≤ 7762)
    (hc : kernel.code[pc]? = some ins) (hi : Assumptions.coreOp ins.op = true)
    (hr : run kernel [] l g 1 t = some u) :
    run kernel Assumptions.all l g 1 t = some u := by
  have hz : t.pc ∉ Assumptions.swExp2Sites := by
    rw [hpc]
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hEq := Assumptions.tauStep_all_eq_nil (L := l) (g := g) hz (hpc.symm ▸ hc) hi
  simpa only [run, hEq] using hr

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem frameFresh {r : Nat} {F : List (Nat × Value)} (h : r ∉ F.map Prod.fst) :
    ∀ pair ∈ F, pair.1 ≠ r := by
  intro pair hm hEq
  exact h (hEq ▸ List.mem_map_of_mem (f := Prod.fst) hm)

def firstLaneFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7267, b32 0), (682, .pred (p.batch < laneOf l g)), (1616, b32 (laneOf l g))] ++
    afterCreditFacts p l g

def firstShuffleFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7267, b32 (Epilogue.firstSchedulerWord p (laneOf l g))), (1616, b32 (laneOf l g))] ++
    afterCreditFacts p l g

local macro "correction_fresh" : tactic => `(tactic|
  (apply frameFresh;
   simp only [firstLaneFacts, firstShuffleFacts, afterCreditFacts, creditFacts, entryFacts,
     nonzeroBarrierFacts, abiFacts, List.cons_append, List.nil_append,
     List.map_cons, List.map_nil, Prod.fst];
   decide))

/-- The first local branch skips cuQ reads only for lanes above the sentinel. -/
theorem prepareSchedulerLane {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    (hp : Pre p l m) (ht : At t 7755 (afterCreditFacts p l g)) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if p.batch < laneOf l g then 7762 else 7759) (firstLaneFacts p l g) := by
  let lane := laneOf l g
  let u := next (setReg t 1616 (b32 lane))
  let v := next (setReg u 682 (.pred (p.batch < lane)))
  let w := next (setReg v 7267 (b32 0))
  have hu : At u 7756 ((1616, b32 lane) :: afterCreditFacts p l g) :=
    ht.set (by correction_fresh)
  have hv : At v 7757 ((682, .pred (p.batch < lane)) :: (1616, b32 lane) ::
      afterCreditFacts p l g) := hu.set (by correction_fresh)
  have hw : At w 7758 (firstLaneFacts p l g) := hv.set (by correction_fresh)
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have h1 : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_7755 rfl ht
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, SReg.width, sregValue, DType.width, Value.bytes,
      bind, Except.bind, pure, Except.pure, u, lane, b32,
      truncBits_ofNat (show lane < 2 ^ 32 by omega) (by decide)]
  have h2 : run kernel [] l g 1 u = some v := by
    apply run_local Flow.code_7756 rfl hu
    rw [execLocalA_nil, execLocal_int rfl]
    have hb := holds_lookup hu.2.2.2.2
      (show ((1616, b32 lane) :: afterCreditFacts p l g).lookup 7277 = _ from rfl)
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hu.2.2.2.2.1, hb, b32,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat (show lane < 2 ^ 32 by omega)
      (by decide), truncBits_ofNat (show p.batch < 2 ^ 32 by omega) (by decide)]
    change Except.ok (next (setReg u 682 (.pred (decide
      (toSigned 32 (BitVec.ofNat 64 p.batch) < toSigned 32 (BitVec.ofNat 64 lane)))))) =
        Except.ok v
    simp only [signedWord hBatch, signedWord (show lane < 2 ^ 31 by omega), Int.ofNat_lt, v]
  have h3 : run kernel [] l g 1 v = some w := by
    apply run_local Flow.code_7757 rfl hv
    rfl
  obtain ⟨z, h4, hz⟩ := run_bra (A := []) Flow.code_7758 (decide (p.batch < lane)) hw
    hw.2.2.2.2.2.1 (by simp)
  refine ⟨z, run_comp (run_comp (run_comp
    (schedulerTau ht.1 (by decide) (by decide) Flow.code_7755 rfl h1)
    (schedulerTau hu.1 (by decide) (by decide) Flow.code_7756 rfl h2))
    (schedulerTau hv.1 (by decide) (by decide) Flow.code_7757 rfl h3))
    (schedulerTau hw.1 (by decide) (by decide) Flow.code_7758 rfl h4), ?_⟩
  by_cases h : p.batch < lane <;> simpa [h, lane] using hz

private theorem schedulerOut {l : Launch} {g pc : Nat} {t : TState} {ins : Instr}
    (hpc : t.pc = pc) (hlo : 7755 ≤ pc) (hhi : pc ≤ 7762)
    (hc : kernel.code[pc]? = some ins) (hi : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hpc.symm ▸ hc) hi
  all_goals
    rw [hpc]
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites, Assumptions.delayedTmemSites,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem laneReadNext {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    (hp : Pre p l m) (hLane : laneOf l g ≤ p.batch) (ht : At t 7759 (firstLaneFacts p l g)) :
    ∃ w, At w 7761 ((8988, b64 (p.cuQBase + 4 * laneOf l g)) ::
        (8987, b64 (4 * laneOf l g)) :: firstLaneFacts p l g) ∧
      Next kernel Assumptions.all l g t w
        (.read { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 }
          (afterLoad w [7267])) := by
  let lane := laneOf l g
  let u := next (setReg t 8987 (b64 (4 * lane)))
  let v := next (setReg u 8988 (b64 (p.cuQBase + 4 * lane)))
  have hu : At u 7760 ((8987, b64 (4 * lane)) :: firstLaneFacts p l g) :=
    ht.set (by correction_fresh)
  have hv : At v 7761 ((8988, b64 (p.cuQBase + 4 * lane)) ::
      (8987, b64 (4 * lane)) :: firstLaneFacts p l g) := hu.set (by correction_fresh)
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane32 : laneOf l g < 2 ^ 32 := by change lane < 2 ^ 32; omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have hOff64 : 4 * lane < 2 ^ 64 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hBase64 : p.cuQBase < 2 ^ 64 := by omega
  have hSum : p.cuQBase + 4 * lane < 2 ^ 64 := by change lane ≤ p.batch at hLane; omega
  have h1 : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_7759 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, ht.2.2.2.2.2.2.1,
      b32, bind, Except.bind, pure, Except.pure, truncBits_ofNat hLane32 (by decide)]
    change Except.ok (next (setReg t 8987 (.bits 64
      (BitVec.ofNat 64 ((BitVec.ofNat 64 lane).toNat * 4))))) = .ok u
    rw [toNat_ofNat_lt hLane64, Nat.mul_comm lane 4]
    rfl
  have h2 : run kernel [] l g 1 u = some v := by
    apply run_local Flow.code_7760 rfl hu
    rw [execLocalA_nil, execLocal_int rfl]
    have hBase := holds_lookup hu.2.2.2.2
      (show ((8987, b64 (4 * lane)) :: firstLaneFacts p l g).lookup 7506 =
        some (b64 p.cuQBase) from rfl)
    simp only [execInt, DType.width, readValue, readBits, readReg, hBase, hu.2.2.2.2.1, b64,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat hBase64 (by decide),
      truncBits_ofNat hOff64 (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hSum (by decide), v]
  refine ⟨v, hv, run_rtg (run_comp
    (schedulerTau ht.1 (by decide) (by decide) Flow.code_7759 rfl h1)
    (schedulerTau hu.1 (by decide) (by decide) Flow.code_7760 rfl h2)), ?_⟩
  rw [schedulerOut hv.1 (by decide) (by decide) Flow.code_7761 rfl]
  unfold out
  rw [hv.1, hv.2.2.2.1, Flow.code_7761]
  change Out.ev (loadTmpl [] l g v .global false 32 [7267] 8988 0) = _
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  exact congrArg Out.ev (loadTmpl_global (t := v) (w := 32) hv.2.1 hv.2.2.2.2.1
    hSum (by decide) (by omega))

private theorem schedulerSuffix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState}
    (hs : 7761 < s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 7761 < e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  apply Thread.eventTailEventsOfSegmentFloor (floor := 7762) (by decide +kernel) _ hWalk hs
  intro site hLo hSite seg hMatch
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An observed correction lane read uses its in-range launch CuQ word. -/
theorem firstCuQReadFootprint (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, j) = some ⟨7761, .rd a bs⟩) :
    j = 9 ∧ laneOf l g ≤ p.batch ∧
      a = {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} := by
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < 7761; decide)
    (by change 7761 ∉ registerHintSites; decide)
  have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    change roleBodyPc (warpIndex l g) 7761 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · cases h
    · split_ifs at h <;> omega
  have hg := event_thread_lt hX he
  obtain ⟨t, o, _, ht, _, _, _, _, _, _, hr, hj⟩ :=
    correctionEntryBeforeEvent hp hX hg hw.1 hw.2 he (.inl (by change 7754 < 7761; decide))
  have hLen : j < (X.tr g).length := len_of_get he
  have hMore : (X.tr g).drop 9 ≠ [] :=
    fun h => Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hj)
  obtain ⟨u, hLocal, hu⟩ := prepareSchedulerLane hp ht
  have hPrefix := hr.after_local_nonempty (run_rtg hLocal) hMore
  by_cases hLane : laneOf l g ≤ p.batch
  · rw [ite_eq_right (Nat.not_lt_of_ge hLane)] at hu
    obtain ⟨v, hv, hNext⟩ := laneReadNext hp hLane hu
    obtain ⟨hPos, hAcc⟩ := hNext.uniqueScalarReadAt hv.1 hPrefix hj he
      (fun _ _ => schedulerSuffix)
    exact ⟨hPos, hLane, hAcc⟩
  · have hPc : u.pc = 7762 := by simpa [Nat.lt_of_not_ge hLane] using hu.1
    have hAt : ((X.tr g).drop 9)[j - 9]? = some ⟨7761, .rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hj]
      exact he
    have hPast := schedulerSuffix (by rw [hPc]; decide) hPrefix _ (List.mem_of_getElem? hAt)
    exact (Nat.lt_irrefl 7761 hPast).elim

private theorem laneReadBytes (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} (hLane : laneOf l g ≤ p.batch) {bs : List (Option Byte)}
    (he : X.get (g, pos) = some ⟨7761,
      .rd { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 } bs⟩) :
    bs = (b32 (p.qOffset (laneOf l g))).toBytes.map some :=
  cuQWordReads hp hX hLane (g, pos) bs ⟨7761, he⟩

private theorem takeEvent {X : Execution} {g pos : Nat} {e : Event}
    (he : X.get (g, pos) = some e) :
    (X.tr g).take (pos + 1) = (X.tr g).take pos ++ [e] := by
  obtain ⟨hlen, hGet⟩ := List.getElem?_eq_some_iff.mp he
  rw [List.take_succ_eq_append_getElem hlen, hGet]

private theorem entryCounts (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {inst : Nat} (h3 : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩)
    (h4 : X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩)
    (h5 : X.get (g, 5) = some ⟨7746, .setMaxReg false 64 inst⟩)
    (h6 : X.get (g, 6) = some ⟨7747, .bar 2 (some 416) .sync⟩)
    (h7 : X.get (g, 7) = some ⟨7752, .arrive (creditLoc l g 0) 0 1 true .cta⟩)
    (h8 : X.get (g, 8) = some ⟨7754, .arrive (creditLoc l g 1) 0 1 true .cta⟩) :
    ((X.tr g).take 9).countP Execution.isShfl = 3 ∧
      ((X.tr g).take 9).countP isFullWarpVote = 0 := by
  have hLen : 5 < (X.tr g).length := (List.getElem?_eq_some_iff.mp h5).1
  let e0 := (X.tr g)[0]'(by omega)
  let e1 := (X.tr g)[1]'(by omega)
  let e2 := (X.tr g)[2]'(by omega)
  have he0 : X.get (g, 0) = some e0 :=
    List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)
  have he1 : X.get (g, 1) = some e1 :=
    List.getElem?_eq_getElem (show 1 < (X.tr g).length by omega)
  have he2 : X.get (g, 2) = some e2 :=
    List.getElem?_eq_getElem (show 2 < (X.tr g).length by omega)
  rw [takeEvent h8, takeEvent h7, takeEvent h6, takeEvent h5, takeEvent h4, takeEvent h3,
    takeEvent he2, takeEvent he1, takeEvent he0, firstSharedValue hp hX g hg he0,
    secondWarpValue hp hX g hg he1, thirdWarpValue hp hX g hg he2]
  exact ⟨rfl, rfl⟩

/-- A late event on the lane supplies every earlier correction entry event and
the lane's actual cuQ word at its first shuffle, even on an unfinished trace. -/
theorem firstCorrectionCursorOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {target : Event} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g)
    (hHi : warpIndex l g < 12) (hEvent : X.get (g, j) = some target)
    (hDemand : 7761 < target.pc ∨ target.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl target = true) :
    let pos := if p.batch < laneOf l g then 9 else 10
    ∃ t o, At t 7762 (firstShuffleFacts p l g) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 ∧ pos ≤ j := by
  obtain ⟨t, o, _, ht, h3, h4, h5, h6, h7, h8, hRun, h9⟩ :=
    correctionEntryBeforeEvent hp hX hg hLo hHi hEvent
      (hDemand.imp_left (fun h => by omega))
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hEvent).1
  have nonempty {pos : Nat} (hPos : pos ≤ j) : (X.tr g).drop pos ≠ [] := by
    intro h
    exact Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hPos)
  have hCounts := entryCounts hp hX hg h3 h4 h5 h6 h7 h8
  obtain ⟨u, hLocal, hu⟩ := prepareSchedulerLane (g := g) hp ht
  have hRun9 := hRun.after_local_nonempty (run_rtg hLocal) (nonempty h9)
  dsimp only
  by_cases hSkip : p.batch < laneOf l g
  · rw [ite_eq_left hSkip] at hu ⊢
    refine ⟨u, o, hu.mono ?_, hRun9, hCounts.1, hCounts.2, h9⟩
    rw [firstShuffleFacts, Epilogue.firstSchedulerWord, ite_eq_left hSkip]
    exact ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2⟩
  · rw [ite_eq_right hSkip] at hu ⊢
    have hLane := Nat.le_of_not_gt hSkip
    obtain ⟨v, hv, hn⟩ := laneReadNext hp hLane hu
    obtain ⟨e, w, he, hFire, hTail⟩ := hn.continuing_at_nonempty (pos := 9) (by
      rintro _ ⟨_, _, _, hBad⟩
      cases hBad) hRun9 (nonempty h9)
    obtain ⟨bs, _, rfl, hw⟩ := hFire
    obtain rfl := Option.some.inj hw
    rw [hv.1] at he
    have hCounts10 : ((X.tr g).take 10).countP Execution.isShfl = 3 ∧
        ((X.tr g).take 10).countP isFullWarpVote = 0 := by
      rw [takeEvent he, List.countP_append, List.countP_append, hCounts.1, hCounts.2]
      exact ⟨rfl, rfl⟩
    obtain rfl := laneReadBytes hp hX hLane he
    let q := b32 (p.qOffset (laneOf l g))
    have hAfter : afterLoad v [7267] (q.toBytes.map some) = next (setReg v 7267 q) := by
      rw [afterLoad_ok hv.2.1 hv.2.2.1
        (PTX.Proof.rebuild_scalar (v := q) (show 0 < 4 by decide) rfl)]
      simp only [next, setReg, hv.2.1, hv.2.2.1]
    rw [hAfter] at hTail
    have hKeep : At v 7761 ((1616, b32 (laneOf l g)) :: afterCreditFacts p l g) :=
      hv.mono hv.2.2.2.2.2.2.2.2
    have hz := hKeep.set (r := 7267) (v := q) (by correction_fresh)
    rw [firstShuffleFacts, Epilogue.firstSchedulerWord, ite_eq_right hSkip]
    have h10 : 10 ≤ j := by
      by_cases hj : j = 9
      · subst j
        obtain rfl := Option.some.inj (he.symm.trans hEvent)
        rcases hDemand with h | h | ⟨_, h⟩
        · exact (show ¬ 7761 < 7761 by decide) h |>.elim
        · cases h
        · cases h
      · omega
    exact ⟨_, o, hz, hTail, hCounts10.1, hCounts10.2, h10⟩

/-- The skipped first read leaves a zero scheduler word and advances to the first shuffle. -/
theorem firstShuffleSkip {p : Params} {l : Launch} {g : Nat} {t : TState}
    (hSkip : p.batch < laneOf l g) (ht : At t 7762 (firstLaneFacts p l g)) :
    At t 7762 (firstShuffleFacts p l g) := by
  apply ht.mono
  rw [firstShuffleFacts, Epilogue.firstSchedulerWord, ite_eq_left hSkip]
  exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩

/-- The first protected CuQ read and its return leave precisely the frame of the first shuffle. -/
theorem firstShuffleReadNext {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    (hp : Pre p l m) (hLane : laneOf l g ≤ p.batch) (ht : At t 7759 (firstLaneFacts p l g)) :
    let addr : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
    let word := b32 (p.qOffset (laneOf l g))
    ∃ v, v.pc = 7761 ∧
      Next kernel Assumptions.all l g t v (.read addr (afterLoad v [7267])) ∧
      At (afterLoad v [7267] (word.toBytes.map some)) 7762 (firstShuffleFacts p l g) := by
  dsimp only
  obtain ⟨v, hv, hNext⟩ := laneReadNext hp hLane ht
  let q := b32 (p.qOffset (laneOf l g))
  have hAfter : afterLoad v [7267] (q.toBytes.map some) = next (setReg v 7267 q) := by
    rw [afterLoad_ok hv.2.1 hv.2.2.1
      (PTX.Proof.rebuild_scalar (v := q) (show 0 < 4 by decide) rfl)]
    simp only [next, setReg, hv.2.1, hv.2.2.1]
  have hKeep : At v 7761 ((1616, b32 (laneOf l g)) :: afterCreditFacts p l g) :=
    hv.mono hv.2.2.2.2.2.2.2.2
  refine ⟨v, hv.1, hNext, ?_⟩
  rw [hAfter, firstShuffleFacts, Epilogue.firstSchedulerWord, ite_eq_right (not_lt.mpr hLane)]
  exact hKeep.set (by correction_fresh)

/-- Decode the first down shuffle from the prepared correction scheduler lane. -/
theorem firstShuffleOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 7762 (firstShuffleFacts p l g)) :
    out kernel Assumptions.all l g t =
      .ev (.shfl .down (b32 (Epilogue.firstSchedulerWord p (laneOf l g))) 1 31
        (fun recv _ => next (setReg t 5869 recv))) := by
  rw [schedulerOut ht.1 (by decide) (by decide) Flow.code_7762 rfl]
  unfold out
  rw [ht.1, ht.2.2.2.1, Flow.code_7762]
  change Out.ev (shflTmpl l g t .down 5869 none (.reg 7267) (.imm 1) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, Value.bytes, readBits,
    pure, Except.pure, b32]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Correction
