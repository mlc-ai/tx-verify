-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueStartupUnique
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Lemmas.CtaBarrier.FirstGeneration

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem startupBeforeEvent (hX : Consistent l kernel Assumptions.all m X) {g index : Nat}
    (hg : g < l.threads) {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ j < index, X.IsBarrier (g, j) 0 none 173 := by
  by_cases hWarp : warpIndex l g = 0
  · obtain ⟨n, _, _, hBar, hEarlier, _⟩ :=
      warp0InitializerPrefix hp hX hg hWarp he (by omega)
    have hLater : n+1 < index := by
      by_contra hLe
      have h := (hEarlier.succ hBar rfl) index (by omega) e he
      omega
    exact ⟨n+1, hLater, hBar⟩
  · obtain ⟨hLater, hBar, _⟩ := nonzeroStartupBar hp hX hg (by omega) he hPc
    exact ⟨4, hLater, hBar⟩

/-- An arrival recorded in generation zero of barrier 0 comes from the common startup site.
A later arrival would have to be counted by the very startup wait it follows. -/
theorem generationZeroStartupSource (hX : Consistent l kernel Assumptions.all m X) {g n : Nat}
    (hg : g < l.threads)
    (hGen : CtaBarrier.GenerationOf l.block (X.barriers (g/l.block)) (g, n) 0 0) :
    X.IsBarrier (g, n) 0 none 173 := by
  obtain ⟨count, pc, mode, hn⟩ := hX.ctaBar.generation_barrier hGen
  obtain ⟨hSites, _, hMode, _, hCount, _, _⟩ := actualNamedBarrier hp hX hn
  by_cases hSite : pc = 173
  · subst pc
    have hC := hCount.mpr rfl
    subst count
    change mode = .sync at hMode
    subst mode
    exact hn
  have hLate : 173 < pc := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
    omega
  obtain ⟨j, hj, hStartup⟩ := startupBeforeEvent hp hX hg hn hLate
  exact (CtaBarrier.not_generationZero_after_sync hX (by decide) hj hStartup hGen).elim

private theorem generationZeroProtocolPrefix (hX : Consistent l kernel Assumptions.all m X)
    {c last : Nat} (hc : c < l.grid) {st : CtaBarrier.State}
    (hAtLast : CtaBarrier.At l.block (X.barriers c) last st)
    (hLastGen : (st.slots 0).generation = 0) :
    NamedBar.Protocol none (Finset.range 16) 0 ((X.barriers c).take (last+1)) := by
  refine CtaBarrier.first_generation_protocol hX.ctaBar hc hAtLast hLastGen ?_
  intro g j hg hGen
  have hWarp : (g % l.block)/32 ∈ Finset.range 16 := by
    have hLane := Nat.mod_lt g (NamedBar.block_pos_of_thread_lt hg)
    rw [hp.block] at hLane ⊢
    exact Finset.mem_range.mpr (by omega)
  exact ⟨hWarp, 173, .sync, generationZeroStartupSource hp hX hg hGen⟩

/-- Every arrival through the end of generation zero has the startup count and a physical warp
of the launched CTA. Later uses of the same numeric resource need no hypothesis here. -/
theorem generationZeroProtocol (hX : Consistent l kernel Assumptions.all m X) {c finish : Nat}
    (hDone : CtaBarrier.CompletesAt l.block (X.barriers c) finish 0 0) :
    NamedBar.Protocol none (Finset.range 16) 0 ((X.barriers c).take (finish+1)) := by
  obtain ⟨_, _, _, hFin, hAt, _, hGen, _⟩ := hDone
  exact generationZeroProtocolPrefix hp hX (hX.ctaBar.grid_of_get hFin) hAt hGen

omit hp in
/-- A returned startup wait proves that its CTA has completed generation zero of barrier 0. -/
theorem generationZeroReleased {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    (hStartup : X.IsBarrier (g, j) 0 none 173) (hPassed : j+1 < (X.tr g).length) :
    CtaBarDone l X (g/l.block) 0 := by
  exact CtaBarrier.first_generation_released_of_returned hX (by decide) hStartup hPassed

omit hp in
/-- The kernel emits no actual exit in the common prologue. -/
theorem exitIsAfterStartup {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {e : EvId} {pc : Nat}
    (he : X.get e = some ⟨pc, .exit⟩) : 173 < pc := by
  let notExit (op : Op) : Bool := match op with | .ret | .exit => false | _ => true
  have hAll : (kernel.code.take 174).all (fun ins => notExit ins.op) = true := by
    decide +kernel
  by_contra hNo
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
  · cases hBad
  have hGet : (kernel.code.take 174)[pc]? = some ins := by
    rwa [List.getElem?_take_of_lt (by omega)]
  have h := List.all_eq_true.mp hAll ins (List.mem_of_getElem? hGet)
  rcases fires_exit_op hFire rfl with hE | hE <;> simp [hE, notExit] at h

/-- Completion of generation zero implies an actual generation-zero startup arrival by every
lane of the CTA. If that lane is recorded as exited, its startup arrival preceded its exit. -/
theorem generationZeroMember (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hDone : CtaBarDone l X (g/l.block) 0) :
    ∃ j, X.IsBarrier (g, j) 0 none 173 ∧ CtaBarK l X (g, j) 0 := by
  have hWarp : (g % l.block)/32 ∈ Finset.range 16 := by
    have hLane := Nat.mod_lt g (NamedBar.block_pos_of_thread_lt hg)
    rw [hp.block] at hLane ⊢
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨finish, hFinished⟩ := hDone
  have hProto := generationZeroProtocol hp hX hFinished
  obtain ⟨j, hGen⟩ := CtaBarrier.first_generation_member hX hg (commonBarrierShape hp) hWarp
    hFinished hProto (fun k pc he => by
      obtain ⟨j, hLt, hBar⟩ := startupBeforeEvent hp hX hg he (exitIsAfterStartup hX he)
      exact ⟨j, hLt, 173, none, hBar⟩)
  have hStartup := generationZeroStartupSource hp hX hg hGen
  exact ⟨j, hStartup, hg, ⟨none, 173, hStartup⟩, hGen⟩

/-- A role event's preceding common startup wait belongs to barrier 0's generation zero. -/
theorem generationZeroBeforeEvent (hX : Consistent l kernel Assumptions.all m X) {g index : Nat}
    (hg : g < l.threads) {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ i < index, X.IsBarrier (g, i) 0 none 173 ∧ CtaBarK l X (g, i) 0 := by
  obtain ⟨i, hLt, hStartup⟩ := startupBeforeEvent hp hX hg he hPc
  have hIndex := (List.getElem?_eq_some_iff.mp he).1
  change index < (X.tr g).length at hIndex
  have hPassed : i+1 < (X.tr g).length := by omega
  have hReleased := generationZeroReleased hX hStartup hPassed
  obtain ⟨j, hMember, hKey⟩ := generationZeroMember hp hX hg hReleased
  have hEq := commonStartupUnique hX hg hMember hStartup
  exact ⟨i, hLt, hStartup, hEq ▸ hKey⟩

/-- After every startup arrival is recorded, generation zero of the common barrier is complete. -/
private theorem generationZeroOfRecorded (hX : Consistent l kernel Assumptions.all m X) {c : Nat}
    (hc : c < l.grid)
    (hAll : ∀ w ∈ Finset.range 16, ∃ j,
      X.IsBarrier (c*l.block+w*32, j) 0 none 173 ∧
        (c*l.block+w*32, j) ∈ (X.barriers c).flatMap CtaBarrier.Record.refs) :
    CtaBarrier.Released l.block (X.barriers c) 0 0 := by
  classical
  obtain ⟨u, hu⟩ := (hX.ctaBar.2 c hc).2.2
  by_cases hPos : 0 < (u.slots 0).generation
  · exact Step.CtaBar.released_of_generation_lt hu hPos
  have hZero : (u.slots 0).generation = 0 := by omega
  have hAtEnd : CtaBarrier.At l.block (X.barriers c) (X.barriers c).length u := by
    simpa [CtaBarrier.At] using hu
  have hProtocol := generationZeroProtocolPrefix hp hX hc hAtEnd hZero
  rw [List.take_of_length_le (by omega)] at hProtocol
  have hShape := commonBarrierShape hp
  refine CtaBarrier.released_of_all_arrived hProtocol hShape.pos hShape.target rfl
    hShape.bound hu ?_
  intro w hw
  obtain ⟨j, hStartup, href⟩ := hAll w hw
  obtain ⟨rec, hRec, hRef⟩ := List.mem_flatMap.mp href
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hRec
  obtain ⟨s, t, hs, ht⟩ := CtaBarrier.run_at_record hu hi
  have hSource := (hX.ctaBar.2 c hc).2.1 rec hRec
  cases rec with
  | exit x y =>
    obtain ⟨_, _, pc, hGet⟩ := hSource
    change _ ∈ [y] at hRef
    rw [← (List.mem_singleton.mp hRef), hStartup] at hGet
    cases hGet
  | arrival id warp count lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hRef
    obtain ⟨_, hq2, pc, mode, hGet⟩ := hSource q hq
    rw [hqe, hStartup] at hGet
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hGet
    obtain ⟨_, rfl, rfl, _⟩ := hGet
    have hLane : q.1 = w*32 := by rw [hqe] at hq2; simp only at hq2; omega
    have hWarp := ((CtaBarrier.perform_arrival_lanes ht).2.1 q hq).2.1
    rw [hLane, Nat.mul_div_cancel _ (by decide : 0 < 32)] at hWarp
    subst warp
    have hLe := CtaBarrier.generation_mono_between (id := 0) hs hAtEnd
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1)
    exact ⟨i, lanes, s, hi, hs, by omega⟩

private theorem implicitStartup (hX : Consistent l kernel Assumptions.all m X) {e : EvId} {pc : Nat}
    {mode : BarMode} (he : X.get e = some ⟨pc, .bar 0 none mode⟩) :
    X.IsBarrier e 0 none 173 := by
  have hSite := actualNamedBarrier hp hX he
  have hPc := hSite.2.2.2.2.1.mp rfl
  have hMode : mode = .sync := by simpa [hPc, namedBarrierMode] using hSite.2.2.1
  change X.get e = some ⟨173, .bar 0 none .sync⟩
  rwa [hPc, hMode] at he

/-- An unrecorded full-warp arrival at common startup cannot mismatch or duplicate the arrival
of any warp. A completed generation already contains this lane's unique startup arrival. -/
theorem commonStartupNoAppendFault (hX : Consistent l kernel Assumptions.all m X) {c w : Nat}
    (hc : c < l.grid) (hw : w ∈ Finset.range 16) : ¬ NamedBar.WarpAppendFault l X c w 0 none := by
  classical
  intro hFault
  obtain ⟨s, err, hs, hSources, hFresh, hFailed, hErr⟩ := hFault
  let base := c*l.block+w*32
  let j := (X.tr base).length-1
  have hShape := commonBarrierShape hp
  have hLane : w*32 < l.block := by have := hShape.bound w hw; omega
  have hWarp : w*32/32 = w := Nat.mul_div_cancel _ (by decide)
  have hBase : base < l.threads := NamedBar.cta_thread_lt hc hLane
  have hOwn : base / l.block = c :=
    (NamedBar.lane_cta (NamedBar.block_pos_of_thread_lt hBase) hLane).1
  have hMem : (w*32, (base, j)) ∈ CtaBarrier.fullLanes l.block w (fun i =>
      (c*l.block+i, (X.tr (c*l.block+i)).length-1)) :=
    CtaBarrier.mem_fullLanes.mpr ⟨hLane, hWarp, rfl⟩
  obtain ⟨_, _, pc, mode, hGet⟩ := hSources _ hMem
  have hStart : X.IsBarrier (base, j) 0 none 173 := implicitStartup hp hX hGet
  have hUnrecorded : (base, j) ∉ (X.barriers c).flatMap CtaBarrier.Record.refs :=
    hFresh _ (List.mem_map.mpr ⟨_, hMem, rfl⟩)
  by_cases hPositive : 0 < (s.slots 0).generation
  · have hDone : CtaBarDone l X c 0 :=
      Step.CtaBar.released_of_generation_lt hs hPositive
    obtain ⟨i, hi, hKey⟩ := generationZeroMember hp hX hBase (by simpa only [hOwn] using hDone)
    have hSame := commonStartupUnique hX hBase hi hStart
    obtain ⟨idx, st, warp, count, lanes, k, hRec, _, hIn, _, _⟩ := hKey.2.2
    rw [hOwn] at hRec
    exact hUnrecorded (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hRec,
      List.mem_map.mpr ⟨(k, (base, i)), hIn, by rw [hSame]⟩⟩)
  have hZero : (s.slots 0).generation = 0 := by omega
  have hAtEnd : CtaBarrier.At l.block (X.barriers c) (X.barriers c).length s := by
    simpa [CtaBarrier.At] using hs
  have hProtocol := generationZeroProtocolPrefix hp hX hc hAtEnd hZero
  rw [List.take_of_length_le (by omega)] at hProtocol
  have hLedger := hProtocol.run_ledger hShape.pos hShape.target rfl hShape.bound hs
  have hNoExit (i pc' : Nat) (he : X.get (base, i) = some ⟨pc', .exit⟩) : False := by
    have hn := Execution.exit_last hX hBase he
    have heq : i = j := by dsimp [j]; omega
    rw [heq, hStart] at he
    exact Kind.noConfusion (congrArg Event.kind (Option.some.inj he))
  have hLive := NamedBar.not_exited_of_noExit hX hc hAtEnd hNoExit
  have hWL : CtaBarrier.warpLive l.block s.exited w :=
    ⟨0, by decide, by simpa only [Nat.add_zero] using hLane,
      by simpa only [Nat.add_zero] using hLive⟩
  have hNotArrived : w ∉ (s.slots 0).arrived := by
    intro hArrived
    have hBalance := hLedger.balance w hw hWL
    have hPositive : 0 < CtaBarrier.idArrivals (X.barriers c) 0 w := by
      simp only [hZero, hArrived, ↓reduceIte, Nat.zero_add] at hBalance
      omega
    obtain ⟨r, hr, hTagged⟩ := List.countP_pos_iff.mp hPositive
    cases r with
    | exit => cases hTagged
    | arrival id warp count lanes =>
      simp [CtaBarrier.isWarpIdArrival] at hTagged
      obtain ⟨rfl, rfl⟩ := hTagged
      have hCount := (hProtocol _ hr rfl).2
      subst count
      obtain ⟨idx, hIdx⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨before, after, hb, ha⟩ := CtaBarrier.run_at_record hs hIdx
      have hLiveBefore := NamedBar.not_exited_of_noExit hX hc hb hNoExit
      have hWitness := CtaBarrier.perform_arrival_lane ha hLane hWarp hLiveBefore
      obtain ⟨q, hq, hqLane⟩ := List.mem_map.mp hWitness
      obtain ⟨_, hOwner, pc', mode', hGet'⟩ := (hX.ctaBar.2 c hc).2.1 _ hr _ hq
      have hQ : q.2.1 = base := by rw [hOwner, hqLane]
      have hGetAt : X.get (base, q.2.2) = some ⟨pc', .bar 0 none mode'⟩ := by
        rw [← hQ, Prod.eta]
        exact hGet'
      have hSame := commonStartupUnique hX hBase (implicitStartup hp hX hGetAt) hStart
      have hRef : q.2 = (base, j) := Prod.ext hQ hSame
      exact hUnrecorded (List.mem_flatMap.mpr ⟨_, hr, List.mem_map.mpr ⟨q, hq, hRef⟩⟩)
  simp only [NamedBar.warpRecord, CtaBarrier.Record.perform] at hFailed
  split_ifs at hFailed
  · have hWarpRange : w < CtaBarrier.warps l.block := by
      simpa only [CtaBarrier.warps, hp.block] using Finset.mem_range.mp hw
    have hExpected := hLedger.expected
    have hValid : w < CtaBarrier.warps l.block ∧ CtaBarrier.warpLive l.block s.exited w :=
      ⟨hWarpRange, hWL⟩
    by_cases hNone : (s.slots 0).arrived = ∅ <;>
      simp [CtaBarrier.arrive, hValid, hNotArrived, hShape.target, hExpected, hNone,
        bind, Except.bind, pure, Except.pure] at hFailed
  · have he := Except.error.inj hFailed
    rw [← he] at hErr
    cases hErr

/-- The common startup wait can be released in a maximal execution with the same traces.
Only generation zero of barrier 0 is needed for this extension. -/
theorem commonBarrierCanReleaseGenerationZero (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLast : X.IsBarrier (g, (X.tr g).length-1) 0 none 173) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  let c := g/l.block
  have hc := NamedBar.cta_lt hg
  have hShape := commonBarrierShape hp
  have hAll (y : Nat) (hy : y < l.block) :=
    commonBarrierAllArrive hp hMax (NamedBar.cta_thread_lt hc hy)
  obtain ⟨Y, hY, hTr, _, hRecords⟩ := NamedBar.warps_record_of_noLocalFault
    Assumptions.wfStep.ctaHistory hShape hc (G := 0)
    (fun _ hY _ hw _ => commonStartupNoAppendFault hp hY hc hw)
    (fun y hy _ => by
      obtain ⟨j, hGet, hZero⟩ := hAll y hy
      exact ⟨j, 173, .sync, hGet, hZero⟩)
    (Finset.range 16).toList (fun w hw => Finset.mem_toList.mp hw) hMax rfl
  have hGet (e : EvId) : Y.get e = X.get e := by simp only [Execution.get, hTr]
  have hReleased : CtaBarDone l Y c 0 := generationZeroOfRecorded hp hY.1 hc (fun w hw => by
    have hLane : w*32 < l.block := by have := hShape.bound w hw; omega
    have hWarp : w*32/32 = w := Nat.mul_div_cancel _ (by decide)
    obtain ⟨j, hBar, hZero⟩ := hAll (w*32) hLane
    refine ⟨j, ?_,
      hRecords w (Finset.mem_toList.mpr hw) (w*32) hLane hWarp j 173 .sync none hBar hZero⟩
    change Y.get (c*l.block+w*32, j) = _
    rwa [hGet])
  obtain ⟨j, hMember, hKey⟩ := generationZeroMember hp hY.1 hg hReleased
  have hLastY : Y.IsBarrier (g, (X.tr g).length-1) 0 none 173 := by
    change Y.get (g, (X.tr g).length-1) = _
    rwa [hGet]
  have hSame := commonStartupUnique hY.1 hg hMember hLastY
  exact ⟨Y, hY, hTr, NamedBar.released_of_key hY.1.ctaBar hTr hLast (hSame ▸ hKey) hReleased⟩

end PTX.Kernels.TmlFa4Fwd.Prologue
