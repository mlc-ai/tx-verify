-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof.SchedulerStartWord
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

private theorem laterOfDifferent {X : Execution} {g pos j : Nat} {e target : Event}
    (he : X.get (g, pos) = some e) (ht : X.get (g, j) = some target)
    (hIndex : pos ≤ j) (hDiff : e ≠ target) : pos + 1 ≤ j := by
  by_contra h
  have hEq : pos = j := by omega
  subst j
  exact hDiff (Option.some.inj (he.symm.trans ht))

variable {A : List Assumption}

private theorem suffixRunTerminated {l : Launch} {X : Execution} {g pos : Nat} {t : TState}
    {o : Option TState} {pc : Nat} (hr : Run kernel A l g t ((X.tr g).drop pos) o)
    (hPos : pos < (X.tr g).length) (hExit : (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    Run kernel A l g t ((X.tr g).drop pos) none := by
  cases o with
  | none => exact hr
  | some u =>
    have hLast : ((X.tr g).drop pos).getLast? = some ⟨pc, .exit⟩ := by
      rw [List.getLast?_drop, ite_eq_right (Nat.not_le.mpr hPos), hExit]
    rw [List.getLast?_eq_getElem?] at hLast
    exact (hr.no_exit hLast).elim

/-- A warp-13 lane with a late event, an exit, or its fourth shuffle necessarily performed
the six common startup events before the target event. -/
theorem warp13StartupBeforeEvent [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) {j : Nat} {target : Event} (hTarget : X.get (g, j) = some target)
    (hDemand : 2769 < target.pc ∨ target.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl target = true)
    : 6 ≤ j := by
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  have hDiff {pos : Nat} {e : Event} (hPc : e.pc ≤ 2769) (hKind : e.kind ≠ .exit)
      (hShfl : pos < 3 ∨ Execution.isShfl e = false) (hEq : pos = j) : e ≠ target := by
    rintro rfl
    rcases hDemand with hl | he | ⟨hj, hs⟩
    · omega
    · exact hKind he
    · rcases hShfl with hEarly | hNo
      · omega
      · exact Bool.noConfusion (hNo.symm.trans hs)
  have advanceIndex {pos : Nat} {e : Event} (he : X.get (g, pos) = some e) (hJ : pos ≤ j)
      (hPc : e.pc ≤ 2769) (hKind : e.kind ≠ .exit)
      (hShfl : pos < 3 ∨ Execution.isShfl e = false) : pos + 1 ≤ j := by
    by_cases hEq : pos = j
    · exact laterOfDifferent he hTarget hJ (hDiff hPc hKind hShfl hEq)
    · omega
  have h₀ : 0 < (X.tr g).length := by omega
  let e₀ := (X.tr g)[0]
  have he₀ : X.get (g, 0) = some e₀ := List.getElem?_eq_getElem h₀
  have hj₁ : 1 ≤ j := by
    have he := firstSharedValue hp hX g hg he₀
    exact advanceIndex he₀ (Nat.zero_le j) (by rw [he]; exact (by decide : 25 ≤ 2769))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have h₁ : 1 < (X.tr g).length := by omega
  let e₁ := (X.tr g)[1]
  have he₁ : X.get (g, 1) = some e₁ := List.getElem?_eq_getElem h₁
  have hj₂ : 2 ≤ j := by
    have he := secondWarpValue hp hX g hg he₁
    exact advanceIndex he₁ hj₁ (by rw [he]; exact (by decide : 34 ≤ 2769))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have h₂ : 2 < (X.tr g).length := by omega
  let e₂ := (X.tr g)[2]
  have he₂ : X.get (g, 2) = some e₂ := List.getElem?_eq_getElem h₂
  have hj₃ : 3 ≤ j := by
    have he := thirdWarpValue hp hX g hg he₂
    exact advanceIndex he₂ hj₂ (by rw [he]; exact (by decide : 35 ≤ 2769))
      (by rw [he]; intro h; cases h) (.inl (by decide))
  have hPrefix : X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
    have h0 := List.drop_eq_getElem_cons h₀
    have h1 := List.drop_eq_getElem_cons h₁
    have h2 := List.drop_eq_getElem_cons h₂
    rw [h2] at h1
    rw [h1] at h0
    exact h0
  obtain ⟨t, o, ht, hf, hBase, hWarp, _, _, _, hRun⟩ := broadcastPrefix hp hX g hg hPrefix
  rw [hw] at hWarp
  have nonempty {pos : Nat} (hpos : pos ≤ j) : (X.tr g).drop pos ≠ [] :=
    fun h => (Nat.not_lt_of_ge ((List.drop_eq_nil_iff.mp h).trans hpos)) hLen
  obtain ⟨u, hLocal, hu, huf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFrame⟩ :=
    nonzeroWarpWith (A := A) hp g 13 t (by decide) (by decide) ht hf hWarp hBase
  have hFenceBase : out kernel [] l g u = .ev (.fenceMbarInit (next u)) := by
    unfold out
    rw [hu, huf, Flow.code_172]
    rfl
  have hFence : Next kernel A l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hLocal, startupOut (.inl (by rw [hu]; decide)) hFenceBase⟩
  obtain ⟨e₃, u', he₃, hf₃, hRun₃⟩ := hFence.continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun (nonempty hj₃)
  obtain ⟨rfl, hEq⟩ := hf₃
  have hj₄ : 4 ≤ j := advanceIndex he₃ hj₃
    (by change u.pc ≤ 2769; rw [hu]; decide) (by intro h; cases h) (.inr rfl)
  obtain rfl := Option.some.inj hEq
  have hu' : (next u).pc = 173 := by change u.pc + 1 = 173; rw [hu]
  have hBarBase : out kernel [] l g (next u) = .ev (.bar 0 (next (next u)) none .sync) := by
    unfold out
    have hClean : (next u).fault = none := huf
    rw [hu', hClean, Flow.code_173]
    rfl
  have hBar : Next kernel A l g (next u) (next u) (.bar 0 (next (next u)) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hu']; decide)) hBarBase⟩
  obtain ⟨e₄, u'', he₄, hf₄, hRun₄⟩ := hBar.continuing_at_nonempty (pos := 4) (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun₃ (nonempty hj₄)
  obtain ⟨rfl, hEq⟩ := hf₄
  have hj₅ : 5 ≤ j := advanceIndex he₄ hj₄
    (by change (next u).pc ≤ 2769; rw [hu']; decide) (by intro h; cases h) (.inr rfl)
  obtain rfl := Option.some.inj hEq
  have hw' : (next (next u)).pc = 174 := by change (next u).pc + 1 = 174; rw [hu']
  obtain ⟨z, hzRun, hz, hzf, _, _, _, _, _, _⟩ :=
    warp13DispatchWith (A := A) hp g (next (next u)) hg hw' huf
      ((hFrame 1062 (by decide)).trans hWarp) ((hFrame 2535 (by decide)).trans hBase)
  have hz' : z.pc = 2769 := hz
  have hMaxBase : out kernel [] l g z = .ev (.setMaxReg false 80 (next z)) := by
    unfold out
    rw [hz', hzf, Flow.code_2769]
    rfl
  have hMax : Next kernel A l g (next (next u)) z (.setMaxReg false 80 (next z)) :=
    ⟨run_rtg hzRun, startupOut (.inr (.inr (by rw [hz']; decide))) hMaxBase⟩
  obtain ⟨e₅, z', he₅, hf₅, _⟩ := hMax.continuing_at_nonempty (pos := 5) (by
    rintro e ⟨_, _, hBad⟩
    cases hBad) hRun₄ (nonempty hj₅)
  obtain ⟨inst, rfl, _⟩ := hf₅
  exact advanceIndex he₅ hj₅ (by change z.pc ≤ 2769; rw [hz']) (by intro h; cases h) (.inr rfl)

/-- Exit is later than the six common startup events of a warp-13 lane. -/
theorem warp13StartupLength [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) {pc : Nat} (hExit : (X.tr g).getLast? = some ⟨pc, .exit⟩)
    : 6 < (X.tr g).length := by
  rw [List.getLast?_eq_getElem?] at hExit
  have he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := hExit
  have := warp13StartupBeforeEvent hp hX hg hw he (.inr (.inl rfl))
  omega

/-- The actual warp-13 startup frame carried throughout scheduling and output writeback. -/
def schedulerStartupFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1178, b32 (l.sharedBase + 68608)),
   (2390, b32 (l.sharedBase + 208)), (6497, b32 (l.sharedBase + 224)),
   (7290, .ptr 64 false (.param (param 10)) 0), (7502, b64 p.cuQBase), (7506, b64 p.cuQBase),
   (1072, b32 (g / l.block)), (1062, b32 13), (1201, b32 (laneOf l g))]

private theorem moveHolds {t u : TState} {facts : List (Nat × Value)}
    (h : Holds t.regs facts) (hKeep : ∀ pair ∈ facts, u.regs pair.1 = t.regs pair.1) :
    Holds u.regs facts := by
  induction facts with
  | nil => trivial
  | cons pair rest ih =>
    exact ⟨(hKeep pair (by simp)).trans h.1, ih h.2 fun pair hp => hKeep pair (by simp [hp])⟩

private theorem warp13StartupTrace {X : Execution} {g : Nat}
    (hLen : 6 < (X.tr g).length) :
    ∃ e₀ e₁ e₂ e₃ e₄ e₅ suffix, X.tr g = e₀ :: e₁ :: e₂ :: e₃ :: e₄ :: e₅ :: suffix := by
  cases hTr : X.tr g with
  | nil => simp [hTr] at hLen
  | cons e₀ xs =>
    cases xs with
    | nil => simp [hTr] at hLen
    | cons e₁ xs =>
      cases xs with
      | nil => simp [hTr] at hLen
      | cons e₂ xs =>
        cases xs with
        | nil => simp [hTr] at hLen
        | cons e₃ xs =>
          cases xs with
          | nil => simp [hTr] at hLen
          | cons e₄ xs =>
            cases xs with
            | nil => simp [hTr] at hLen
            | cons e₅ suffix => exact ⟨e₀, e₁, e₂, e₃, e₄, e₅, suffix, rfl⟩

/-- A lane with a pending scheduler event reaches the drain scheduler with the ABI's
batch count and CuQ base already installed. -/
theorem warp13SchedulerEntryOfNonemptyPrefix [StartupAgreement A] {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13) (hLen : 6 < (X.tr g).length) :
    ∃ s o, Run kernel A l g s ((X.tr g).drop 6) o ∧ s.pc = 2770 ∧ s.fault = none ∧
      s.regs 7228 = some (b32 p.batch) ∧ s.regs 7506 = some (b64 p.cuQBase) := by
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, suffix, hTrace⟩ := warp13StartupTrace hLen
  obtain ⟨_, _, _, t, o, hRun, ht, hf, _, _, _, _, _, _, hBatch, _, hCuQ, _, _, _⟩ :=
    warp13Startup hp hX g hg hw hTrace
  exact ⟨t, o, by simpa [hTrace] using hRun, ht, hf, hBatch, hCuQ⟩

/-- A warp-13 lane with an event beyond startup has the actual scheduler input
and a cursor to its first shuffle, including any required cuQ read. -/
theorem firstSchedulerCursorPrefixOnThread [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hLen : 6 < (X.tr g).length)
    (hReads : laneOf l g ≤ p.batch → CuQWordReadsFromLaunchOnThread p X g (laneOf l g)) :
    let lane := laneOf l g
    let pos := if p.batch < lane then 6 else 7
    ∃ s o, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
        schedulerStartupFrame p l g) ∧
      Run kernel A l g s ((X.tr g).drop pos) o ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 ∧
      (∀ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ → o = none) ∧
      (∀ j e, X.get (g, j) = some e →
        (2776 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) → pos ≤ j) := by
  dsimp only
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, suffix, hTrace⟩ := warp13StartupTrace hLen
  obtain ⟨he₃, he₄, ⟨inst, he₅⟩, t, o, hRun, ht, hf, hShared, hWarp, hReady,
    hFree, hCta, hBuf, hBatch, hCuQ', hCuQ, hMap, hSub, hAcc⟩ := warp13Startup hp hX g hg hw hTrace
  have he₀ : X.get (g, 0) = some e₀ := by simp [Execution.get, hTrace]
  have he₁ : X.get (g, 1) = some e₁ := by simp [Execution.get, hTrace]
  have he₂ : X.get (g, 2) = some e₂ := by simp [Execution.get, hTrace]
  have hKnown₀ := firstSharedValue hp hX g hg he₀
  have hKnown₁ := secondWarpValue hp hX g hg he₁
  have hKnown₂ := thirdWarpValue hp hX g hg he₂
  have hCounts : ((X.tr g).take 6).countP Execution.isShfl = 3 ∧
      ((X.tr g).take 6).countP isFullWarpVote = 0 := by
    rw [hTrace, hKnown₀, hKnown₁, hKnown₂, he₃, he₄, he₅]
    exact ⟨rfl, rfl⟩
  have hRun6 : Run kernel A l g t ((X.tr g).drop 6) o := by
    simpa [hTrace] using hRun
  have hEnd : ∀ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ → o = none := by
    intro pc he
    cases o with
    | none => rfl
    | some t =>
      have hh : ((X.tr g).drop 6).getLast? = some ⟨pc, .exit⟩ := by
        rw [List.getLast?_drop, ite_eq_right (Nat.not_le.mpr hLen), he]
      rw [List.getLast?_eq_getElem?] at hh
      exact (hRun6.no_exit hh).elim
  have hSuffix : (X.tr g).drop 6 ≠ [] :=
    fun h => Nat.not_le_of_lt hLen (List.drop_eq_nil_iff.mp h)
  obtain ⟨u, hLocal, huf, hu, hLane, hZero, hPart, hClean, hKeep⟩ :=
    enterSchedulerWith (A := A) hp g t ht hf hBatch
  have hCleanU := hClean ⟨hSub, hAcc⟩
  have hFrame : Holds u.regs ((7228, b32 p.batch) :: schedulerStartupFrame p l g) := by
    exact ⟨(hKeep 7228 (by decide)).trans hBatch, (hKeep 2535 (by decide)).trans hShared,
      (hKeep 1178 (by decide)).trans hBuf, (hKeep 2390 (by decide)).trans hReady,
      (hKeep 6497 (by decide)).trans hFree, (hKeep 7290 (by decide)).trans hMap,
      (hKeep 7502 (by decide)).trans hCuQ', (hKeep 7506 (by decide)).trans hCuQ,
      (hKeep 1072 (by decide)).trans hCta, (hKeep 1062 (by decide)).trans hWarp, hLane, trivial⟩
  by_cases hSkip : p.batch < laneOf l g
  · have hup : u.pc = 2777 := by simpa only [hSkip, ↓reduceIte] using hu
    have hNext : Next kernel A l g t u
        (.shfl .down (b32 0) 1 31 (fun x _ => next (setReg u 2308 x))) :=
      ⟨run_rtg hLocal, startupOut (.inr (.inr (by rw [hup]; decide)))
        (schedulerFirstShuffle hp g u 0 hup huf hZero)⟩
    rw [ite_eq_left hSkip, firstSchedulerWord, ite_eq_left hSkip]
    have hAt : At u 2777 ((7228, b32 p.batch) :: (7217, b32 0) ::
        schedulerStartupFrame p l g) :=
      ⟨hup, hCleanU.1, hCleanU.2, huf, hFrame.1, hZero, hFrame.2⟩
    -- Keeping the initial state of the suffix lets the next theorem invert its local steps.
    refine ⟨u, o, hAt, ?_, hCounts.1, hCounts.2, hEnd, ?_⟩
    swap
    · intro j e he hDemand
      exact warp13StartupBeforeEvent hp hX hg hw he
        (hDemand.imp_left (fun h => by omega))
    -- A local prefix is part of a run with a continuing event, so strip it at its stopping state.
    obtain ⟨recv, ok, he, _, hTail⟩ := hNext.shuffle_at_nonempty hRun6 hSuffix hCounts.1
    have hDrop : (X.tr g).drop 6 =
        ⟨2777, .shfl .down (b32 0) 1 31 recv ok⟩ :: (X.tr g).drop 7 := by
      rw [hup] at he
      have hIndex := (List.getElem?_eq_some_iff.mp he).1
      rw [List.drop_eq_getElem_cons hIndex, (List.getElem?_eq_some_iff.mp he).2]
    rw [hDrop]
    exact .step .refl ⟨_, hNext.stop, recv, ok, by rw [hup], rfl⟩ hTail
  · have hLaneBound := Nat.le_of_not_lt hSkip
    have hup : u.pc = 2774 := by simpa only [hSkip, ↓reduceIte] using hu
    obtain ⟨v, hvRun, hv, hvf, hvs, hva, hOut⟩ := schedulerLaneRead hp g u
      hLaneBound hup huf (hPart hLaneBound).1 (hPart hLaneBound).2 hLane
      ((hKeep 7506 (by decide)).trans hCuQ)
    obtain ⟨i₁, hCode₁, hNextPc, hBrx, hWrite₁⟩ :
        ∃ i : Instr, kernel.code[2774]? = some i ∧ nextPc i.op u.pc = u.pc + 1 ∧
          (∀ pc, ¬ BrxTarget i.op pc) ∧ writesRegs i.op = [7862] :=
      ⟨_, Flow.code_2774, rfl, fun _ h => h, rfl⟩
    obtain ⟨i₂, hCode₂, hWrite₂⟩ :
        ∃ i : Instr, kernel.code[2775]? = some i ∧ writesRegs i.op = [7863] :=
      ⟨_, Flow.code_2775, rfl⟩
    have hCode₁' : kernel.code[u.pc]? = some i₁ := by rw [hup]; exact hCode₁
    have hCode₂' : kernel.code[u.pc + 1]? = some i₂ := by rw [hup]; exact hCode₂
    have hReadRun : run kernel A l g 2 u = some v := by
      apply run_two_core_transport hCode₁' hNextPc hBrx _ hvRun
      intro s hs
      apply StartupAgreement.out_eq
      unfold StartupPc
      omega
    have hMove : ∀ r ∉ [7862, 7863], v.regs r = u.regs r := by
      intro r hr
      apply run_two_core_frame hCode₁' hCode₂' hNextPc hBrx hvRun r
      · rw [hWrite₁]
        intro h
        exact hr (by simp only [List.mem_singleton] at h; simp [h])
      · rw [hWrite₂]
        exact fun h => hr (List.mem_cons_of_mem _ h)
    let a : Acc := { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 }
    have hRead : Next kernel A l g t v (.read a (afterLoad v [7217])) :=
      ⟨run_rtg (run_comp hLocal hReadRun), startupOut (.inr (.inr (by rw [hv]; decide))) hOut⟩
    obtain ⟨e, w, he, hFire, hTail⟩ := hRead.continuing_at_nonempty (pos := 6) (by
      rintro _ ⟨_, _, _, hBad⟩
      cases hBad) hRun6 hSuffix
    obtain ⟨bs, _, rfl, hState⟩ := hFire
    obtain rfl := Option.some.inj hState
    rw [hv] at he
    have hBytes := hReads hLaneBound 6 bs ⟨2776, he⟩
    subst bs
    let word := b32 (p.qOffset (laneOf l g))
    let z := afterLoad v [7217] (word.toBytes.map some)
    have hz : z = next (setReg v 7217 word) := by
      dsimp only [z]
      rw [afterLoad_ok hvs hva (rebuild_scalar (v := word) (show 0 < 4 by decide) rfl)]
      simp only [next, setReg, hvs, hva]
    have hzp : z.pc = 2777 := by rw [hz]; change v.pc + 1 = 2777; rw [hv]
    have hFrameZ : Holds z.regs ((7228, b32 p.batch) :: schedulerStartupFrame p l g) := by
      apply moveHolds hFrame
      intro pair hPair
      have hReg : pair.1 ≠ 7217 ∧ pair.1 ∉ [7862, 7863] := by
        simp only [schedulerStartupFrame, List.mem_cons, List.not_mem_nil, or_false] at hPair
        rcases hPair with h | h | h | h | h | h | h | h | h | h | h <;>
          rw [h] <;> dsimp only <;> decide
      rw [hz]
      change (Function.update v.regs 7217 (some word)) pair.1 = u.regs pair.1
      rw [Function.update_of_ne hReg.1]
      exact hMove _ hReg.2
    rw [ite_eq_right hSkip, firstSchedulerWord, ite_eq_right hSkip]
    have hAt : At z 2777 ((7228, b32 p.batch) :: (7217, word) :: schedulerStartupFrame p l g) :=
      ⟨hzp, by rw [hz]; exact hvs, by rw [hz]; exact hva, by rw [hz]; exact hvf, hFrameZ.1,
        by rw [hz]; rfl, hFrameZ.2⟩
    refine ⟨z, o, hAt, hTail, ?_, ?_, hEnd, ?_⟩
    rotate_left 2
    · intro j e hGet hDemand
      have hAfter := warp13StartupBeforeEvent hp hX hg hw hGet
        (hDemand.imp_left (fun h => by omega))
      by_contra h
      have hIndex : j = 6 := by omega
      subst j
      have heq := Option.some.inj (he.symm.trans hGet)
      subst e
      rcases hDemand with hPc | hExit | ⟨_, hShfl⟩
      · exact Nat.lt_irrefl 2776 hPc
      · cases hExit
      · cases hShfl
    · rw [List.take_add_one]
      rw [show (X.tr g)[6]? = _ from he]
      exact (List.countP_append ..).trans (by rw [hCounts.1]; rfl)
    · rw [List.take_add_one]
      rw [show (X.tr g)[6]? = _ from he]
      exact (List.countP_append ..).trans (by rw [hCounts.2]; rfl)

/-- Apply the scoped proof when every CuQ read agrees with the launch. -/
theorem firstSchedulerCursorPrefix [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hLen : 6 < (X.tr g).length)
    (hReads : laneOf l g ≤ p.batch → CuQWordReadsFromLaunch p X (laneOf l g)) :
    let lane := laneOf l g
    let pos := if p.batch < lane then 6 else 7
    ∃ s o, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
        schedulerStartupFrame p l g) ∧
      Run kernel A l g s ((X.tr g).drop pos) o ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 ∧
      (∀ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩ → o = none) ∧
      (∀ j e, X.get (g, j) = some e →
        (2776 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) → pos ≤ j) :=
  firstSchedulerCursorPrefixOnThread hp hX g hg hw hLen
    (fun h => (hReads h).onThread g)

private theorem firstSchedulerCursor [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) (g : Nat) (hg : g < l.threads)
    (hw : warpIndex l g = 13) {pc : Nat} (hExit : (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) :
    let lane := laneOf l g
    let pos := if p.batch < lane then 6 else 7
    ∃ s, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
        schedulerStartupFrame p l g) ∧
      Run kernel A l g s ((X.tr g).drop pos) none ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 := by
  dsimp only
  have hLen := warp13StartupLength hp hX hg hw hExit
  obtain ⟨s, o, hs, hr, hShfl, hVote, hEnd, _⟩ :=
    firstSchedulerCursorPrefix hp hX g hg hw hLen
      (fun hi => cuQWordReadsFromLaunchOfProtected hp hX hi (hProtected hi))
  exact ⟨s, hs, hEnd pc hExit ▸ hr, hShfl, hVote⟩

/-- Replay the first scheduler shuffle at the actual prefix cursors. The per-lane terminal
state remains arbitrary after the collective. -/
theorem warp13FirstShuffleOfCursors [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X) {g : Nat} (hg : g < l.threads)
    (o : Nat → Option TState)
    (hCursors : ∀ lane < 32,
      let pos := if p.batch < lane then 6 else 7
      let thread := warpLane l g lane
      ∃ s, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
          schedulerStartupFrame p l thread) ∧
        Run kernel A l thread s ((X.tr thread).drop pos) (o lane) ∧
        ((X.tr thread).take pos).countP Execution.isShfl = 3 ∧
        ((X.tr thread).take pos).countP isFullWarpVote = 0 ∧
        (X.tr thread).drop pos ≠ []) :
    let pos := fun lane => if p.batch < lane then 6 else 7
    ∃ state : Nat → TState,
      WarpOrdinals l X g (fun lane => pos lane + 1) 4 0 ∧
      ∀ lane < 32,
        let thread := warpLane l g lane
        let source := if lane + 1 < 32 then lane + 1 else lane
        X.ShflK (thread, pos lane) 3 ∧
        Run kernel A l thread (state lane) ((X.tr thread).drop (pos lane + 1)) (o lane) ∧
        At (state lane) 2778
          ([(7228, b32 p.batch), (7217, b32 (firstSchedulerWord p lane)),
            (2308, b32 (firstSchedulerWord p source))] ++ schedulerStartupFrame p l thread) := by
  classical
  dsimp only
  let pos : Nat → Nat := fun lane => if p.batch < lane then 6 else 7
  let before : Nat → List (Nat × Value) := fun lane =>
    (7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
      schedulerStartupFrame p l (warpLane l g lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  let _ : Inhabited TState := ⟨{}⟩
  choose! state hAt hRun hCountShfl hCountVote hNonempty using hCursors
  have hOrd : WarpOrdinals l X g pos 3 0 := ⟨hCountShfl, hCountVote⟩
  have hShuffles (lane : Nat) (hl : lane < 32) :
      ∃ recv ok, X.get (warpLane l g lane, pos lane) =
          some ⟨2777, .shfl .down (b32 (firstSchedulerWord p lane)) 1 31 recv ok⟩ ∧
        Run kernel A l (warpLane l g lane) (next (setReg (state lane) 2308 recv))
          ((X.tr (warpLane l g lane)).drop (pos lane + 1)) (o lane) := by
    have ht := hAt lane hl
    let step := fun x (_ : Bool) => next (setReg (state lane) 2308 x)
    have hn : Next kernel A l (warpLane l g lane) (state lane) (state lane)
        (.shfl .down (b32 (firstSchedulerWord p lane)) 1 31 step) :=
      ⟨.refl, startupOut (.inr (.inr (by rw [ht.1]; decide)))
        (schedulerFirstShuffle hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1)⟩
    obtain ⟨recv, ok, he, _, hr⟩ :=
      hn.shuffle_at_nonempty (hRun lane hl) (hNonempty lane hl) (hCountShfl lane hl)
    exact ⟨recv, ok, by simpa only [ht.1] using he, hr⟩
  let _ : Inhabited Value := ⟨b32 0⟩
  choose! recv ok hEvent hTail using hShuffles
  have hValues := hOrd.shuffle_value hX hBlock hg (fun _ => 2777) .down
    (fun lane => b32 (firstSchedulerWord p lane)) recv (fun _ => 1) (fun _ => 31) ok hEvent
  obtain ⟨hK, hStep⟩ := hOrd.shuffle (fun _ => 2777) .down
    (fun lane => b32 (firstSchedulerWord p lane)) recv (fun _ => 1) (fun _ => 31) ok hEvent
  refine ⟨fun lane => next (setReg (state lane) 2308 (recv lane)), hStep, ?_⟩
  intro lane hl
  have hV : recv lane = b32 (firstSchedulerWord p (if lane + 1 < 32 then lane + 1 else lane)) := by
    have hSource : (shflSource .down lane 1 31).1 = if lane + 1 < 32 then lane + 1 else lane := by
      rw [Flow.shflSource_down_one]
      split <;> rfl
    simpa only [hSource] using (hValues lane hl).1
  have ht := hAt lane hl
  have hNext : At (next (setReg (state lane) 2308 (recv lane))) 2778 ((2308, recv lane) ::
      before lane) :=
    ht.set (r := 2308) (by simp [schedulerStartupFrame])
  exact ⟨hK lane hl, hTail lane hl,
    hNext.mono ⟨hNext.2.2.2.2.2.1, hNext.2.2.2.2.2.2.1,
      hV ▸ hNext.2.2.2.2.1, hNext.2.2.2.2.2.2.2⟩⟩

/-- The first scheduler shuffle aligns all warp-13 lanes at PC 2778. The access cursor
and all scheduler operands are the actual values after their observed events. -/
theorem warp13FirstShuffle [StartupAgreement A] {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel A m X) (hComplete : Complete l X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13)
    (hNoCancel : ∀ lane < 32, ¬ ClcCanceled l X (warpLane l g lane))
    (hProtected : ∀ lane < 32, lane ≤ p.batch → ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((globalLoc (p.cuQBase + 4 * lane)).at k)) :
    let pos := fun lane => if p.batch < lane then 6 else 7
    ∃ state : Nat → TState,
      WarpOrdinals l X g (fun lane => pos lane + 1) 4 0 ∧
      ∀ lane < 32,
        let thread := warpLane l g lane
        let source := if lane + 1 < 32 then lane + 1 else lane
        X.ShflK (thread, pos lane) 3 ∧
        Run kernel A l thread (state lane) ((X.tr thread).drop (pos lane + 1)) none ∧
        At (state lane) 2778
          ([(7228, b32 p.batch), (7217, b32 (firstSchedulerWord p lane)),
            (2308, b32 (firstSchedulerWord p source))] ++ schedulerStartupFrame p l thread) := by
  classical
  dsimp only
  let pos : Nat → Nat := fun lane => if p.batch < lane then 6 else 7
  let before : Nat → List (Nat × Value) := fun lane =>
    (7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
      schedulerStartupFrame p l (warpLane l g lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarp {lane : Nat} (hl : lane < 32) : SameWarp l g (warpLane l g lane) :=
    (Step.sameWarp_lane hBlock hg hl).1
  have hLane {lane : Nat} (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hCursors (lane : Nat) (hl : lane < 32) :
      ∃ s, At s 2777 (before lane) ∧
        Run kernel A l (warpLane l g lane) s ((X.tr (warpLane l g lane)).drop (pos lane)) none ∧
        ((X.tr (warpLane l g lane)).take (pos lane)).countP Execution.isShfl = 3 ∧
        ((X.tr (warpLane l g lane)).take (pos lane)).countP isFullWarpVote = 0 := by
    have hThread := (hWarp hl).1.2.1
    have hw' : warpIndex l (warpLane l g lane) = 13 := (hWarp hl).2.symm.trans hw
    obtain ⟨pc, hExit⟩ := (hComplete.1 _ hThread).resolve_left (hNoCancel lane hl)
    simpa only [hLane hl, pos, before] using firstSchedulerCursor hp hX _ hThread hw' hExit
      (by simpa only [hLane hl] using hProtected lane hl)
  apply warp13FirstShuffleOfCursors hp hX hg (fun _ => none)
  intro lane hl
  obtain ⟨s, hs, hr, hCountShfl, hCountVote⟩ := hCursors lane hl
  exact ⟨s, hs, hr, hCountShfl, hCountVote, fun hn => by rw [hn] at hr; cases hr⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
