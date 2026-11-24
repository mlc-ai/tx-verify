-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
public import Kernels.TmlFa4Fwd.Proof.MmaQueryCoverage
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Kernels.TmlFa4Fwd.Proof.MmaQkOperandFrame
import Kernels.TmlFa4Fwd.Proof.MmaQkQueryRetarget
public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue

noncomputable section

private inductive QueryCut
  | election | setup | secondElection | secondSetup | logicalExit

private def QueryCut.lower : QueryCut → Nat
  | .election => 1935
  | .setup => 2154
  | .secondElection => 2197
  | .secondSetup => 2216
  | .logicalExit => 2763

private def QueryCut.upper : QueryCut → Nat
  | .election => 2153
  | .setup => 2157
  | .secondElection => 2215
  | .secondSetup => 2219
  | .logicalExit => 2768

private def queryBankRegisters : List Nat := 9632 :: (List.finRange 8).map (9624 + ·.val)

private def QueryCut.keep : QueryCut → List Nat
  | .election | .secondElection => queryBankRegisters
  | .setup => 9636 :: queryBankRegisters
  | .secondSetup => 9653 :: queryBankRegisters
  | .logicalExit => []

private def QueryCut.allows (c : QueryCut) (pc : Nat) : Bool :=
  (c.lower ≤ pc && pc ≤ c.upper) || pc == 2763 || pc == 3099

private def QueryCut.check (c : QueryCut) (op : Op) : Bool :=
  c.keep.all (fun reg => !(mmaWrites op).contains reg) &&
    match op with
    | .bra dst _ => c.allows dst
    | .brx .. => false
    | _ => true

private theorem queryCutChecked (c : QueryCut) {pc : Nat} {i : Instr}
    (hl : c.lower ≤ pc) (hh : pc < c.upper) (hc : kernel.code[pc]? = some i) :
    c.check i.op = true := by
  let code := (kernel.code.drop c.lower).take (c.upper - c.lower)
  have hAll : code.all (fun ins => c.check ins.op) = true := by
    cases c <;> set_option maxRecDepth 100000 in kernel_rfl
  have hAt : code[pc - c.lower]? = some i := by
    dsimp only [code]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl, hc]
  exact List.all_eq_true.mp hAll i (List.mem_of_getElem? hAt)

private theorem queryCutStep (c : QueryCut) {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} {F : List (Nat × Value)}
    (hl : c.lower ≤ s.pc) (hh : s.pc < c.upper)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hF : Holds s.regs F) (hKeep : ∀ r ∈ F.map Prod.fst, r ∈ c.keep)
    (hw : WStep kernel Assumptions.all l g s ev u) :
    c.allows u.pc = true ∧
      (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F := by
  have hLo : 1907 ≤ s.pc := (show 1907 ≤ c.lower from by cases c <;> decide).trans hl
  have hHi : s.pc < 2768 := hh.trans_le (show c.upper ≤ 2768 from by cases c <;> decide)
  obtain ⟨hReach, hFrame⟩ := mmaCutStep hLo hHi hw hs
  have hOut : (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) := by
    simpa using hReach
  have hRegisters : Holds u.regs F := by
    apply Epilogue.holdsSchedulerFrame hF
    · intro r hr
      apply mmaStepReg (by omega) hHi _ hw
      intro i hc
      have h := (Bool.and_eq_true_iff.mp (queryCutChecked c hl hh hc)).1
      simpa using List.all_eq_true.mp h r (hKeep r hr)
    · intro _ h
      exact List.mem_map_of_mem h
  refine ⟨?_, hOut, hFrame, hRegisters⟩
  have hFall : c.allows (s.pc + 1) = true := by
    have hℓ : c.lower ≤ s.pc + 1 := by omega
    have hU : s.pc + 1 ≤ c.upper := by omega
    simp [QueryCut.allows, hℓ, hU]
  rcases hw with ⟨-, ht⟩ | ⟨e, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    rcases tau_core_frame hc ht' with rfl | h
    · exact hFall
    have hp := h.pc
    have hJump := (Bool.and_eq_true_iff.mp (queryCutChecked c hl hh hc)).2
    cases hi : i.op <;> simp only [hi, nextPc, BrxTarget, or_false] at hp
    case bra dst uni => rw [hp]; simpa only [hi] using hJump
    case brx => simp [hi] at hJump
    all_goals exact hp.symm ▸ hFall
  · have he' : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm, hTpl, hf⟩ := he
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · have hh' := hh.le
      simp [h, QueryCut.allows, hl, hh']
    · exact h.symm ▸ hFall

private theorem walkAtQueryCut (c : QueryCut) {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} {events : List Event} {visits : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : c.lower ≤ s.pc) (hHi : s.pc ≤ c.upper)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hF : Holds s.regs F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r ∈ c.keep)
    (hTarget : target ∈ events) (hLate : c.upper ≤ target.pc) (hMma : target.pc < 2768) :
    ∃ u pre tail post,
      events = pre ++ tail ∧ (u.pc = c.upper ∨ u.pc = 2763) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F ∧
      Walk kernel Assumptions.all l g u tail post ∧ target ∈ tail ∧
      (∀ e ∈ pre, e.pc < c.upper) := by
  have crosses {s u : TState} {ev : Option Event} {es : List Event} {vs : List Visit}
      (hLo : c.lower ≤ s.pc) (hHi : s.pc < c.upper)
      (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hF : Holds s.regs F)
      (hStep : WStep kernel Assumptions.all l g s ev u)
      (hWalk : Walk kernel Assumptions.all l g u es vs) (hm : target ∈ es) :
      (c.lower ≤ u.pc ∧ u.pc ≤ c.upper ∨ u.pc = 2763) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) ∧ Holds u.regs F := by
    obtain ⟨hA, hR, hShape, hRegs⟩ := queryCutStep c hLo hHi hs hF hKeep hStep
    simp only [QueryCut.allows, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hA
    rcases hA with (h | h) | hExit
    · exact ⟨.inl h, hShape, hRegs⟩
    · exact ⟨.inr h, hShape, hRegs⟩
    · rcases hR with h | ⟨_, hClean⟩
      · omega
      have hEvent := mmaEpilogueExitEvents hExit hClean (.inl rfl) hShape.2 hWalk _ hm
      omega
  induction hw with
  | stop => simp at hTarget
  | @tau s u events visits ht hw ih =>
    by_cases hStop : s.pc = c.upper
    · exact ⟨s, [], events, _, rfl, .inl hStop, hs, hF, .tau ht hw, hTarget, by simp⟩
    obtain ⟨h | h, hSh, hRegs⟩ := crosses hLo (by omega) hs hF (.inl ⟨rfl, ht⟩) hw hTarget
    · exact ih h.1 h.2 hSh hRegs hTarget
    · exact ⟨u, [], events, _, rfl, .inr h, hSh, hRegs, hw, hTarget, by simp⟩
  | @ev s u e events visits he hw ih =>
    by_cases hStop : s.pc = c.upper
    · exact ⟨s, [], e :: events, _, rfl, .inl hStop, hs, hF, .ev he hw, hTarget, by simp⟩
    have hMem := (List.mem_cons.mp hTarget).resolve_left (fun h => by
      have hp := estep_source_pc he
      rw [← h] at hp
      omega)
    obtain ⟨h | h, hShape, hRegs⟩ :=
      crosses hLo (by omega) hs hF (.inr ⟨_, rfl, he⟩) hw hMem
    · obtain ⟨v, pre, tail, post, hEq, hp, hS, hR, hW, hm, hPre⟩ := ih h.1 h.2 hShape hRegs hMem
      refine ⟨v, e :: pre, tail, post, by rw [hEq]; rfl, hp, hS, hR, hW, hm, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · have := estep_source_pc he
        omega
      · exact hPre v hv
    · refine ⟨u, [e], events, _, rfl, .inr h, hShape, hRegs, hw, hMem, ?_⟩
      intro other hm
      obtain rfl := List.mem_singleton.mp hm
      have := estep_source_pc he
      omega
  | last he =>
    obtain rfl := List.mem_singleton.mp hTarget
    exact ⟨_, [], [_], _, rfl, .inl (by have := estep_source_pc he; omega),
      hs, hF, .last he, by simp, by simp⟩

private theorem noEarlierEventInExit {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s events visits) (hLo : 2763 ≤ s.pc)
    (hHi : s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (he : e ∈ events) (hEarly : e.pc < 2763) : False := by
  have advance {s u : TState} {ev : Option Event} {es : List Event} {vs : List Visit}
      (hLo : 2763 ≤ s.pc) (hHi : s.pc < 2768)
      (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
      (hStep : WStep kernel Assumptions.all l g s ev u)
      (hW : Walk kernel Assumptions.all l g u es vs) (hE : e ∈ es) :
      2763 ≤ u.pc ∧ u.pc < 2768 ∧ (RoleShape u ∧ u.regs 1062 = some (b32 12)) := by
    obtain ⟨hAt, hRole | ⟨hExit, hClean⟩, hShape', _⟩ :=
      queryCutStep .logicalExit hLo hHi hShape (F := []) trivial (by simp) hStep
    · have hBound : 2763 ≤ u.pc := by
        simp only [QueryCut.allows, QueryCut.lower, QueryCut.upper, Bool.or_eq_true,
          Bool.and_eq_true, beq_iff_eq] at hAt
        rcases hAt with (h | h) | h
        · exact of_decide_eq_true h.1
        · omega
        · omega
      exact ⟨hBound, hRole.2, hShape'⟩
    · have hRet := mmaEpilogueExitEvents hExit hClean (.inl rfl) hShape'.2 hW _ hE
      omega
  induction hw with
  | stop => simp at he
  | tau ht hw ih =>
    obtain ⟨hA, hB, hC⟩ := advance hLo hHi hShape (.inl ⟨rfl, ht⟩) hw he
    exact ih hA hB hC he
  | ev hf hw ih =>
    rcases List.mem_cons.mp he with rfl | hm
    · have := estep_source_pc hf
      omega
    · obtain ⟨hA, hB, hC⟩ := advance hLo hHi hShape (.inr ⟨_, rfl, hf⟩) hw hm
      exact ih hA hB hC hm
  | last hf =>
    obtain rfl := List.mem_singleton.mp he
    have := estep_source_pc hf
    omega

private theorem queryCutAt {l : Launch} {g pc : Nat} {s : TState} {F : List (Nat × Value)}
    {events : List Event} {vs : List Visit} {e : Event}
    (hs : s.pc = pc) (hP : pc ≠ 1909) (hShape : RoleShape s) (hF : Holds s.regs F)
    (hWalk : Walk kernel Assumptions.all l g s events vs) (hMem : e ∈ events)
    (hLater : pc < e.pc) : At s pc F := by
  refine ⟨hs, hShape.2.2 (hs.symm ▸ hP), hShape.2.1, ?_, hF⟩
  cases hf : s.fault with
  | none => rfl
  | some fault =>
    cases hWalk with
    | stop => simp at hMem
    | tau ht _ => simp [Tau, out, hf] at ht
    | ev he _ =>
      obtain ⟨tm, hout, hFire⟩ := he
      simp only [out, hf, Out.ev.injEq] at hout
      subst tm
      cases hFire.2
    | last he =>
      obtain rfl := List.mem_singleton.mp hMem
      have := estep_source_pc he
      omega

private def queryBankFacts (l : Launch) (stage : Fin 2) : List (Nat × Value) :=
  (9632, b32 0x8200490) :: qDescriptorFacts l stage

private def queryBankElection (stage : Fin 2) : Fin 20 := if stage = 0 then 0 else 2

private def queryElectionCut (stage : Fin 2) : QueryCut :=
  if stage = 0 then .election else .secondElection

private def querySetupCut (stage : Fin 2) : QueryCut := if stage = 0 then .setup else .secondSetup

private theorem bankMap (l : Launch) (stage : Fin 2) :
    (queryBankFacts l stage).map Prod.fst = queryBankRegisters := by
  simp [queryBankFacts, queryBankRegisters, qDescriptorFacts, List.map_map, Function.comp_def]

private theorem bankRegBounds (l : Launch) (stage : Fin 2) {f : Nat × Value}
    (hf : f ∈ queryBankFacts l stage) : 9624 ≤ f.1 ∧ f.1 ≤ 9632 := by
  have h : f.1 ∈ (queryBankFacts l stage).map Prod.fst := List.mem_map.mpr ⟨f, hf, rfl⟩
  rw [bankMap] at h
  rcases List.mem_cons.mp h with h | h
  · omega
  · obtain ⟨step, _, hstep⟩ := List.mem_map.mp h
    have := step.isLt
    omega

private theorem beforeCommitSuffix {X : Execution} {g pos index : Nat} {target : Event}
    {earlier tail : List Event} (he : X.get (g, index) = some target) (hi : pos ≤ index)
    (hTrace : (X.tr g).drop pos = earlier ++ tail) (hEarlier : target ∉ earlier) :
    (X.tr g).drop (pos + earlier.length) = tail ∧ pos + earlier.length ≤ index := by
  constructor
  · rw [← List.drop_drop, hTrace, List.drop_append_length]
  · have hGet : ((X.tr g).drop pos)[index - pos]? = some target := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le hi]
    rw [hTrace] at hGet
    by_contra! h
    rw [List.getElem?_append_left (show index - pos < earlier.length by omega)] at hGet
    exact hEarlier (List.mem_of_getElem? hGet)

private theorem querySetupOnCommitLane {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g pos index commitPc : Nat} {spec : TcCommit.Spec}
    (hCommitSite : commitPc = 2642 ∨ commitPc = 2646 ∨ commitPc = 2274)
    (he : X.get (g, index) = some ⟨commitPc, .tc (.commit spec)⟩)
    {s : TState} {vs : List Visit}
    (hs : At s (queryElectionCut stage).lower
      (queryBankFacts l (if stage = 0 then 1 else 0)))
    (hRole : s.regs 1062 = some (b32 12)) (hIndex : pos ≤ index)
    (hWalk : Walk kernel Assumptions.all l g s ((X.tr g).drop pos) vs) :
    ∃ u nextPos visits, At u (qkPc (initialQkBlock stage) - 40)
        ((qkGuard (initialQkBlock stage), .pred true) ::
          queryBankFacts l (if stage = 0 then 1 else 0)) ∧
      u.regs 1062 = some (b32 12) ∧ nextPos ≤ index ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop nextPos) visits ∧
      ∃ election inst leader, election < nextPos ∧
        X.Elect (g,election) (electSite (queryBankElection stage)).pc (2^32-1) inst leader := by
  let target : Event := ⟨commitPc, .tc (.commit spec)⟩
  let first := queryElectionCut stage
  let setupCut := querySetupCut stage
  let ei := queryBankElection stage
  let F := queryBankFacts l (if stage = 0 then 1 else 0)
  let pred := qkGuard (initialQkBlock stage)
  have hElectPc : first.upper = (electSite ei).pc := by fin_cases stage <;> rfl
  have hSetupPc : setupCut.lower = (electSite ei).pc + 1 := by fin_cases stage <;> rfl
  have hSetupEnd : setupCut.upper = qkPc (initialQkBlock stage) - 40 := by fin_cases stage <;> rfl
  have hPred : (electSite ei).pred = pred := by fin_cases stage <;> rfl
  have hNoResult : (electSite ei).result = none := by fin_cases stage <;> rfl
  have hFirstKeep : first.keep = queryBankRegisters := by fin_cases stage <;> rfl
  have hSetupKeep : setupCut.keep = pred :: queryBankRegisters := by fin_cases stage <;> rfl
  have hFirstLate : first.upper < commitPc := by
    rcases hCommitSite with rfl | rfl | rfl <;> fin_cases stage <;> decide
  have hSetupLate : setupCut.upper < commitPc := by
    rcases hCommitSite with rfl | rfl | rfl <;> fin_cases stage <;> decide
  have hp₁ : first.upper ≠ 1909 := by fin_cases stage <;> decide
  have hp₂ : setupCut.upper ≠ 1909 := by fin_cases stage <;> decide
  have hg : g < l.threads := event_thread_lt hX he
  have hTarget : target ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := index - pos)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  have hsShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  have hLo : first.lower ≤ s.pc := hs.1.symm.le
  have hHi : s.pc ≤ first.upper := by
    rw [show s.pc = first.lower from hs.1]
    fin_cases stage <;> decide
  obtain ⟨u, pre, rest, post, hSplit, hu | hu, hUShape, hU, hW, hRem, hPre⟩ :=
    walkAtQueryCut first hWalk hLo hHi ⟨hsShape, hRole⟩ hs.2.2.2.2
      (by intro r hr; rwa [bankMap, ← hFirstKeep] at hr)
      hTarget hFirstLate.le (show commitPc < 2768 by omega)
  · have huAt : At u (electSite ei).pc F :=
      hElectPc ▸ queryCutAt hu hp₁ hUShape.1 hU hW hRem hFirstLate
    have hOut := electTemplate (l := l) (g := g) ei huAt
    cases hW with
    | stop => simp at hRem
    | tau ht _ => rw [Tau, hOut] at ht; cases ht
    | last ht =>
      obtain rfl := List.mem_singleton.mp hRem
      have hPc := estep_source_pc ht
      change commitPc = u.pc at hPc
      omega
    | @ev _ v e tail trail hE hW =>
      obtain ⟨tm, hTm, hFire⟩ := hE
      rw [hOut] at hTm
      obtain rfl := Out.ev.inj hTm.symm
      obtain ⟨inst, leader, rfl, hNext⟩ := hFire
      obtain rfl := Option.some.inj hNext
      have hElect : X.Elect (g, pos + pre.length) (electSite ei).pc
          (2 ^ 32 - 1) inst leader := by
        unfold Execution.Elect
        change (X.tr g)[pos + pre.length]? = _
        rw [← List.getElem?_drop, hSplit, List.getElem?_append_right (by rfl)]
        simp [huAt.1]
      have hFinal : ∃ electPc inst leader,
          X.Elect (g, index - 1) electPc (2 ^ 32 - 1) inst leader ∧ laneOf l g = leader := by
        rcases hCommitSite with rfl | rfl | rfl
        · obtain ⟨_, inst, leader, hElection, hLane⟩ := firstOutputCommitLeader hp hX he
          exact ⟨_, inst, leader, hElection, hLane⟩
        · obtain ⟨_, inst, leader, hElection, hLane⟩ := secondOutputCommitLeader hp hX he
          exact ⟨_, inst, leader, hElection, hLane⟩
        · obtain ⟨_, inst, leader, hElection, hLane⟩ := readyReleaseLeader hp hX 0 he
          exact ⟨_, inst, leader, hElection, hLane⟩
      obtain ⟨_, inst', leader', hFinalElect, hFinalLane⟩ := hFinal
      have hPeer : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
      have hLead := hFinalLane.trans (sameLeader hX hPeer hFinalElect hElect)
      have hFresh : ∀ f ∈ F, f.1 ≠ (electSite ei).pred := by
        intro f hf
        obtain ⟨_, hMax⟩ := bankRegBounds l _ hf
        have hGT : 9632 < (electSite ei).pred := by fin_cases stage <;> decide
        omega
      have hV := electStateFrame (l := l) (g := g) ei huAt leader hFresh
        (by intro f hf; simp [hNoResult])
      rw [beq_iff_eq.mpr hLead, hPred, ← hSetupPc] at hV
      let v := electState l g u ei leader
      have hVRole : v.regs 1062 = some (b32 12) := by
        have hNe : 1062 ≠ (electSite ei).pred := by fin_cases stage <;> decide
        simp [v, electState, hNoResult, next, setReg, hNe, hUShape.2]
      have hVShape : RoleShape v :=
        ⟨hV.2.1.symm ▸ Nat.zero_le _, hV.2.2.1, fun _ => hV.2.1⟩
      have hTail : target ∈ tail := (List.mem_cons.mp hRem).resolve_left (fun h => by
        have hp := congrArg Event.pc h
        change commitPc = u.pc at hp
        omega)
      have hvHi : v.pc ≤ setupCut.upper := by
        rw [show v.pc = setupCut.lower from hV.1]
        fin_cases stage <;> decide
      obtain ⟨w, setupPre, setupRest, setupPost, hSetupSplit, hw | hw, hWShape, hWRegs,
          hSetupWalk, hSetupMem, hSPre⟩ :=
        walkAtQueryCut setupCut hW hV.1.symm.le hvHi ⟨hVShape, hVRole⟩ hV.2.2.2.2
          (by intro r hr; rwa [List.map_cons, bankMap, ← hSetupKeep] at hr)
          hTail hSetupLate.le (show commitPc < 2768 by omega)
      · have hwAt : At w (qkPc (initialQkBlock stage) - 40) ((pred, .pred true) :: F) :=
          hSetupEnd ▸ queryCutAt hw hp₂ hWShape.1 hWRegs hSetupWalk hSetupMem hSetupLate
        let prior := pre ++ [⟨u.pc, .elect (2 ^ 32 - 1) inst leader⟩] ++ setupPre
        have hTrace : (X.tr g).drop pos = prior ++ setupRest := by
          rw [hSplit, hSetupSplit]
          simp [prior, List.append_assoc]
        have hEarlier : target ∉ prior := by
          intro hm
          simp only [prior, List.mem_append, List.mem_singleton, or_assoc] at hm
          rcases hm with h | h | h
          · have hh := hPre target h
            change commitPc < first.upper at hh
            omega
          · have hh := congrArg Event.pc h
            change commitPc = u.pc at hh
            omega
          · have hh := hSPre target h
            change commitPc < setupCut.upper at hh
            omega
        obtain ⟨hDrop, hLater⟩ := beforeCommitSuffix he hIndex hTrace hEarlier
        refine ⟨w, _, setupPost, hwAt, hWShape.2, hLater, hDrop.symm ▸ hSetupWalk,
          pos+pre.length,inst,leader,?_,hElect⟩
        simp [prior]
      · exact (noEarlierEventInExit hSetupWalk (by rw [hw]) (by rw [hw]; decide) hWShape
          hSetupMem (show commitPc < 2763 by omega)).elim
  · exact (noEarlierEventInExit hW (by rw [hu]) (by rw [hu]; decide) hUShape hRem
      (show commitPc < 2763 by omega)).elim

/-- The entry to one initial score issue bank records the elected lane and the actual Q words. -/
private structure PreparedQueryBank (l : Launch) (stage : Fin 2) (t : TState) : Prop where
  frame : At t (qkPc (initialQkBlock stage)) []
  role : t.regs 1062 = some (b32 12)
  guard : t.regs (qkGuard (initialQkBlock stage)) = some (.pred true)
  id : t.regs 9632 = some (b32 0x8200490)
  words : ∀ step : Fin 8, t.regs (9624 + step.val) =
    some (b64 (sharedDescriptorWord (qStart l stage + qkFragment step) 16))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem preparedQueryBank (stage : Fin 2) {g pos index commitPc : Nat}
    {spec : TcCommit.Spec} (hCommitSite : commitPc = 2642 ∨ commitPc = 2646 ∨ commitPc = 2274)
    (he : X.get (g, index) = some ⟨commitPc, .tc (.commit spec)⟩) {s : TState} {vs : List Visit}
    (hs : At s (queryElectionCut stage).lower (queryBankFacts l (if stage = 0 then 1 else 0)))
    (hRole : s.regs 1062 = some (b32 12)) (hIndex : pos ≤ index)
    (hWalk : Walk kernel Assumptions.all l g s ((X.tr g).drop pos) vs) :
    ∃ u nextPos visits, PreparedQueryBank l stage u ∧ nextPos ≤ index ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop nextPos) visits := by
  obtain ⟨w, nextPos, _, hw, hWRole, hLater, hRest, _⟩ :=
    querySetupOnCommitLane hp hX stage hCommitSite he hs hRole hIndex hWalk
  have hMem : (⟨commitPc, .tc (.commit spec)⟩ : Event) ∈ (X.tr g).drop nextPos := by
    apply List.mem_of_getElem? (i := index - nextPos)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hLater]
  have hEnd : qkPc (initialQkBlock stage) ≤ commitPc := by
    rcases hCommitSite with rfl | rfl | rfl <;> fin_cases stage <;> decide
  obtain ⟨u, visits, hRun, hu, hTail⟩ := querySetupRunBeforeEvent stage (hw.mono trivial)
    hRest hMem hEnd
  let regs := [1062, 9632, qkGuard (initialQkBlock stage)]
  have hKeep (r : Nat) (hr : r ∈ regs) : u.regs r = w.regs r :=
    Epilogue.schedulerLocalFrame (lo := qkPc (initialQkBlock stage) - 40) (len := 40)
      (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl)
      (by fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl) hRun hw.1.ge
      (by rw [hw.1]) hr
  have hWords := retargetQueryBank hp stage (hw.mono trivial) (fun step =>
    holds_mem hw.2.2.2.2.2.2 (List.mem_map.mpr ⟨step, List.mem_finRange step, rfl⟩)) hRun
  refine ⟨u, nextPos, visits, ⟨hu, (hKeep 1062 (by simp [regs])).trans hWRole, ?_, ?_, hWords⟩,
    hLater, hTail⟩
  · exact (hKeep _ (by simp [regs])).trans hw.2.2.2.2.1
  · exact (hKeep 9632 (by simp [regs])).trans hw.2.2.2.2.2.1

omit hp hX in
private theorem holdsRegisters {R : Nat → Option Value} {facts : List (Nat × Value)}
    (h : ∀ f ∈ facts, R f.1 = some f.2) : Holds R facts := by
  induction facts with
  | nil => trivial
  | cons f rest ih =>
    exact ⟨h f (by simp), ih (fun f hf => h f (List.mem_cons_of_mem _ hf))⟩

private theorem initialBanksBeforeCommit {g index commitPc : Nat} {spec : TcCommit.Spec}
    (hCommitSite : commitPc = 2642 ∨ commitPc = 2646 ∨ commitPc = 2274)
    (he : X.get (g, index) = some ⟨commitPc, .tc (.commit spec)⟩) (stage : Fin 2) :
    ∃ u pos visits, PreparedQueryBank l stage u ∧ pos ≤ index ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop pos) visits := by
  have hHint : commitPc ∉ registerHintSites := by
    rcases hCommitSite with rfl | rfl | rfl <;> decide
  have hRange := roleBodyPcOfEvent hp hX he (show 173 < commitPc by omega) hHint
  change roleBodyPc (warpIndex l g) commitPc at hRange
  have hWarp : warpIndex l g = 12 := by
    rcases hRange with h | h
    · change commitPc = 9205 at h
      omega
    · change (if 14 ≤ warpIndex l g then _ else _) at h
      split_ifs at h <;> omega
  obtain ⟨s, _, hIndex, hs, hRun⟩ := initialQueryBankBeforeEvent hp hX he hWarp
    (show 1916 < commitPc by omega) (by intro f h; cases h)
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  have hs' : At s (queryElectionCut 0).lower (queryBankFacts l 1) := hs.mono hs.2.2.2.2.2
  obtain ⟨u, pos, visits, hU, hPos, hTail⟩ :=
    preparedQueryBank hp hX 0 hCommitSite he hs' hs.2.2.2.2.1 hIndex hWalk
  fin_cases stage
  · exact ⟨u, pos, visits, hU, hPos, hTail⟩
  · have hu' : At u (queryElectionCut 1).lower (queryBankFacts l 0) := by
      refine hU.frame.mono ⟨hU.id, ?_⟩
      apply holdsRegisters
      intro f hf
      obtain ⟨step, _, rfl⟩ := List.mem_map.mp hf
      exact hU.words step
    exact preparedQueryBank hp hX 1 hCommitSite he hu' hU.role hPos hTail

/-- The first QK bank's real election precedes the observed final MMA commit. -/
theorem firstQkElectionBeforeFinalCommit {g index commitPc : Nat} {spec : TcCommit.Spec}
    (hw : warpIndex l g = 12) (hCommitSite : commitPc = 2642 ∨ commitPc = 2646)
    (he : X.get (g,index) = some ⟨commitPc,.tc (.commit spec)⟩) :
    ∃ election inst leader, election < index ∧
      X.Elect (g,election) 2153 (2^32-1) inst leader := by
  obtain ⟨s,_,hIndex,hs,hRun⟩ := initialQueryBankBeforeEvent hp hX he hw
    (show 1916 < commitPc by omega) (by intro f h; cases h)
  obtain ⟨_,hWalk⟩ := walkFromRun hRun
  have hs' : At s (queryElectionCut 0).lower (queryBankFacts l 1) := hs.mono hs.2.2.2.2.2
  obtain ⟨_,nextPos,_,_,_,hNext,_,election,inst,leader,hEarly,hElect⟩ :=
    querySetupOnCommitLane hp hX 0 (hCommitSite.imp id Or.inl) he hs' hs.2.2.2.2.1 hIndex hWalk
  exact ⟨election,inst,leader,hEarly.trans_le hNext,hElect⟩

/-- The final output issuer's real second score-bank election. -/
theorem secondQkElectionBeforeFinalCommit {g index commitPc : Nat} {spec : TcCommit.Spec}
    (hCommitSite : commitPc = 2642 ∨ commitPc = 2646)
    (he : X.get (g,index) = some ⟨commitPc,.tc (.commit spec)⟩) :
    ∃ election inst leader, election < index ∧
      X.Elect (g,election) 2215 (2^32-1) inst leader := by
  obtain ⟨u,pos,_,hU,hPos,hTail⟩ :=
    initialBanksBeforeCommit hp hX (hCommitSite.imp id Or.inl) he 0
  have hu : At u (queryElectionCut 1).lower (queryBankFacts l 0) := by
    refine hU.frame.mono ⟨hU.id,?_⟩
    apply holdsRegisters
    intro f hf
    obtain ⟨step,_,rfl⟩ := List.mem_map.mp hf
    exact hU.words step
  obtain ⟨_,nextPos,_,_,_,hNext,_,election,inst,leader,hEarly,hElect⟩ :=
    querySetupOnCommitLane hp hX 1 (hCommitSite.imp id Or.inl) he hu hU.role hPos hTail
  exact ⟨election,inst,leader,hEarly.trans_le hNext,hElect⟩

private theorem initialQueryOperandsBeforeCommit {g index commitPc : Nat} {spec : TcCommit.Spec}
    (hCommitSite : commitPc = 2642 ∨ commitPc = 2646 ∨ commitPc = 2274)
    (he : X.get (g, index) = some ⟨commitPc, .tc (.commit spec)⟩) (stage : Fin 2) :
    ∃ base, ∀ step : Fin 8, ∃ d op accum mask, base + step.val < index ∧
      X.get (g, base + step.val) =
        some ⟨qkPc (initialQkBlock stage) + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g stage step op := by
  obtain ⟨u, pos, visits, hU, hPos, hWalk⟩ := initialBanksBeforeCommit hp hX hCommitSite he stage
  refine ⟨pos, ?_⟩
  intro step
  have hStage : qkStage (initialQkBlock stage) = stage := Fin.ext (Nat.mod_eq_of_lt stage.isLt)
  have hWords := hU.words
  rw [← hStage] at hWords
  have hAfter : qkPc (initialQkBlock stage) + 8 ≤ commitPc := by
    rcases hCommitSite with rfl | rfl | rfl <;> fin_cases stage <;> decide
  obtain ⟨d, op, accum, mask, hBefore, hIssue, hOperand⟩ :=
    queryBankOperandsBeforeEvent hp hX (initialQkBlock stage) hU.frame hU.guard hU.id
      hWords hWalk hPos he hAfter step
  exact ⟨d, op, accum, mask, hBefore, hIssue, hStage ▸ hOperand⟩

/-- The actual final output issuer executed all eight A fragments of each initial Q bank. -/
theorem initialQueryOperandsBeforeFinalCommit {g index commitPc : Nat} {spec : TcCommit.Spec}
    (hCommitSite : commitPc = 2642 ∨ commitPc = 2646)
    (he : X.get (g, index) = some ⟨commitPc, .tc (.commit spec)⟩) (stage : Fin 2) :
    ∃ base, ∀ step : Fin 8, ∃ d op accum mask, base + step.val < index ∧
      X.get (g, base + step.val) =
        some ⟨qkPc (initialQkBlock stage) + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g stage step op :=
  initialQueryOperandsBeforeCommit hp hX (hCommitSite.imp id Or.inl) he stage

/-- The startup key slot release follows all fragments of each initial QK bank. -/
theorem initialQueryOperandsBeforeFirstKeyRelease {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g,index) = some ⟨(commitSite (releaseCommitSite 0)).pc, .tc (.commit spec)⟩)
    (stage : Fin 2) :
    ∃ base, ∀ step : Fin 8, ∃ d op accum mask, base + step.val < index ∧
      X.get (g, base + step.val) =
        some ⟨qkPc (initialQkBlock stage) + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g stage step op :=
  initialQueryOperandsBeforeCommit hp hX (.inr (.inr rfl)) he stage

/-- The actual first output issuer executed all eight fragments of each initial Q bank. -/
theorem initialQueryOperandsBeforeOutputCommit {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2642, .tc (.commit spec)⟩) (stage : Fin 2) :
    ∃ base, ∀ step : Fin 8, ∃ d op accum mask, base + step.val < index ∧
      X.get (g, base + step.val) =
        some ⟨qkPc (initialQkBlock stage) + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g stage step op :=
  initialQueryOperandsBeforeFinalCommit hp hX (.inl rfl) he stage

/-- The lane whose retained output commit was actually observed issued the first QK fragment.
The decoded A footprint applies to all rows of the first fragment. -/
theorem firstQueryOperandFragmentBeforeOutputCommitOfPrefix {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2642, .tc (.commit spec)⟩) :
    ∃ mma < index, ∃ d op accum mask, X.get (g, mma) =
      some ⟨2197, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g 0 0 op ∧
      ∀ byte < 4, op.byteLoc .a byte = some ⟨.shared, g / l.block,
        l.sharedBase + 3072 + byte⟩ := by
  obtain ⟨pos, hBank⟩ := initialQueryOperandsBeforeOutputCommit hp hX he 0
  obtain ⟨d, op, accum, mask, hBefore, hIssue, hOperand⟩ := hBank 0
  refine ⟨pos, hBefore, d, op, accum, mask, hIssue, hOperand, ?_⟩
  intro byte hByte
  have hLoc := correctionQueryByteLoc hp (writer := g) (x := 0) (row := 0)
    (subbox := 0) rfl (by decide) (by decide) hByte (by
      have hStep : correctionQueryFragment 0 0 byte (by decide) hByte = 0 := by
        apply Fin.ext
        change 4 * (0 % 2) + (4 * 0 + byte) / 32 = 0
        omega
      rw [hStep]
      exact hOperand)
  have hIndex : correctionQueryByte 0 0 byte = byte := by
    unfold correctionQueryByte
    omega
  simpa [hIndex, Correction.outputElementAccess, Correction.outputChunkLoc,
    Epilogue.sharedSlot, Loc.at] using hLoc

end
end PTX.Kernels.TmlFa4Fwd.Mma
