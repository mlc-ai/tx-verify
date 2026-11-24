-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The final MMA gates that release a query stage or make an output stage available. -/
inductive TerminalCommit where
  | query (stage : Fin 2)
  | output (stage : Fin 2)

def TerminalCommit.site : TerminalCommit → Fin 12
  | .query stage => queryReleaseSite stage
  | .output stage => if stage = 0 then 10 else 11

def TerminalCommit.pc (gate : TerminalCommit) : Nat := (commitSite gate.site).pc

private theorem terminalLeader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (gate : TerminalCommit) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨gate.pc, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader,
      X.Elect (g, index - 1) (electSite (commitElection gate.site)).pc
        (2 ^ 32 - 1) inst leader ∧ laneOf l g = leader := by
  cases gate with
  | query stage => exact queryReleaseLeader hp hX stage he
  | output stage =>
    fin_cases stage
    · exact firstOutputCommitLeader hp hX he
    · exact secondOutputCommitLeader hp hX he

private theorem releaseRange (gate : TerminalCommit) : 2145 ≤ gate.pc ∧ gate.pc < 2768 := by
  cases gate with
  | query stage => fin_cases stage <;> decide
  | output stage => fin_cases stage <;> decide

private def floorCode (floor : Nat) (op : Op) : Bool :=
  (op.isLocal || linearEventOp op) && match op with
  | .bra dst _ => decide (floor ≤ dst)
  | .brx .. => false
  | _ => true

private theorem floorCodeChecked (gate : TerminalCommit) {pc : Nat} {ins : Instr}
    (hLo : gate.pc < pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    floorCode (gate.pc + 1) ins.op = true := by
  let floor := gate.pc + 1
  let code := (kernel.code.drop floor).take (2768 - floor)
  have ha : code.all (fun i => floorCode floor i.op) = true := by
    cases gate with
    | query stage => fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
    | output stage => fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  have hm : code[pc - floor]? = some ins := by
    dsimp only [code]
    have hFloor : floor ≤ pc := hLo
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hFloor]
    exact hc
  exact List.all_eq_true.mp ha ins (List.mem_of_getElem? hm)

private theorem nextAboveRelease (gate : TerminalCommit) {l : Launch} {g : Nat}
    {s u : TState} {e : Option Event} (hLo : gate.pc < s.pc) (hHi : s.pc < 2768)
    (hShape : RoleShape s) (hStep : WStep kernel Assumptions.all l g s e u) :
    gate.pc < u.pc := by
  have hRange := releaseRange gate
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, hEvent⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have ha := floorCodeChecked gate hLo hHi hc
    rcases tau_core_frame hc hCore with rfl | hf
    · change gate.pc < s.pc + 1
      omega
    have hPc := hf.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst aligned =>
      have hd : gate.pc + 1 ≤ dst := by
        simpa [floorCode, ho] using (Bool.and_eq_true_iff.mp ha).2
      omega
    case brx => simp [floorCode, ho] at ha
    all_goals omega
  · obtain ⟨ins, hc, hloc, _⟩ := estep_event_source hEvent
    have he : linearEventOp ins.op = true := by
      simpa [floorCode, hloc] using (Bool.and_eq_true_iff.mp (floorCodeChecked gate hLo hHi hc)).1
    obtain ⟨_, _, hadv | hsub | hf⟩ := linearEventProgress hc he hShape.1 hShape.2.1 hEvent
    · omega
    · omega
    · omega

private theorem terminalCommitAdvances (gate : TerminalCommit) {l : Launch} {g : Nat} {s u : TState}
    {sp : TcCommit.Spec}
    (he : EStep kernel Assumptions.all l g s ⟨gate.pc, .tc (.commit sp)⟩ (some u)) :
    u.pc = gate.pc + 1 := by
  have hPc : gate.pc = s.pc := estep_source_pc he
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [← hPc] at hc
  have expected : ∃ base off, kernel.code[gate.pc]? =
      some ⟨none, .tcCommit .one base off none⟩ := by
    cases gate with
    | query stage =>
      fin_cases stage
      · exact ⟨_, _, Flow.code_2537⟩
      · exact ⟨_, _, Flow.code_2541⟩
    | output stage =>
      fin_cases stage
      · exact ⟨_, _, Flow.code_2642⟩
      · exact ⟨_, _, Flow.code_2646⟩
  obtain ⟨base, off, hCode⟩ := expected
  rw [hCode] at hc
  obtain rfl := Option.some.inj hc.symm
  obtain rfl := fires_tcCommit hf
  exact congrArg (· + 1) hPc.symm

private theorem noReleaseInSuffix (gate : TerminalCommit) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hLo : gate.pc < s.pc) (hHi : s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (e : Event) (he : e ∈ es) : e.pc ≠ gate.pc := by
  have hRange := releaseRange gate
  induction hWalk with
  | stop => simp at he
  | @tau t u es vs ht hw ih =>
    have hStep : WStep kernel Assumptions.all l g t none u := .inl ⟨rfl, ht⟩
    obtain ⟨hin | ⟨hx, hf⟩, hs⟩ := mmaCutStep (by omega) hHi hStep hShape
    · exact ih (nextAboveRelease gate hLo hHi hShape.1 hStep) hin.2 hs he
    · have h := mmaEpilogueExitEvents (by simpa using hx) hf (.inl rfl) hs.2 hw e he
      omega
  | @ev t u actual es vs ht hw ih =>
    rcases List.mem_cons.mp he with rfl | ht'
    · have hPc := estep_source_pc ht
      omega
    have hStep : WStep kernel Assumptions.all l g t (some actual) u := .inr ⟨_, rfl, ht⟩
    obtain ⟨hin | ⟨hx, hf⟩, hs⟩ := mmaCutStep (by omega) hHi hStep hShape
    · exact ih (nextAboveRelease gate hLo hHi hShape.1 hStep) hin.2 hs ht'
    · have h := mmaEpilogueExitEvents (by simpa using hx) hf (.inl rfl) hs.2 hw e ht'
      omega
  | last ht =>
    obtain rfl := List.mem_singleton.mp he
    have hPc := estep_source_pc ht
    omega

private theorem atMostOneRelease (gate : TerminalCommit) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s es vs) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    {i j : Nat} {a b : TcCommit.Spec} (hij : i ≤ j)
    (ha : es[i]? = some ⟨gate.pc, .tc (.commit a)⟩)
    (hb : es[j]? = some ⟨gate.pc, .tc (.commit b)⟩) : i = j := by
  have hRange := releaseRange gate
  induction hWalk generalizing i j with
  | stop => simp at ha
  | @tau t u es vs ht hw ih =>
    obtain ⟨hin | ⟨hx, hf⟩, hs⟩ := mmaCutStep hPc.1 hPc.2 (.inl ⟨rfl, ht⟩) hShape
    · exact ih hin hs hij ha hb
    · have h := mmaEpilogueExitEvents (by simpa using hx) hf (.inl rfl) hs.2 hw _
        (List.mem_of_getElem? ha)
      change gate.pc = 9205 at h
      omega
  | @ev t u actual es vs ht hw ih =>
    obtain ⟨hin | ⟨hx, hf⟩, hs⟩ := mmaCutStep hPc.1 hPc.2 (.inr ⟨_, rfl, ht⟩) hShape
    · cases i with
      | zero =>
        obtain rfl := Option.some.inj ha
        cases j with
        | zero => rfl
        | succ j =>
          have hAfter := terminalCommitAdvances gate ht
          have hNot := noReleaseInSuffix gate hw (by omega) hin.2 hs ⟨_, _⟩
            (List.mem_of_getElem? hb)
          exact (hNot rfl).elim
      | succ i =>
        cases j with
        | zero => omega
        | succ j => exact congrArg Nat.succ (ih hin hs (by omega) ha hb)
    · cases j with
      | zero => omega
      | succ j =>
        have h := mmaEpilogueExitEvents (by simpa using hx) hf (.inl rfl) hs.2 hw _
          (List.mem_of_getElem? hb)
        change gate.pc = 9205 at h
        omega
  | last _ =>
    have hi := (List.getElem?_eq_some_iff.mp ha).1
    have hj := (List.getElem?_eq_some_iff.mp hb).1
    simp only [List.length_singleton] at hi hj
    omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Each MMA lane can issue a given terminal commit only once. -/
private theorem terminalCommitOnceInLane (gate : TerminalCommit) {g i j : Nat} {a b : TcCommit.Spec}
    (hij : i ≤ j) (ha : X.get (g,i) = some ⟨gate.pc, .tc (.commit a)⟩)
    (hb : X.get (g,j) = some ⟨gate.pc, .tc (.commit b)⟩) :
    i = j := by
  have hRange := releaseRange gate
  obtain ⟨pos, s, vs, hi, hs, hw⟩ := initialMmaTrace hp hX ha hRange.1 hRange.2
  have ha' : ((X.tr g).drop (pos + 1))[i - (pos + 1)]? =
      some ⟨gate.pc, .tc (.commit a)⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact ha
  have hb' : ((X.tr g).drop (pos + 1))[j - (pos + 1)]? =
      some ⟨gate.pc, .tc (.commit b)⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (show pos + 1 ≤ j by omega)]
    exact hb
  have hShape : RoleShape s := ⟨by rw [hs.2.1]; decide, hs.2.2.1, fun _ => hs.2.1⟩
  have hEq := atMostOneRelease gate hw (by rw [hs.1]; decide)
    ⟨hShape, hs.2.2.2.2.1⟩ (by omega) ha' hb'
  omega

/-- Each terminal commit has at most one actual issuer and occurrence in its CTA. -/
theorem terminalCommitUnique (gate : TerminalCommit) {i j : EvId} {a b : TcCommit.Spec}
    (hCta : i.1 / l.block = j.1 / l.block) (ha : X.get i = some ⟨gate.pc, .tc (.commit a)⟩)
    (hb : X.get j = some ⟨gate.pc, .tc (.commit b)⟩) :
    i = j := by
  have warp {f : EvId} {sp : TcCommit.Spec}
      (he : X.get f = some ⟨gate.pc, .tc (.commit sp)⟩) :
      Prologue.warpIndex l f.1 = 12 := by
    have hBounds : 2145 ≤ gate.pc ∧ gate.pc < 2768 ∧
        gate.pc ∉ registerHintSites := by
      cases gate with
      | query stage => fin_cases stage <;> decide
      | output stage => fin_cases stage <;> decide
    have hBody : roleBodyPc (Prologue.warpIndex l f.1) (gate.pc) :=
      roleBodyPcOfEvent hp hX he (by change 173 < gate.pc; omega) hBounds.2.2
    rcases hBody with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨g, ai⟩ := i
  obtain ⟨h, bi⟩ := j
  have hWarp : SameWarp l g h := ⟨⟨event_thread_lt hX ha, event_thread_lt hX hb, hCta⟩,
    (warp ha).trans (warp hb).symm⟩
  obtain ⟨_, _, al, hElect, haLane⟩ := terminalLeader hp hX gate ha
  obtain ⟨_, _, bl, hElect', hbLane⟩ := terminalLeader hp hX gate hb
  have hThread := sameWarp_eq_of_lane_eq hWarp
    (haLane.trans ((PTX.Kernels.TmlFa4Fwd.Mma.sameLeader hX hWarp hElect hElect').trans
      hbLane.symm))
  subst h
  apply Prod.ext (x := (g, ai)) (y := (g, bi)) rfl
  rcases Nat.le_total ai bi with hab | hba
  · exact terminalCommitOnceInLane hp hX gate hab ha hb
  · exact (terminalCommitOnceInLane hp hX gate hba hb ha).symm

/-- Each MMA lane can issue a given query release only once. -/
theorem queryReleaseOnceInLane (stage : Fin 2) {g i j : Nat} {a b : TcCommit.Spec} (hij : i ≤ j)
    (ha : X.get (g, i) = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit a)⟩)
    (hb : X.get (g, j) = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit b)⟩) :
    i = j :=
  terminalCommitOnceInLane hp hX (.query stage) hij ha hb

/-- Each query release has at most one actual issuer and occurrence in each CTA. -/
theorem queryReleaseEventUnique (stage : Fin 2) {i j : EvId} {a b : TcCommit.Spec}
    (hCta : i.1 / l.block = j.1 / l.block)
    (ha : X.get i = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit a)⟩)
    (hb : X.get j = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit b)⟩) :
    i = j :=
  terminalCommitUnique hp hX (.query stage) hCta ha hb

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
