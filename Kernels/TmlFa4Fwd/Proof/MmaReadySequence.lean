-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadySegments
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyBarriers

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Prologue

noncomputable section

def readyOperand (l : Launch) (g use : Nat) : Loc × Nat :=
  (initObject l (g / l.block) (readySlot (readyStage use)), readyWord use)

/-- Any finite sequence of successful ready observations begins at the given ring use. -/
inductive ReadySequence (l : Launch) (g : Nat) : Nat → List (Loc × Nat) → Prop
  | nil (use : Nat) : ReadySequence l g use []
  | next {use : Nat} {rest : List (Loc × Nat)} :
      ReadySequence l g (use + 1) rest → ReadySequence l g use (readyOperand l g use :: rest)

/-- The K0 gate starts the ring. Subsequent physical K and V gates alternate. -/
def ReadyUseSite (use pc : Nat) : Prop :=
  (pc = readyHead 0 ∧ use = 0) ∨ (pc = readyHead 2 ∧ 0 < use ∧ use % 2 = 0) ∨
    ((pc = readyHead 1 ∨ pc = readyHead 3) ∧ use % 2 = 1)

def readyEventTagged (e : Event) : Option (Nat × (Loc × Nat)) :=
  (readyEvent e).map (fun payload => (e.pc, payload))

/-- The ready sequence also retains which decoded gate consumed each use. -/
inductive TaggedReadySequence (l : Launch) (g : Nat) :
    Nat → List (Nat × (Loc × Nat)) → Prop
  | nil (use : Nat) : TaggedReadySequence l g use []
  | next {use pc : Nat} {rest : List (Nat × (Loc × Nat))} :
      ReadyUseSite use pc → TaggedReadySequence l g (use + 1) rest →
      TaggedReadySequence l g use ((pc, readyOperand l g use) :: rest)

theorem TaggedReadySequence.erase {l : Launch} {g use : Nat}
    {es : List (Nat × (Loc × Nat))} (h : TaggedReadySequence l g use es) :
    ReadySequence l g use (es.map Prod.snd) := by
  induction h with
  | nil => exact .nil _
  | next _ _ ih => exact .next ih

theorem taggedProjectionErase (es : List Event) :
    (es.filterMap readyEventTagged).map Prod.snd = es.filterMap readyEvent := by
  induction es with
  | nil => rfl
  | cons e es ih => cases he : readyEvent e <;> simp [readyEventTagged, he, ih]

/-- A cache-ready attempt records the actual gate and operands on both outcomes. -/
def readyAttemptEvent (e : Event) : Option (Bool × (Nat × (Loc × Nat))) :=
  match e.kind with
  | .wait loc parity ok _ _ =>
    if (List.finRange 4).any (fun i => readyHead i == e.pc)
    then some (ok, (e.pc, (loc, parity))) else none
  | _ => none

/-- A failed attempt keeps its ring use. A successful attempt consumes it. -/
inductive ReadyAttemptSequence (l : Launch) (g : Nat) :
    Nat → List (Bool × (Nat × (Loc × Nat))) → Prop
  | nil (use : Nat) : ReadyAttemptSequence l g use []
  | retry {use pc : Nat} {rest : List (Bool × (Nat × (Loc × Nat)))} :
      ReadyUseSite use pc → ReadyAttemptSequence l g use rest →
      ReadyAttemptSequence l g use ((false, (pc, readyOperand l g use)) :: rest)
  | acquire {use pc : Nat} {rest : List (Bool × (Nat × (Loc × Nat)))} :
      ReadyUseSite use pc → ReadyAttemptSequence l g (use + 1) rest →
      ReadyAttemptSequence l g use ((true, (pc, readyOperand l g use)) :: rest)

def successfulReadyAttempt (a : Bool × (Nat × (Loc × Nat))) : Option (Nat × (Loc × Nat)) :=
  if a.1 then some a.2 else none

theorem ReadyAttemptSequence.erase {l : Launch} {g use : Nat}
    {es : List (Bool × (Nat × (Loc × Nat)))} (h : ReadyAttemptSequence l g use es) :
    TaggedReadySequence l g use (es.filterMap successfulReadyAttempt) := by
  induction h with
  | nil => exact .nil _
  | retry _ _ ih => exact ih
  | acquire hSite _ ih => exact .next hSite ih

theorem readyAttemptProjection (es : List Event) :
    (es.filterMap readyAttemptEvent).filterMap successfulReadyAttempt =
      es.filterMap readyEventTagged := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    obtain ⟨pc, kind⟩ := a
    cases kind <;> try exact ih
    rename_i loc phase ok acq scope
    cases ok <;> by_cases h : ((List.finRange 4).any fun i => readyHead i == pc) = true <;>
      simp [List.filterMap_cons, readyAttemptEvent, readyEventTagged, readyEvent,
        successfulReadyAttempt, h, ih]

/-- The number of successful attempts already seen determines the ring operands. -/
theorem ReadyAttemptSequence.get {l : Launch} {g use index pc : Nat}
    {events : List (Bool × (Nat × (Loc × Nat)))} {ok : Bool} {operand : Loc × Nat}
    (h : ReadyAttemptSequence l g use events) (he : events[index]? = some (ok, (pc, operand))) :
    let current := use + ((events.take index).filterMap successfulReadyAttempt).length
    ReadyUseSite current pc ∧ operand = readyOperand l g current := by
  induction h generalizing index with
  | nil => simp at he
  | retry hSite _ ih =>
    cases index with
    | zero =>
      obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj he
      exact ⟨hSite,rfl⟩
    | succ index =>
      rw [List.getElem?_cons_succ] at he
      simpa [List.filterMap_cons, successfulReadyAttempt] using ih he
  | acquire hSite _ ih =>
    cases index with
    | zero =>
      obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj he
      exact ⟨hSite,rfl⟩
    | succ index =>
      rw [List.getElem?_cons_succ] at he
      simpa [List.filterMap_cons, successfulReadyAttempt, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih he

private theorem readyAttemptOutside (i : Fin 9) {e : Event}
    (hPc : (readyInterval i).lo ≤ e.pc ∧ e.pc < (readyInterval i).hi) :
    readyAttemptEvent e = none := by
  simp [readyAttemptEvent, readyIntervalNoHead i hPc]
  split <;> rfl

private theorem atIntervalExit (i : Fin 9) {s : TState}
    {F : List (Nat × Value)} (hp : s.pc ∈ (readyInterval i).exits)
    (hf : s.fault = none) (hs : RoleShape s) (hF : Holds s.regs F) : At s s.pc F := by
  have hNo : ∀ pc ∈ (readyInterval i).exits, pc ≠ 1909 := by
    fin_cases i <;> simp [readyInterval]
  exact ⟨rfl, hs.2.2 (hNo _ hp), hs.2.1, hf, hF⟩

private theorem intervalSequence (i : Fin 9) {l : Launch} {g use : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hPc : (readyInterval i).lo ≤ s.pc ∧ s.pc < (readyInterval i).hi)
    (hs : At s s.pc F) (hWarp : (1062, b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u tail post}, u.pc ∈ (readyInterval i).exits → At u u.pc F →
      post.length < vs.length → Walk kernel Assumptions.all l g u tail post →
      ReadyAttemptSequence l g use (tail.filterMap readyAttemptEvent)) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  rcases readyIntervalCutWith readyAttemptEvent i (fun _ he => readyAttemptOutside i he) hw hPc
      ⟨hShape, holds_mem hs.2.2.2.2 hWarp⟩
      hs.2.2.2.2 hKeep with h | ⟨u, pre, tail, post, hE, hP, hL, hX, hF, hS, hH, hw'⟩
  · rw [h]
    exact .nil _
  · rw [hE, List.filterMap_append, hP, List.nil_append]
    exact after hX (atIntervalExit i hX hF hS.1 hH) hL hw'

private theorem segmentSequence {l : Launch} {g use pc nextPc n : Nat} {s : TState}
    {F G : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hSeg : Seg kernel Assumptions.all l g n pc F nextPc G) (ht : At s pc F)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (after : ∀ {u post}, At u nextPc G → post.length ≤ vs.length →
      Walk kernel Assumptions.all l g u es post →
      ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent)) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  obtain ⟨u, hr, hu⟩ := hSeg s ht
  rcases advanceWalkLocals hr hw with rfl | ⟨post, hLen, _, hWalk⟩
  · exact .nil _
  · exact after hu (by omega) hWalk

private def canonicalReadyWait : Fin 4 → Fin 14
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 9

private theorem readyWaitIndex (i : Fin 4) :
    (waitSite (canonicalReadyWait i)).pc = readyHead i := by
  fin_cases i <;> decide

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
include hp

private theorem readyPollSequence (i : Fin 4) {g use : Nat} {t : TState} {F : List (Nat × Value)}
    (hUse : ReadyUseSite use (readyHead i)) {es : List Event} {vs : List Visit}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite (canonicalReadyWait i)).result)
    (hBase : ((waitSite (canonicalReadyWait i)).base, b32 (readyAddr l use)) ∈ F)
    (hPar : ((waitSite (canonicalReadyWait i)).phase, b32 (readyWord use)) ∈ F)
    (ht : At t (waitSite (canonicalReadyWait i)).pc F)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (after : ∀ {u rest post}, post.length < vs.length →
      At u ((waitSite (canonicalReadyWait i)).pc + 3) F →
      Walk kernel Assumptions.all l g u rest post →
      ReadyAttemptSequence l g (use + 1) (rest.filterMap readyAttemptEvent)) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  have hAddr : readyAddr l use < 2 ^ 32 := by
    have h := hp.shared.2.1
    have hSlot := (readyStage use).isLt
    unfold readyAddr
    omega
  have hAlign : readyAddr l use % 8 = 0 := by
    have h := hp.shared.1
    unfold readyAddr
    omega
  let ev := fun ok => Event.mk (waitSite (canonicalReadyWait i)).pc
    (.wait ⟨.shared, g / l.block, readyAddr l use⟩ (readyWord use) ok true .cta)
  have hMark (ok : Bool) : readyAttemptEvent (ev ok) =
      some (ok, (readyHead i, readyOperand l g use)) := by
    have hi : (List.finRange 4).any (fun j => readyHead j == readyHead i) = true :=
      List.any_eq_true.mpr ⟨i, by simp, beq_self_eq_true _⟩
    simp [readyAttemptEvent, readyOperand, readySlot_address, readyAddr, Nat.add_assoc,
      ev, readyWaitIndex, hi]
  have hRetries (n : Nat) {rest : List (Bool × (Nat × (Loc × Nat)))}
      (h : ReadyAttemptSequence l g use rest) :
      ReadyAttemptSequence l g use
        ((List.replicate n (ev false)).filterMap readyAttemptEvent ++ rest) := by
    induction n with
    | zero => exact h
    | succ n ih =>
      rw [List.replicate_succ, List.filterMap_cons, hMark false, List.cons_append]
      exact .retry hUse ih
  rcases waitWalk (canonicalReadyWait i) hAddr hAlign (readyWord_lt use) hFresh hBase hPar
      ht hw with ⟨n, hEq⟩ | ⟨n, rest, hEq, hTail⟩
  · change es = List.replicate n (ev false) at hEq
    rw [hEq, ← List.append_nil ((List.replicate n (ev false)).filterMap readyAttemptEvent)]
    exact hRetries n (.nil _)
  · change es = List.replicate n (ev false) ++ ev true :: rest at hEq
    rw [hEq, List.filterMap_append, List.filterMap_cons, hMark true]
    apply hRetries n
    apply ReadyAttemptSequence.acquire hUse
    rcases hTail with rfl | ⟨u, post, hL, hu, hw'⟩
    · exact .nil _
    · exact after hL hu hw'

omit hp in
private theorem finalReadySequence {l : Launch} {g use : Nat} {t : TState}
    {es : List Event} {vs : List Visit} (hPc : 2548 ≤ t.pc ∧ t.pc < 2768)
    (ht : At t t.pc [(1062, b32 12)]) (hw : Walk kernel Assumptions.all l g t es vs) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  apply intervalSequence 8 hPc ht (by simp) (by decide) hw
  intro u tail post hExit hu _ hWalk
  have hPc : u.pc = 3099 := by simpa [readyInterval] using hExit
  have hEvents := mmaEpilogueExitEvents hPc hu.2.2.2.1 (.inl rfl) hu.2.2.2.2.1 hWalk
  have hEmpty : tail.filterMap readyAttemptEvent = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have h := hEvents e he
    obtain ⟨pc, kind⟩ := e
    dsimp only at h
    subst pc
    cases kind <;> rfl
  rw [hEmpty]
  exact .nil _

private theorem tailReadySequence {g use : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hOdd : use % 2 = 1) (ht : At t 2534 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g t es vs) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  apply intervalSequence 7 (by rw [ht.1]; decide) ⟨rfl, ht.2⟩
    (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hu' : At u 2542 (ringFrame l 7207 7208 use) :=
    ⟨by simpa [readyInterval] using hExit, hu.2⟩
  apply segmentSequence (readyAddress hp g 2 use) hu' hw'
  intro v visits hv _ hw''
  apply readyPollSequence hp 3 (.inr (.inr ⟨.inr rfl, hOdd⟩))
    (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
    (by simp [canonicalReadyWait, waitSite, readyAddressSite])
    (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame]) hv hw''
  intro w rest wVisits _ hz hw'''
  exact finalReadySequence (use := use + 1) (by rw [hz.1]; decide)
    ⟨rfl, (by at_select hz : At w 2548 [(1062, b32 12)]).2⟩ hw'''

private theorem steadyReadySequence {g use : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (hOdd : use % 2 = 1) (ht : At t 2291 (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g t es vs) :
    ReadyAttemptSequence l g use (es.filterMap readyAttemptEvent) := by
  generalize hLen : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing use t es vs with
  | h fuel ih =>
    apply segmentSequence (readyAddress hp g 0 use) ht hw
    intro w₁ v₁ hAt₁ hLen₁ hw₁
    apply readyPollSequence hp 1 (.inr (.inr ⟨.inl rfl, hOdd⟩))
      (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [canonicalReadyWait, waitSite, readyAddressSite])
      (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame]) hAt₁ hw₁
    intro w₂ es₂ v₂ hLen₂ hAt₂ hw₂
    have hAt₂' : At w₂ (2297 : Nat) (ringFrame l 7207 7208 use) := ⟨hAt₂.1, hAt₂.2.1,
      hAt₂.2.2.1, hAt₂.2.2.2.1, hAt₂.2.2.2.2.2⟩
    apply intervalSequence 4 (by rw [hAt₂'.1]; decide) ⟨rfl, hAt₂'.2⟩
      (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw₂
    intro w₃ es₃ v₃ hExit₃ hAt₃ hLen₃ hw₃
    have hAt₃' : At w₃ 2344 (ringFrame l 7207 7208 use) :=
      ⟨by simpa [readyInterval] using hExit₃, hAt₃.2⟩
    apply segmentSequence (readyAdvanceFramed l g 0 use) hAt₃' hw₃
    intro w₄ v₄ hAt₄ hLen₄ hw₄
    apply segmentSequence (readyAddress hp g 1 (use + 1)) hAt₄ hw₄
    intro w₅ v₅ hAt₅ hLen₅ hw₅
    apply readyPollSequence hp 2 (.inr (.inl ⟨rfl, by omega, by omega⟩))
      (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame, readyFrame])
      (by simp [canonicalReadyWait, waitSite, readyAddressSite])
      (by simp [canonicalReadyWait, waitSite, readyAddressSite, ringFrame]) hAt₅ hw₅
    intro w₆ es₆ v₆ hLen₆ hAt₆ hw₆
    have hAt₆' : At w₆ 2355 (ringFrame l 1192 2572 (use + 1)) := ⟨hAt₆.1, hAt₆.2.1,
      hAt₆.2.2.1, hAt₆.2.2.2.1, hAt₆.2.2.2.2.2⟩
    apply intervalSequence 5 (by rw [hAt₆'.1]; decide) ⟨rfl, hAt₆'.2⟩
      (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw₆
    intro w₇ es₇ v₇ hExit₇ hAt₇ hLen₇ hw₇
    have hAt₇' : At w₇ 2524 (ringFrame l 1192 2572 (use + 1)) :=
      ⟨by simpa [readyInterval] using hExit₇, hAt₇.2⟩
    apply segmentSequence (readyAdvanceFramed l g 1 (use + 1)) hAt₇' hw₇
    intro w₈ v₈ hAt₈ hLen₈ hw₈
    apply intervalSequence 6 (by rw [hAt₈.1]; decide) ⟨rfl, hAt₈.2⟩
      (by simp [ringFrame, readyFrame, readyAdvanceSite])
      (by simp [ringFrame, readyFrame, readyAdvanceSite, readyInterval]) hw₈
    intro w₉ es₉ v₉ hExit₉ hAt₉ hLen₉ hw₉
    have hExit : w₉.pc = 2291 ∨ w₉.pc = 2534 := by simpa [readyInterval] using hExit₉
    rcases hExit with hPc | hPc
    · exact ih v₉.length (by omega) (by omega) ⟨hPc, hAt₉.2⟩ hw₉ rfl
    · exact tailReadySequence hp (by omega) ⟨hPc, hAt₉.2⟩ hw₉

private theorem afterFirstReady {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 2148 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    ReadyAttemptSequence l g 1 (es.filterMap readyAttemptEvent) := by
  apply intervalSequence 2 (by rw [ht.1]; decide) ⟨rfl, ht.2⟩
    (by simp [readyFrame])
    (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hu' : At u 2280 (readyFrame l) := ⟨by simpa [readyInterval] using hExit, hu.2⟩
  apply segmentSequence (readySeedShort l g) hu' hw'
  intro v visits hv _ hw''
  apply intervalSequence 3 (by rw [hv.1]; decide) ⟨rfl, hv.2⟩
    (by simp [ringFrame, readyFrame])
      (by simp [ringFrame, readyFrame, readyInterval]) hw''
  intro w rest wVisits hExit hwAt _ hWalk
  have hPc : w.pc = 2287 ∨ w.pc = 2534 := by simpa [readyInterval] using hExit
  rcases hPc with hSteady | hTail
  · have hSeed : At w 2287 (readyFrame l) :=
      ⟨hSteady, hwAt.2.1, hwAt.2.2.1, hwAt.2.2.2.1, hwAt.2.2.2.2.2.2⟩
    apply segmentSequence (readySeedSteady l g) hSeed hWalk
    intro z post hz _ hW
    exact steadyReadySequence hp (by decide) hz hW
  · exact tailReadySequence hp (by decide) ⟨hTail, hwAt.2⟩ hWalk

/-- Every finite MMA-body walk consumes the prescribed ready attempts. -/
theorem readyAttemptSequenceFromEntry {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g t es vs) :
    ReadyAttemptSequence l g 0 (es.filterMap readyAttemptEvent) := by
  apply intervalSequence 0 (by rw [ht.1]; decide) ⟨rfl, ht.2⟩
    (by simp [readyFrame])
    (by simp [readyFrame, readyInterval]) hw
  intro u tail post hExit hu _ hw'
  have hPc : u.pc = 2140 ∨ u.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hPc with hInit | hSkip
  · apply segmentSequence (readyInitialPhase l g) ⟨hInit, hu.2⟩ hw'
    intro v visits hv _ hw''
    apply intervalSequence 1 (by rw [hv.1]; decide) ⟨rfl, hv.2⟩
      (by simp [readyFrame])
      (by simp [readyFrame, readyInterval]) hw''
    intro w rest wVisits hExit hwAt _ hw'''
    have hwAt' : At w 2144 ((2536, b32 0) :: readyFrame l) :=
      ⟨by simpa [readyInterval] using hExit, hwAt.2⟩
    apply segmentSequence (readyInitialAddress hp g) hwAt' hw'''
    intro z zVisits hz _ hzWalk
    apply readyPollSequence hp 0 (.inl ⟨rfl, rfl⟩)
      (by simp [canonicalReadyWait, waitSite, readyFrame])
      (by simp [canonicalReadyWait, waitSite, readyAddr, readyStage, MbarRing.Index.slot])
      (by simp [canonicalReadyWait, waitSite, readyWord, MbarRing.Index.round]) hz hzWalk
    intro f suffix fVisits _ hf hWalk
    have hf' : At f 2148 (readyFrame l) :=
      ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2⟩
    exact afterFirstReady hp hf' hWalk
  · exact finalReadySequence (use := 0) (by rw [hSkip]; decide)
      (by at_select hu) hw'

end
end PTX.Kernels.TmlFa4Fwd.Mma
