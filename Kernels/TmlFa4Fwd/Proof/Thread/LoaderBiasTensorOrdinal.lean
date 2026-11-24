-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorGuard
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasWaitHistory
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.Flow PTX.MBarrier PTX.Kernels.TmlFa4Fwd.Loader

/-- A half is counted by its actual stage barrier and destination. -/
def biasTensorHalf (l : Launch) (cta : Nat) (stage half : Fin 2) (e : Event) : Bool :=
  match e.kind with
  | .tensorIssue _ spec =>
      decide (spec.mbar = biasReadyObject l cta stage ∧
        spec.sharedBase = ⟨.shared, cta,
          l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val)⟩)
  | _ => false

/-- The count of earlier issues to the same stage and half on this issuing lane. -/
def biasTensorOrdinal (l : Launch) (X : Execution) (stage half : Fin 2) (e : EvId) : Nat :=
  ((X.tr e.1).take e.2).countP (biasTensorHalf l (e.1 / l.block) stage half)

private theorem biasTensorHalfGet {p : Params} {l : Launch} {X : Execution}
    {e : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec} {ev : Event}
    (h : BiasSubbox p l X e stage half spec) (hGet : X.get e = some ev) :
    biasTensorHalf l (e.1 / l.block) stage half ev = true := by
  obtain ⟨src, hs⟩ := h.1
  obtain rfl := Option.some.inj (hGet.symm.trans hs)
  exact decide_eq_true ⟨h.2.1, h.2.2.1⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasSubboxOfHalf {e : EvId} {stage half : Fin 2} {ev : Event}
    (hGet : X.get e = some ev) (hMark : biasTensorHalf l (e.1 / l.block) stage half ev) :
    ∃ spec, BiasSubbox p l X e stage half spec := by
  obtain ⟨src, kind⟩ := ev
  cases kind <;> simp [biasTensorHalf] at hMark
  case tensorIssue addr spec =>
    obtain ⟨_, other, hBox⟩ := biasSubboxOfBarrier hp hX stage ⟨_, hGet⟩ hMark.1
    have hAddr := congrArg Loc.addr (hMark.2.symm.trans hBox.2.2.1)
    have hEq : half.val = other.val := by
      change l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) =
        l.sharedBase + (166912 + 32768 * stage.val + 16384 * other.val) at hAddr
      omega
    exact ⟨spec, (Fin.ext hEq).symm ▸ hBox⟩

private theorem biasTensorResume {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X (g,j) stage half spec) (lower : Option Nat)
    (hLower : ∀ a, lower = some a → a < j ∧ ∃ earlier, BiasSubbox p l X (g,a) stage half earlier) :
    ∃ k, ∃ poll : Event, ∃ q scope,
      X.get (g,k) = some poll ∧
      poll.kind = .wait (biasEmptyObject l (g / l.block) stage) q true true scope ∧
      Resumes kernel X (g,k) (g,j) ∧ ∀ a, lower = some a → a < k := by
  obtain ⟨i, hStage, hHalf, hEv⟩ := biasTensorSelectorOfSubbox hp hX hIssue
  obtain ⟨k, poll, q, scope, hGet, hKind, hResume, hOrder⟩ :=
    biasTensorGuardedSince hp hX i hEv lower (by
      intro a ha
      obtain ⟨haj, earlier, hEarlier⟩ := hLower a ha
      obtain ⟨b, hbs, hbh, hb⟩ := biasTensorSelectorOfSubbox hp hX hEarlier
      exact ⟨haj, b, _, earlier, hbs.trans hStage.symm, hbh.trans hHalf.symm, hb⟩)
  exact ⟨k, poll, q, scope, hGet, hStage ▸ hKind, hResume, hOrder⟩

/-- Every actual half uses a fresh successful empty acquire. This includes both priming halves. -/
theorem biasTensorPollBudget {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X (g,j) stage half spec) :
    biasTensorOrdinal l X stage half (g,j) + 1 ≤
      okPolls (biasEmptyObject l (g / l.block) stage) ((X.tr g).take j) := by
  let empty := biasEmptyObject l (g / l.block) stage
  let mark := biasTensorHalf l (g / l.block) stage half
  let traceTake := (X.tr g).take
  have grows {k : Nat} {e : Event} {phase : Nat} {scope : MbarScope}
      (he : X.get (g,k) = some e) (hw : e.kind = .wait empty phase true true scope) :
      okPolls empty (traceTake (k + 1)) = okPolls empty (traceTake k) + 1 := by
    obtain ⟨source, kind⟩ := e
    change kind = _ at hw
    subst kind
    exact MbarRing.Poll.okPoll_get he
  induction j using Nat.strong_induction_on generalizing spec with
  | h j ih =>
    change (traceTake j).countP mark + 1 ≤ okPolls empty (traceTake j)
    rcases Nat.eq_zero_or_pos ((traceTake j).countP mark) with hz | hPos
    · obtain ⟨k, e, _, _, he, hKind, hResume, _⟩ :=
        biasTensorResume hp hX hIssue none (by simp)
      have hBefore : k < j := hResume.1.2.1
      have hGrow := grows he hKind
      have hLe := MbarRing.Poll.okPolls_mono empty (X.tr g) (show k + 1 ≤ j by omega)
      change okPolls empty (traceTake (k + 1)) ≤ okPolls empty (traceTake j) at hLe
      omega
    · let prev := (traceTake j).countP mark - 1
      have hPrev : prev + 1 ≤ (traceTake j).countP mark := by dsimp only [prev]; omega
      obtain ⟨a, e, ha, hLabel, hCount⟩ := MbarRing.Slot.exists_nth_countP mark hPrev
      have hOrder : a < j := by
        have hLen := (List.getElem?_eq_some_iff.mp ha).1
        simp only [traceTake, List.length_take] at hLen
        omega
      have hEarlier : X.get (g,a) = some e := by
        change (X.tr g)[a]? = some e
        rw [List.getElem?_take_of_lt hOrder] at ha
        exact ha
      rw [List.take_take, Nat.min_eq_left hOrder.le] at hCount
      obtain ⟨earlier, hEarlierBox⟩ := biasSubboxOfHalf hp hX hEarlier hLabel
      obtain ⟨k, f, _, _, hf, hKind, hResume, hFresh⟩ :=
        biasTensorResume hp hX hIssue (some a) (by
          intro b hb
          obtain rfl := Option.some.inj hb.symm
          exact ⟨hOrder, earlier, hEarlierBox⟩)
      have hak := hFresh a rfl
      have hkj : k < j := hResume.1.2.1
      have hInd := ih a hOrder hEarlierBox
      change (traceTake a).countP mark + 1 ≤ okPolls empty (traceTake a) at hInd
      have hMono := MbarRing.Poll.okPolls_mono empty (X.tr g) hak.le
      have hNext := MbarRing.Poll.okPolls_mono empty (X.tr g) (show k + 1 ≤ j by omega)
      have hGrow := grows hf hKind
      change okPolls empty (traceTake a) ≤ okPolls empty (traceTake k) at hMono
      change okPolls empty (traceTake (k + 1)) ≤ okPolls empty (traceTake j) at hNext
      change (traceTake a).countP mark = prev at hCount
      dsimp only [prev] at hCount
      omega

/-- A later Bias issue of a half supplies each earlier issue of that same half. -/
theorem biasEarlierHalfOfOrdinal {g j n : Nat} {stage half : Fin 2}
    (hN : n < biasTensorOrdinal l X stage half (g,j)) :
    ∃ k < j, ∃ earlier, BiasSubbox p l X (g,k) stage half earlier ∧
      biasTensorOrdinal l X stage half (g,k) = n := by
  let mark := biasTensorHalf l (g/l.block) stage half
  have hBudget : n + 1 ≤ ((X.tr g).take j).countP mark := by
    change n < ((X.tr g).take j).countP mark at hN
    omega
  obtain ⟨k,e,hGet,hMarked,hCount⟩ := MbarRing.Slot.exists_nth_countP mark hBudget
  have hK := (List.getElem?_eq_some_iff.mp hGet).1
  simp only [List.length_take] at hK
  have hBefore : k < j := by omega
  rw [List.getElem?_take_of_lt hBefore] at hGet
  rw [List.take_take,Nat.min_eq_left hBefore.le] at hCount
  obtain ⟨box,hBox⟩ := biasSubboxOfHalf hp hX (e := (g,k)) hGet hMarked
  exact ⟨k,hBefore,box,hBox,hCount⟩

/-- The stage's successful loader waits alternate from the initially free stage. -/
theorem biasTensorEmptyAlternates {e : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X e stage half spec)
    (hClean : ∀ r ∈ X.objects (biasEmptyObject l (e.1 / l.block) stage),
      (∃ q ok, r.action = .pollParity q ok) → r.fault = none) :
    SelectedAlternates (objectThreadSelected e.1)
      (X.objects (biasEmptyObject l (e.1 / l.block) stage)) 1 := by
  have hWarp := biasTensorActorWarp hp hX hIssue
  apply MbarRing.Poll.alternates hX hClean
  intro k _ q acq sc hPoll
  rw [biasEmptyPollParity hp hX stage hWarp hPoll rfl, Nat.mod_mod]

/-- The half's ordinal identifies a successful acquire preceding the actual issue. -/
theorem biasTensorOrdinalGuard {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X (g,j) stage half spec) :
    let empty := biasEmptyObject l (g / l.block) stage
    ∃ (k : Nat) (e : Event) (phase : Nat),
      X.get (g,k) = some e ∧ e.kind = .wait empty phase true true .cta ∧
      okPolls empty ((X.tr g).take k) = biasTensorOrdinal l X stage half (g,j) ∧
      Resumes kernel X (g,k) (g,j) := by
  have hBudget := biasTensorPollBudget hp hX hIssue
  obtain ⟨k, source, phase, acquire, scope, hk, he, hOrdinal⟩ :=
    MbarRing.Poll.exists_nth hBudget
  have hWarp := biasTensorActorWarp hp hX hIssue
  obtain ⟨_, _, rfl, rfl⟩ := biasEmptyLoaderPollShape hp hX stage hWarp.ge he
  obtain ⟨exit, hs⟩ := actualCanonicalPoll hX he
  obtain ⟨_, hEnd⟩ := hIssue.1
  have hTrace : TraceBefore X (g,k) (g,j) :=
    ⟨rfl, hk, (List.getElem?_eq_some_iff.mp hEnd).1⟩
  refine ⟨k, _, phase, he, rfl, hOrdinal, hTrace, ?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨source, exit, _, phase, true, .cta, he, hs, hTrace⟩

/-- On one stage and half in the same CTA, equal actual ordinals are the same issue. -/
theorem biasTensorOrdinalInjective {e f : EvId} {stage half : Fin 2} {spec other : TensorCopy.Spec}
    (he : BiasSubbox p l X e stage half spec) (hf : BiasSubbox p l X f stage half other)
    (hOwner : e.1 / l.block = f.1 / l.block)
    (hOrd : biasTensorOrdinal l X stage half e = biasTensorOrdinal l X stage half f) :
    e = f := by
  obtain ⟨g, j⟩ := e
  obtain ⟨g', j'⟩ := f
  have hg : g = g' := biasTensorSameIssuer hp hX he hf hOwner
  subst g'
  obtain ⟨_, hGet⟩ := he.1
  obtain ⟨_, hGet'⟩ := hf.1
  have ha := biasTensorHalfGet (e := (g,j)) he hGet
  have hb := biasTensorHalfGet (e := (g,j')) hf hGet'
  exact congrArg (fun k => (g,k)) (nthEv_unique hGet ha hGet' hb hOrd)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
