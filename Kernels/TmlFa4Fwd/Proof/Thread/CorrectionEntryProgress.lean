-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationReadProgress
public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWarpZero
import Lemmas.Step.Object
import Lemmas.Snoc.SnocAsyncSilent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue
open Mma (allocationEntrySites allocationGenerationZeroMember)
open AsyncCopy

noncomputable section

private theorem advancePrefix {l : Launch} {X : Execution} {g pos : Nat}
    {s t u : TState} {e : Event} (he : X.get (g,pos) = some e)
    (hr : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hs : EStep kernel Assumptions.all l g t e (some u)) :
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some u) := by
  rw [List.take_succ_eq_append_getElem (len_of_get he), (List.getElem?_eq_some_iff.mp he).2]
  exact hr.snoc hl hs

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem initialArrival (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) :
    X.IsBarrier (g,6) 2 (some 416) 7747 := by
  obtain ⟨pos, u, _, e, _, _, _, he, hk, hPos, hu, hPrefix, hTail⟩ :=
    Thread.Register.requestReturn hp hMax hg
  obtain rfl := hPos (by omega)
  have hSite : u.pc = 7747 := by
    rw [hu.1]
    simp [registerHintPc, dispatchParamPc, show ¬ warpIndex l g < 8 by omega,
      show ¬ 14 ≤ warpIndex l g by omega, show warpIndex l g ≠ 13 by omega,
      show warpIndex l g ≠ 12 by omega]
  have h := Thread.Allocation.requireArrival hp hMax hg (by change 0 < 6; decide)
    (len_of_get he) (by rw [hSite]; decide) hu.2.2.2.1 hPrefix hTail
    (Thread.Register.releasedAfterRequest hp hMax he hk)
  rwa [hSite] at h

/-- A correction lane in a maximal execution crosses the released initial allocation rendezvous
with its actual trace prefix and its role's parameter frame. -/
theorem rendezvousOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) :
    ∃ t o, X.IsBarrier (g,6) 2 (some 416) 7747 ∧ At t 7748 (entryFacts p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 7) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 7) o ∧
      Softmax.beforeFirstScan X g 7 ∧
      (7 = (X.tr g).length → Step.Released l X g) := by
  have hNonzero : 0 < warpIndex l g := by omega
  have hArr := initialArrival hp hMax hg hLo hHi
  have hLen : 6 < (X.tr g).length := len_of_get hArr
  obtain ⟨s, o, hs, _, hPast, hTail⟩ := nonzeroCommonPrefix hp hMax.1 hg hNonzero (by omega)
  obtain ⟨t, ht, hLocal⟩ := nonzeroRoleEntryFromPrefix hp hg hs
  have hSite : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hSite] at ht
  obtain ⟨u, hu, hFrame⟩ := entryBatch hp ht
  have hHint : Next kernel Assumptions.all l g s u (.setMaxReg false 64 (next u)) :=
    ⟨hLocal.trans (run_rtg hu), entryHint hFrame.1 hFrame.2.2.2.1⟩
  obtain ⟨e, v, he, ⟨inst, rfl, hv⟩, hRun⟩ := hHint.continuing_at_nonempty (pos := 5)
    (by rintro _ ⟨_, _, hBad⟩; cases hBad) hTail
    (fun hNil => by have := List.drop_eq_nil_iff.mp hNil; omega)
  obtain rfl := Option.some.inj hv
  have hPast' := advancePrefix he hPast hHint.steps ⟨_, hHint.stop, inst, rfl, rfl⟩
  have hOut := entryBar (g := g) hFrame.next.1 hFrame.2.2.2.1 hp.block
  have hBarNext : Next kernel Assumptions.all l g (next u) (next u)
      (.bar 2 (next (next u)) (some 416) .sync) := ⟨.refl, hOut⟩
  obtain ⟨f, w, hf, ⟨rfl, hw⟩, hRest⟩ := hBarNext.continuing_at_nonempty (pos := 6)
    (by rintro _ ⟨_, hBad⟩; cases hBad) hRun
    (fun hNil => (Nat.not_le_of_lt hLen) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hw
  have hPast'' := advancePrefix hf hPast' .refl ⟨_, hOut, rfl, rfl⟩
  obtain ⟨hFence, hCTA⟩ := nonzeroBarrierArrives hp hMax hg hNonzero
  have hCount := Softmax.beforeFirstScan_advance
    (Softmax.beforeFirstScan_advance (Softmax.beforeFirstScan_three hp hMax.1 hg (by omega))
      hFence rfl rfl) hCTA rfl rfl
  have hCount' := Softmax.beforeFirstScan_advance
    (Softmax.beforeFirstScan_advance hCount he rfl rfl) hf rfl rfl
  refine ⟨_, o, hArr, hFrame.next.next, hPast'', hRest, hCount', ?_⟩
  intro hLast
  have hDone := Thread.Allocation.initialBarrierReleased hp hMax hg
  obtain ⟨k, site, hS, hFound, hKey⟩ :=
    allocationGenerationZeroMember hp hMax.1 hg (by omega) hDone
  have hK : k < (X.tr g).length := len_of_get hFound
  change X.get (g,k) = some ⟨site, .bar 2 (some 416) .sync⟩ at hFound
  have hEq : k = 6 := by
    have hLe : k ≤ 6 := by omega
    rcases Nat.lt_or_eq_of_le hLe with hLt | rfl
    · exfalso
      interval_cases k
      · have hKind := congrArg Event.kind (firstSharedValue hp hMax.1 g hg hFound)
        cases hKind
      · have hKind := congrArg Event.kind (secondWarpValue hp hMax.1 g hg hFound)
        cases hKind
      · have hKind := congrArg Event.kind (thirdWarpValue hp hMax.1 g hg hFound)
        cases hKind
      · rw [hFence] at hFound
        cases congrArg Event.kind (Option.some.inj hFound)
      · rw [hCTA] at hFound
        cases congrArg Event.kind (Option.some.inj hFound)
      · rw [he] at hFound
        cases congrArg Event.kind (Option.some.inj hFound)
    · rfl
  subst k
  have hEnd : (X.tr g).length - 1 = 6 := by omega
  exact NamedBar.released_of_key hMax.1.ctaBar rfl (hEnd.symm ▸ hArr)
    (hEnd.symm ▸ hKey) hDone

private theorem creditAtMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos : Nat} (hg : g < l.threads) (hPos : 0 < pos) (hFramePos : pos ≤ (X.tr g).length)
    {s t : TState} {o : Option TState} {F : List (Nat × Value)} (stage : Fin 2)
    (ht : At t (7752 + 2 * stage.val) F) (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hOne : (5868, b32 1) ∈ F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 8985 + stage.val)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ u, X.get (g,pos) = some ⟨7752+2*stage.val, .arrive (creditLoc l g stage) 0 1 true .cta⟩ ∧
      At u (7752 + 2 * stage.val + 1) F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+1)) o := by
  let addr := creditLoc l g stage
  let u := next (mbarStateDest t (some (8985 + stage.val)))
  have hOut := creditTemplate (g := g) hp stage ht.1 ht.2.2.2.1
    (holds_mem ht.2.2.2.2 hShared) (holds_mem ht.2.2.2.2 hOne)
  let event := Event.mk t.pc (.arrive addr 0 1 true .cta)
  have hStep : EStep kernel Assumptions.all l g t event (some u) := ⟨_, hOut, rfl, rfl⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hShort
    have hEq := Nat.le_antisymm hFramePos hShort
    have hStarted : X.tr g ≠ [] := fun h => by rw [h, List.length_nil] at hEq; omega
    rw [List.take_of_length_le hShort] at hPast
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      (hRelease hEq) hPast hLocal hStep ⟨trivial, fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := addr) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = addr
      · subst loc
        simp [objectAction, snoc_get_new, event]
      · simp [objectAction, snoc_get_new, event, h, Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hn : Next kernel Assumptions.all l g s t (.arrive addr 0 u 1 true .cta) := ⟨hLocal, hOut⟩
  obtain ⟨e, v, he, ⟨rfl, hv⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, h⟩; cases h) hRun
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hv
  exact ⟨u, ht.1 ▸ he,
    ⟨congrArg (· + 1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_update ht.2.2.2.2 hFresh⟩,
    advancePrefix he hPast hLocal hStep, hTail⟩

/-- Both initial release credits occur before a maximal correction lane's scheduler entry. -/
theorem schedulerEntryOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) :
    ∃ t o, At t 7755 (afterCreditFacts p l g) ∧
      X.get (g,7) = some ⟨7752, .arrive (creditLoc l g 0) 0 1 true .cta⟩ ∧
      X.get (g,8) = some ⟨7754, .arrive (creditLoc l g 1) 0 1 true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 9) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 9) o ∧
      Softmax.beforeFirstScan X g 9 ∧
      (9 = (X.tr g).length → Step.Released l X g) := by
  obtain ⟨t, o, hBar, ht, hPast, hTail, hCount, hReady⟩ :=
    rendezvousOfMaximal hp hMax hg hLo hHi
  obtain ⟨s, hs, hS⟩ := prepareCredits hp ht
  obtain ⟨u, hGet₀, hu, hPast', hTail'⟩ :=
    creditAtMaximal hp hMax hg (pos := 7) (by decide) (len_of_get hBar) 0 hS
      (by simp [creditFacts, entryFacts, nonzeroBarrierFacts]) (by simp [creditFacts])
      (creditFactsFresh (by decide)) (run_rtg hs) hPast hTail hReady
  have released {pos site : Nat} {addr : Loc}
      (he : X.get (g,pos) = some ⟨site, .arrive addr 0 1 true .cta⟩)
      (hLast : pos+1 = (X.tr g).length) : Step.Released l X g := by
    apply Step.Released.of_get
    intro e hGet
    have hEnd : (X.tr g).length - 1 = pos := by omega
    rw [hEnd, he] at hGet
    obtain rfl := Option.some.inj hGet
    intro hImpossible
    cases hImpossible
  obtain ⟨v, hv, hV⟩ := prepareSecondCredit hp hu
  obtain ⟨w, hGet₁, hw, hPast'', hTail''⟩ :=
    creditAtMaximal hp hMax hg (pos := 8) (by decide) (len_of_get hGet₀) 1 hV
      (by simp [afterCreditFacts, creditFacts, entryFacts, nonzeroBarrierFacts])
      (by simp [afterCreditFacts, creditFacts])
      (by
        intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · dsimp only; decide
        · exact creditFactsFresh (by decide) pair hm)
      (run_rtg hv) hPast' hTail' (released hGet₀)
  have hCount' := Softmax.beforeFirstScan_advance
    (Softmax.beforeFirstScan_advance hCount hGet₀ rfl rfl) hGet₁ rfl rfl
  exact ⟨w, o, hw, hGet₀, hGet₁, hPast'', hTail'', hCount', released hGet₁⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
