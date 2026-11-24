-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueProgress
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Order.GuardSnoc
public import Lemmas.Step.Issue
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Expose the initial three event records while retaining the remaining trace. -/
theorem broadcastTraceSplit {X : Execution} {g : Nat} (hn : 3 ≤ (X.tr g).length) :
    ∃ e₀ e₁ e₂, X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
  have h₀ : 0 < (X.tr g).length := by omega
  have h₁ : 1 < (X.tr g).length := by omega
  have h₂ : 2 < (X.tr g).length := by omega
  refine ⟨(X.tr g)[0], (X.tr g)[1], (X.tr g)[2], ?_⟩
  have h0 := List.drop_eq_getElem_cons h₀
  have h1 := List.drop_eq_getElem_cons h₁
  have h2 := List.drop_eq_getElem_cons h₂
  rw [h2] at h1
  rw [h1] at h0
  exact h0

private theorem nextNonzeroFence {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hWarp : 0 < warpIndex l g) (hLen : 3 ≤ (X.tr g).length) :
    ∃ t u o, Run kernel Assumptions.all l g
      ({} : TState) ((X.tr g).take 3) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 3) o ∧
      Next kernel Assumptions.all l g t u (.fenceMbarInit (next u)) ∧
      u.pc = 172 ∧ u.fault = none := by
  obtain ⟨e₀, e₁, e₂, he⟩ := broadcastTraceSplit hLen
  obtain ⟨t, o, hPc, hFault, hBase, hW, _, _, _, _, hRun, hPrefix⟩ :=
    broadcastPrefixRun hp hX g hg he
  obtain ⟨u, hu, hUpc, hUf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t hWarp
      (warpIndex_lt hp g) hPc hFault hW hBase
  have hOut : out kernel [] l g u = .ev (.fenceMbarInit (next u)) := by
    unfold out
    rw [hUpc, hUf, Flow.code_172]
    rfl
  have hNext : Next kernel Assumptions.all l g t u (.fenceMbarInit (next u)) :=
    ⟨run_rtg hu, startupOut (.inl (by rw [hUpc]; decide)) hOut⟩
  have hTake : (X.tr g).take 3 = [e₀, e₁, e₂] := by
    conv_lhs => rw [he]
    rfl
  exact ⟨t, u, o, hTake ▸ hPrefix, hRun, hNext, hUpc, hUf⟩

/-- Appending the initialization fence leaves the visibility of every existing read
unchanged. The fence only participates in the publication of later initialization arrivals. -/
theorem fenceInitCanIssue {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hNonempty : X.tr g ≠ []) (hReleased : Step.Released l X g) {t u : TState}
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t))
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    {site : Nat}
    (hStep : EStep kernel Assumptions.all l g u ⟨site, .fenceMbarInit⟩ (some (next u))) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  let e : Event := ⟨site, .fenceMbarInit⟩
  let Y := X.snoc g e (fun _ => none)
  have hTc : ∀ k, e.kind ≠ .tc k := by intro _ h; cases h
  have hWait : e.kind.WaitFree := ⟨trivial,hTc⟩
  have hShuffle : ∀ mode a b mask recv ok, e.kind ≠ .shfl mode a b mask recv ok := by
    intro _ _ _ _ _ _ h
    cases h
  have hRead : ∀ a bs, e.kind ≠ .rd a bs := by intro _ _ h; cases h
  have hWrite : ∀ a bs, e.kind ≠ .wr a bs := by intro _ _ h; cases h
  have hAtomic : ∀ a old new, e.kind ≠ .rmw a old new := by intro _ _ _ h; cases h
  have hOld {a b : EvId} (hb : b.2 < (X.tr b.1).length) :
      baseCausality l Y a b ↔ baseCausality l X a b :=
    Step.snoc_baseCausality_old hX.effectValidity hX.cluster
      (by intro _ _ _ h; cases h) (by intro _ _ h; cases h) (.of_rfWf hX.rf)
      (by intro _ h; cases h) hb
  have hVisibility loc v f (hf : X.RefPresent f) :
      modelCausality l Y loc v f ↔ modelCausality l X loc v f :=
    Kind.AsyncSilent.modelCausality_snoc_old (by trivial) hOld
      (snoc_allocResultBefore_old hX.dependency.ready) (refPresent_issuer_lt hX.effectValidity hf)
  refine ⟨Y,?_,le_snoc,?_⟩
  · refine consistent_snoc_preserving hX hg hRun hTau hStep hShuffle
      (by intro h; cases h) hReleased.ready (Step.snoc_new_ready hWait hShuffle rfl rfl)
      (fun _ _ _ hv => (snoc_memReads_control hX.effectValidity hTc hRead hAtomic).mp hv)
      (fun _ _ _ => snoc_memWrites_control hX.effectValidity hWrite hAtomic) hVisibility
      (snoc_plain_orderOk hX hWait hShuffle (by intro h; cases h) rfl rfl
        (by intro _ _ _ _ h; cases h) (fun a old new h => (hAtomic a old new h).elim))
      (Assumptions.wfStep.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl))
      (hX.tmaOk_snoc_unobserved hTc (by intro loc; simp [AsyncCopy.objectAction,snoc_get_new,e]))
      (ExtensionObligations.snoc_plain hX trivial (.inl hNonempty) (by intro h; cases h)
        hAtomic rfl (by intro _ h; cases h)
        (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => hWrite _ _ (congrArg Event.kind h)))
  · change X.size l < (X.snoc g e (fun _ => none)).size l
    rw [size_snoc hX hg (show e.counts = true from rfl)]
    omega

/-- A maximal execution records the nonzero warps' initialization fences. -/
theorem nonzeroFenceProgress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g) :
    4 ≤ (X.tr g).length := by
  have hLen := startupBroadcastsProgress hp hMax g hg
  by_contra hShort
  have hEq : (X.tr g).length = 3 := by omega
  obtain ⟨t, u, _, hRun, _, hNext, hUpc, _⟩ :=
    nextNonzeroFence hp hMax.1 hg hWarp hLen
  have hPrefix : (X.tr g).take 3 = X.tr g := List.take_of_length_le hEq.le
  rw [hPrefix] at hRun
  let e : Event := ⟨172, .fenceMbarInit⟩
  have hStep : EStep kernel Assumptions.all l g u e (some (next u)) :=
    ⟨_, hNext.stop, by rw [hUpc], rfl⟩
  have hNotEmpty : X.tr g ≠ [] := by intro h; rw [h] at hEq; contradiction
  have hReleased : Step.Released l X g := by
    apply Step.Released.of_get
    intro ev he
    rw [show (X.tr g).length - 1 = 2 by omega] at he
    rw [thirdWarpValue hp hMax.1 g hg he]
    intro h
    cases h
  apply hMax.not_grows
  exact fenceInitCanIssue hMax.1 hg hNotEmpty hReleased hRun hNext.steps hStep

private theorem consumeFence {l : Launch} {g : Nat} {t u : TState} {e : Event}
    {es : List Event} {o : Option TState}
    (hNext : Next kernel Assumptions.all l g t u (.fenceMbarInit (next u)))
    (hr : Run kernel Assumptions.all l g t (e :: es) o) :
    e = ⟨u.pc, .fenceMbarInit⟩ ∧ Run kernel Assumptions.all l g (next u) es o := by
  obtain ⟨v, ⟨hev, hv⟩, hr⟩ := hNext.continuing_event (by
    rintro ⟨_, h⟩; cases h) hr
  obtain rfl := Option.some.inj hv
  exact ⟨hev, hr⟩

/-- Once its three broadcasts and fence have been issued, a nonzero warp can arrive at the
common CTA barrier even if other warps have not arrived yet. -/
theorem nonzeroBarrierArrives {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g) :
    X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ := by
  have hLen := nonzeroFenceProgress hp hMax hg hWarp
  obtain ⟨t, u, o, hPrefix, hTail, hNext, hPc, hSafe⟩ :=
    nextNonzeroFence hp hMax.1 hg hWarp (by omega)
  have hi : 3 < (X.tr g).length := by omega
  have hSplit := List.drop_eq_getElem_cons hi
  rw [hSplit] at hTail
  obtain ⟨hEvent, hPast⟩ := consumeFence hNext hTail
  have hFence : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ := by
    change (X.tr g)[3]? = _
    rw [List.getElem?_eq_getElem hi, hEvent, hPc]
  have hNow : (next u).pc = 173 := by change u.pc + 1 = 173; rw [hPc]
  have hBarCore : out kernel [] l g (next u) = .ev (.bar 0 (next (next u)) none .sync) := by
    have hFault : (next u).fault = none := hSafe
    unfold out
    rw [hNow, hFault, Flow.code_173]
    rfl
  have hBar := startupOut (A := Assumptions.all) (.inl (by rw [hNow]; decide)) hBarCore
  refine ⟨hFence, ?_⟩
  by_cases hb : 4 < (X.tr g).length
  · have hs := List.drop_eq_getElem_cons hb
    rw [show 3 + 1 = 4 by decide, hs] at hPast
    change (X.tr g)[4]? = _
    rw [List.getElem?_eq_getElem hb]
    have hn : Next kernel Assumptions.all l g (next u) (next u)
        (.bar 0 (next (next u)) none .sync) := ⟨.refl, hBar⟩
    obtain ⟨_, ⟨he, _⟩, _⟩ := hn.continuing_event (by rintro ⟨_, h⟩; cases h) hPast
    exact congrArg some (hNow ▸ he)
  · exfalso
    have hFull : (X.tr g).take 3 ++ [⟨172, .fenceMbarInit⟩] = X.tr g := by
      have hEmpty : (X.tr g).drop (3 + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      have h := List.take_append_drop 3 (X.tr g)
      rw [hSplit, hEmpty, hEvent, hPc] at h
      exact h
    have hFires : EStep kernel Assumptions.all l g u ⟨172, .fenceMbarInit⟩ (some (next u)) :=
      ⟨_, hNext.stop, by rw [hPc], rfl⟩
    have hr := hPrefix.snoc hNext.steps hFires
    rw [hFull] at hr
    have hReleased : Step.Released l X g := by
      apply Step.Released.of_get
      intro ev he
      rw [show (X.tr g).length - 1 = 3 by omega, hFence] at he
      obtain rfl := Option.some.inj he.symm
      intro he
      cases he
    have hNotEmpty : X.tr g ≠ [] := by intro h; rw [h] at hLen; contradiction
    have hStep : EStep kernel Assumptions.all l g (next u)
        ⟨(next u).pc, .bar 0 none⟩ (some (next (next u))) := ⟨_, hBar, rfl, rfl⟩
    exact hMax.not_grows (Step.bar_counted_extension hMax.1 hg (.inl hNotEmpty) hReleased
      (fun a ha => Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl) a ha) hr .refl hStep)

end
end PTX.Kernels.TmlFa4Fwd.Prologue
