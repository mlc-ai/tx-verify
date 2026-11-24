-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Prologue
public import Kernels.TmlFa4Fwd.Proof.RegisterSafety
public import Lemmas.Step.RegIssue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Register
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem commonReturn {g : Nat} (hg : g < l.threads) :
    ∃ pos t o, 0 < pos ∧ (0 < warpIndex l g → pos = 5) ∧
      X.get (g, pos - 1) = some ⟨173, .bar 0 none .sync⟩ ∧
      EarlierEvents X g pos 174 ∧
      At t 174 [(1062, b32 (warpIndex l g)), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  rcases Nat.eq_zero_or_pos (warpIndex l g) with hw | hw
  · obtain ⟨index, hBar, _⟩ := commonBarrierAllArrive hp hMax hg
    obtain ⟨n, t, o, _, ht, he, hEarly, hRun, hTail⟩ :=
      warp0CommonPrefixOfRendezvous hp hMax.1 hg hw hBar
    have hRegs := ht.2.2.2.2
    exact ⟨n + 2, t, o, by omega, (by omega), he, hEarly,
      ht.mono ⟨hw.symm ▸ hRegs.1, holds_mem hRegs (by simp [initFacts, initAddresses]), trivial⟩,
      hRun, hTail⟩
  · obtain ⟨hFence, hBar⟩ := nonzeroBarrierArrives hp hMax hg hw
    have hLen : 5 ≤ (X.tr g).length := len_of_get hBar
    obtain ⟨t, o, ht, _, hRun, hTail⟩ := nonzeroCommonPrefix hp hMax.1 hg hw hLen
    have hEarly : EarlierEvents X g 5 174 := by
      intro j hj e he
      interval_cases j
      · rw [firstSharedValue hp hMax.1 g hg he]
        change 25 < 174; decide
      · rw [secondWarpValue hp hMax.1 g hg he]
        change 34 < 174; decide
      · rw [thirdWarpValue hp hMax.1 g hg he]
        change 35 < 174; decide
      · cases Option.some.inj (he.symm.trans hFence)
        decide
      · cases Option.some.inj (he.symm.trans hBar)
        decide
    exact ⟨5, t, o, by decide, (fun _ => rfl), hBar, hEarly,
      ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩, hRun, hTail⟩

private theorem firstRequest {g : Nat} (hg : g < l.threads) :
    ∃ j site inc n inst, SetMaxNReg.Request X (g, j) site inc n inst := by
  obtain ⟨pos, t, o, hPos, _, hBar, hEarly, ht, hRun, hTail⟩ := commonReturn hp hMax hg
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  by_cases hNil : (X.tr g).drop pos = []
  · exfalso
    have hLen : pos = (X.tr g).length := by
      have hEnd := List.drop_eq_nil_iff.mp hNil
      have hIndex := len_of_get hBar
      change pos - 1 < (X.tr g).length at hIndex
      omega
    rw [hLen] at hBar
    obtain ⟨Y, hY, hTr, hReleased⟩ :=
      Startup.releaseRendezvous hp hMax hg ⟨_, hBar, rfl⟩
    have hStarted : Y.tr g ≠ [] := by
      intro h
      have hLenY : pos = (Y.tr g).length := by rwa [hTr]
      rw [h, List.length_nil] at hLenY
      omega
    have hCompleteRun : Run kernel Assumptions.all l g {} (Y.tr g) (some t) := by
      rw [hTr]
      simpa [hLen] using hRun
    have hNo (j site : Nat) (inc : Bool) (n inst : Nat) :
        ¬ SetMaxNReg.Request Y (g, j) site inc n inst := by
      intro he
      have heX : SetMaxNReg.Request X (g, j) site inc n inst := by
        change (Y.tr g)[j]? = _ at he
        rwa [hTr] at he
      have hj : j < pos := hLen ▸ len_of_get heX
      have hPc : site < 174 := hEarly j hj _ heX
      have hSite := registerRequestSite hMax.1 heX
      simp [registerHintSites] at hSite
      omega
    obtain ⟨u, hu, hn⟩ := firstRegisterHintNext hp hg warp ht
    have he : EStep kernel Assumptions.all l g u
        (Step.regRequestEvent u.pc (registerHintOf warp.val).1 (registerHintOf warp.val).2 0)
        (some (next u)) := ⟨_, hn.stop, 0, rfl, rfl⟩
    exact hY.not_grows (Step.reg_issue_counted_extension_of_started hY.1 hg hStarted
      hReleased.ready hNo hCompleteRun hn.steps he
      (Assumptions.wfStep.quiet hY.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  · obtain ⟨_, inst, he, _, _⟩ := firstRegisterHintFromCommon hp hg warp ht hTail hNil
    exact ⟨pos, _, _, _, inst, he⟩

/-- No register request can remain blocked on a missing warp lane in a maximal execution. -/
theorem requestReady {i : EvId} {e : Event} {inc : Bool} {n inst : Nat} (he : X.get i = some e)
    (hk : e.kind = .setMaxReg inc n inst) : Ready l X i := by
  obtain ⟨g, j⟩ := i
  obtain ⟨site, kind⟩ := e
  cases hk
  have he' : SetMaxNReg.Request X (g, j) site inc n inst := he
  apply (SetMaxNReg.ready_iff he').2
  intro lane hLane
  have hg := Step.CtaBar.thread_lt_of_get hMax.1 he
  have hWarp : SameWarp l g (warpLane l g lane) :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hLane).1
  obtain ⟨k, dst, inc', n', inst', hf⟩ := firstRequest hp hMax hWarp.1.2.1
  have hFin : (⟨warpIndex l g, warpIndex_lt hp g⟩ : Fin 16) =
      ⟨warpIndex l (warpLane l g lane), warpIndex_lt hp _⟩ := Fin.ext hWarp.2
  obtain ⟨hOrd1, hSite, hKind⟩ := registerRequestShape hp hMax.1 he'
  obtain ⟨hOrd2, hDst, hKind'⟩ := registerRequestShape hp hMax.1 hf
  rw [hFin] at hSite hKind
  obtain rfl := hSite.trans hDst.symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hKind.trans hKind'.symm)
  exact ⟨k, ⟨_, hf⟩, hWarp, hOrd1.trans hOrd2.symm, _, _, _, _, _, he', hf⟩

/-- Replay through the first issued request, preserving its exact prefix and suffix. -/
theorem requestReturn {g : Nat} (hg : g < l.threads) :
    ∃ (pos : Nat) (u : TState) (o : Option TState) (e : Event) (inc : Bool) (n inst : Nat),
      X.get (g, pos) = some e ∧
      e.kind = .setMaxReg inc n inst ∧ (0 < warpIndex l g → pos = 5) ∧
      At u (registerHintPc ⟨warpIndex l g, warpIndex_lt hp g⟩ + 1)
        [(1062, b32 (warpIndex l g)), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨pos, t, o, _, hNonzero, _, hEarly, ht, hRun, hTail⟩ := commonReturn hp hMax hg
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨j, site, inc, n, inst, hReq⟩ := firstRequest hp hMax hg
  have hLe : pos ≤ j := by
    by_contra! hLt
    have hPc : site < 174 := hEarly j hLt _ hReq
    have hSite := registerRequestSite hMax.1 hReq
    simp [registerHintSites] at hSite
    omega
  have hLt : pos < (X.tr g).length := hLe.trans_lt (len_of_get hReq)
  obtain ⟨u, hu, hNext⟩ := firstRegisterHintNext hp hg warp ht
  obtain ⟨e, v, he, ⟨inst', hKind, hv⟩, hRest⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hv
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some (next u)) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos] = e := by
      change (X.tr g)[pos]? = some e at he
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at he
    rw [hEq]
    exact hRun.snoc hNext.steps ⟨_, hNext.stop, inst', hKind, rfl⟩
  have hGet : X.get (g, pos) = some e := he
  exact ⟨pos, next u, o, e, _, _, inst', hGet, congrArg Event.kind hKind, hNonzero,
    hu.next, hPast, hRest⟩

/-- A maximal execution can return from its final register request. -/
theorem releasedAfterRequest {g pos : Nat} {e : Event} {inc : Bool} {n inst : Nat}
    (he : X.get (g, pos) = some e) (hk : e.kind = .setMaxReg inc n inst)
    (hLast : pos + 1 = (X.tr g).length) : Step.Released l X g := by
  constructor
  intro site kind he' _
  have hPos : (X.tr g).length - 1 = pos := by omega
  rw [hPos] at he' ⊢
  obtain rfl := Option.some.inj (he'.symm.trans he)
  exact requestReady hp hMax he hk

end
end PTX.Kernels.TmlFa4Fwd.Thread.Register
