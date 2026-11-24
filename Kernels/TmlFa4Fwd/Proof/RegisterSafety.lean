-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.TerminalSite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem commonPrefixBeforeHint (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} (hg : g < l.threads) {e : Event}
    (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ n t o, n ≤ index ∧ At t 174 [(1062, b32 (warpIndex l g)), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop n) o ∧ EarlierEvents X g n 174 := by
  cases Nat.eq_zero_or_pos (warpIndex l g) with
  | inl hZero =>
    obtain ⟨n, t, o, hn, ht, hr, hEarly⟩ :=
      warp0CommonPrefixOfLateEventWithEarlier hp hX hg hZero he hPc
    have hReg := ht.2.2.2.2
    exact ⟨n, t, o, hn, ht.mono
      ⟨hZero.symm ▸ hReg.1, holds_mem hReg (by simp [initFacts, initAddresses]), trivial⟩,
      hr, hEarly⟩
  | inr hNZ =>
    obtain ⟨t, o, hn, ht, hr⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hNZ he hPc
    obtain ⟨_, hb, hEarly⟩ := nonzeroStartupBar hp hX hg hNZ he hPc
    have hBefore : EarlierEvents X g 4 173 := hEarly
    exact ⟨5, t, o, hn, ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩, hr,
      hBefore.succ hb rfl⟩

private theorem notHintBeforeCommon {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g n : Nat} (hEarly : EarlierEvents X g n 174) :
    SetMaxNReg.ordinal X (g, n) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hm
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hLt : k < n :=
    (List.getElem?_eq_some_iff.mp hk).1.trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hLt] at hk
  have hp := hEarly k hLt e hk
  rcases e with ⟨pc, kind⟩
  cases kind <;> simp [SetMaxNReg.isRequest]
  rename_i inc count inst
  change pc < 174 at hp
  have hSite := registerRequestSite hX (i := (g, k)) (pc := pc) (inc := inc) (n := count)
    (inst := inst) hk
  simp [registerHintSites] at hSite
  omega

/-- Each actual register hint is the first request of its warp, with the decoded PC,
direction and count for that role. -/
theorem registerRequestShape (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc n inst : Nat} {inc : Bool} (he : SetMaxNReg.Request X (g, index) pc inc n inst) :
    let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
    SetMaxNReg.ordinal X (g, index) = 0 ∧ pc = registerHintPc warp ∧
      (inc, n) = registerHintOf warp.val := by
  dsimp only
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hSite := registerRequestSite hX he
  have hLate : 173 < pc := by simp [registerHintSites] at hSite; omega
  obtain ⟨pos, t, o, hBefore, ht, hr, hEarly⟩ :=
    commonPrefixBeforeHint hp hX hg he hLate
  have hIndex : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hSuffix : (X.tr g).drop pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hIndex) ((List.drop_eq_nil_iff.mp h).trans hBefore)
  obtain ⟨u, inst', hReq, hU, hTail⟩ := firstRegisterHintFromCommon hp hg warp ht hr hSuffix
  rcases Nat.eq_or_lt_of_le hBefore with rfl | hLt
  · have hEq := Option.some.inj (he.symm.trans hReq)
    obtain ⟨hPc, hKind⟩ := Event.mk.inj hEq
    obtain ⟨hInc, hN, _⟩ := Kind.setMaxReg.inj hKind
    exact ⟨notHintBeforeCommon hX hEarly, hPc, Prod.ext hInc hN⟩
  · exfalso
    obtain ⟨_, hWalk⟩ := Mma.walkFromRun hTail
    have hm : (⟨pc, .setMaxReg inc n inst⟩ : Event) ∈ (X.tr g).drop (pos + 1) := by
      apply List.mem_of_getElem? (i := index - (pos + 1))
      rw [List.getElem?_drop, Nat.add_sub_of_le hLt]
      exact he
    exact noRegisterHintAfterFirst warp hU hWalk _ hm hSite

private theorem no_prior_hint {X : Execution} {e : EvId} (ho : SetMaxNReg.ordinal X e = 0) :
    SetMaxNReg.prior X e = none := by
  have hNo := List.countP_eq_zero.mp ho
  unfold SetMaxNReg.prior
  generalize (X.tr e.1).take e.2 = es at hNo ⊢
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons]
    have hHead := hNo e (by simp)
    rcases e with ⟨pc, kind⟩
    cases kind
    case setMaxReg => exact (hHead rfl).elim
    all_goals exact ih (fun q h => hNo q (List.mem_cons_of_mem _ h))

/-- Every actual register request is safe under the kernel's declared register semantics. -/
theorem noRegisterRequestUnsafe (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    ¬ SetMaxNReg.Unsafe l X := by
  rintro ⟨⟨g, index⟩, pc, inc, n, inst, hGet, hUnsafe⟩
  obtain ⟨hOrdinal, _, hCount⟩ := registerRequestShape hp hX hGet
  rcases hUnsafe with ⟨m, hm, _⟩ | hb | ⟨f, pc', inc', n', inst', hG, hf, _, hBad⟩ | ⟨hn, _⟩
  · rw [no_prior_hint hOrdinal] at hm
    cases hm
  · rw [hp.block] at hb
    omega
  · obtain ⟨_, _, hOther⟩ := registerRequestShape hp hX hf
    have hSame : registerHintOf (warpIndex l g) = registerHintOf (warpIndex l f.1) := by
      have hGroup := hG.2
      rw [hp.block] at hGroup
      simp only [warpIndex, hp.block, registerHintOf]
      have h8 : g % 512 / 32 < 8 ↔ f.1 % 512 / 32 < 8 := by omega
      have h12 : g % 512 / 32 < 12 ↔ f.1 % 512 / 32 < 12 := by omega
      simp only [h8, h12]
    have he := hCount.trans (hSame.trans hOther.symm)
    obtain ⟨hInc, hN⟩ := Prod.mk.inj he
    exact hBad.elim (· hInc) (· hN)
  · omega

/-- A lane that exits has already issued its role's unique register request. -/
theorem exitAfterRegisterHint (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} (hx : X.get (g, index) = some ⟨pc, .exit⟩) :
    1 ≤ SetMaxNReg.ordinal X (g, index) := by
  have hg := Step.CtaBar.thread_lt_of_get hX hx
  have hPc := actualExitPc hX hx
  have hLate : 173 < pc := by omega
  obtain ⟨pos, t, o, hn, ht, hr, _⟩ := commonPrefixBeforeHint hp hX hg hx hLate
  have hIndex : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  have hSuffix : (X.tr g).drop pos ≠ [] :=
    fun h => (Nat.not_le_of_lt hIndex) ((List.drop_eq_nil_iff.mp h).trans hn)
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  obtain ⟨u, inst, hReq, _, _⟩ := firstRegisterHintFromCommon hp hg warp ht hr hSuffix
  have hBefore : pos < index := by
    rcases Nat.eq_or_lt_of_le hn with rfl | hLt
    · have hKind := congrArg Event.kind (Option.some.inj (hx.symm.trans hReq))
      cases hKind
    · exact hLt
  by_contra hc
  have hZero : SetMaxNReg.ordinal X (g, index) = 0 := by omega
  have hh := List.countP_eq_zero.mp hZero
  have hm : (⟨registerHintPc warp, .setMaxReg (registerHintOf warp.val).1
      (registerHintOf warp.val).2 inst⟩ : Event) ∈ (X.tr g).take index := by
    apply List.mem_of_getElem? (i := pos)
    rw [List.getElem?_take_of_lt hBefore]
    exact hReq
  exact hh _ hm rfl

/-- Register adjustments neither diverge on their source PC nor outlast an exiting peer. -/
theorem noRegisterAlignmentMismatch (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    :
    ¬ (AlignedClass.setMaxReg.Divergent l kernel X ∨
      AlignedClass.setMaxReg.Exited l kernel X) := by
  rintro (hd | hx)
  · obtain ⟨e, f, pc, pc', inc, inc', n, n', inst, inst', hw, he, hf, _, hb⟩ :=
      (AlignedClass.divergent_setMaxReg_iff l).mp hd
    obtain ⟨_, hp₁, _⟩ := registerRequestShape hp hX (g := e.1) (index := e.2) he
    obtain ⟨_, hp₂, _⟩ := registerRequestShape hp hX (g := f.1) (index := f.2) hf
    have hW : warpIndex l e.1 = warpIndex l f.1 := hw.2
    exact hb (hp₁.trans ((congrArg registerHintPc (Fin.ext hW)).trans hp₂.symm))
  · obtain ⟨e, pc, inc, n, inst, he, g, index, px, _, _, hh, hCount⟩ :=
      AlignedClass.exited_setMaxReg_old l hx
    obtain ⟨hOrd, _, _⟩ := registerRequestShape hp hX (g := e.1) (index := e.2) he
    have hOrdinal : SetMaxNReg.ordinal X e = 0 := hOrd
    have hBefore := exitAfterRegisterHint hp hX hh
    omega

end
end PTX.Kernels.TmlFa4Fwd
