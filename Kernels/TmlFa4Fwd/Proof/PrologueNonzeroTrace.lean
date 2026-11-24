-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueTrace
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof

noncomputable section

/-- The shared addresses and ABI registers present after the common CTA barrier. -/
def nonzeroBarrierFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 (warpIndex l g)), (2535, b32 l.sharedBase),
   (1063, b32 (l.sharedBase + 32)), (1064, b32 (l.sharedBase + 16)),
   (1065, b32 (l.sharedBase + 80)), (1066, b32 (l.sharedBase + 56)),
   (1067, b32 (l.sharedBase + 112)), (1068, b32 (l.sharedBase + 96)),
   (6495, b32 (l.sharedBase + 144)), (2390, b32 (l.sharedBase + 208)),
   (1069, b32 (l.sharedBase + 192)), (1070, b32 (l.sharedBase + 320)),
   (6497, b32 (l.sharedBase + 224)), (1071, b32 (l.sharedBase + 336))] ++ abiFacts p l

private theorem hasLaterEvent {X : Execution} {g i pc : Nat} {e : Event}
    (hLast : (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (he : X.get (g, i) = some e) (hn : e.kind ≠ .exit) : i + 1 < (X.tr g).length := by
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  by_contra hb
  have hp : (X.tr g).length - 1 = i := by omega
  change (X.tr g)[i]? = some e at he
  rw [List.getLast?_eq_getElem?, hp, he] at hLast
  exact hn (congrArg Event.kind (Option.some.inj hLast))

private theorem preservesAbi {p : Params} {l : Launch} {t u : TState}
    (ht : Holds t.regs (abiFacts p l))
    (h : ∀ r ∉ [18, 19, 1063, 22, 1064, 1065, 27, 1066, 1067, 32, 1068, 6495,
      37, 42, 2390, 47, 1069, 1070, 52, 6497, 57, 1071], u.regs r = t.regs r) :
    Holds u.regs (abiFacts p l) := by
  have keep (r : Nat) (hr : r ∈ (abiFacts p l).map Prod.fst) : u.regs r = t.regs r := by
    apply h
    change r ∈ [1, 7492, 7493, 7494, 7495, 1663, 1664, 7496, 7497, 7498, 7499, 7500, 7501,
      7502, 7503, 7504, 7505, 7291, 7290, 7289, 7506, 7292, 7293, 7294, 7295, 1665] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  generalize hF : abiFacts p l = F at ht keep ⊢
  clear hF
  induction F with
  | nil => trivial
  | cons a rest ih =>
    exact ⟨(keep a.1 (by simp)).trans ht.1,
      ih ht.2 (fun r hr => keep r (by simp [hr]))⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- In a complete execution each nonzero warp reaches the role split with an actual Run,
after its three broadcasts, the mbarrier initialization fence and the CTA barrier. -/
theorem nonzeroAfterCommonBarrierWithTid (hComplete : Complete l X) {g : Nat} (hg : g < l.threads)
    (hWarp : 0 < warpIndex l g) :
    ∃ t, At t 174 (nonzeroBarrierFacts p l g) ∧
      t.regs 1061 = some (b32 (g % l.block)) ∧
      X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧ X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) none := by
  obtain ⟨pc, hLast⟩ := (hComplete.1 g hg).resolve_left (noCanceled hX)
  have h₀ : 0 < (X.tr g).length := by
    rw [List.getLast?_eq_getElem?] at hLast
    have := (List.getElem?_eq_some_iff.mp hLast).1
    omega
  let e₀ := (X.tr g)[0]
  have he₀ : X.get (g, 0) = some e₀ := List.getElem?_eq_getElem h₀
  have h₁ : 1 < (X.tr g).length := hasLaterEvent hLast he₀
    (by rw [firstSharedValue hp hX g hg he₀]; intro h; cases h)
  let e₁ := (X.tr g)[1]
  have he₁ : X.get (g, 1) = some e₁ := List.getElem?_eq_getElem h₁
  have h₂ : 2 < (X.tr g).length := hasLaterEvent hLast he₁
    (by rw [secondWarpValue hp hX g hg he₁]; intro h; cases h)
  let e₂ := (X.tr g)[2]
  have he₂ : X.get (g, 2) = some e₂ := List.getElem?_eq_getElem h₂
  have h₃ : 3 < (X.tr g).length := hasLaterEvent hLast he₂
    (by rw [thirdWarpValue hp hX g hg he₂]; intro h; cases h)
  have hTrace : X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
    have h0 := List.drop_eq_getElem_cons h₀
    have h1 := List.drop_eq_getElem_cons h₁
    have h2 := List.drop_eq_getElem_cons h₂
    rw [h2] at h1
    rw [h1] at h0
    exact h0
  obtain ⟨t, o, hPc, hFault, hBase, hIndex, hTid, hAbi, hSub, hAcc, hr⟩ :=
    broadcastPrefixWithTid hp hX g hg hTrace
  have hRun : Run kernel Assumptions.all l g t ((X.tr g).drop 3) none := by
    cases o with
    | none => exact hr
    | some u =>
      have hSuffix : ((X.tr g).drop 3).getLast? = some ⟨pc, .exit⟩ := by
        rw [List.getLast?_drop, ite_eq_right (Nat.not_le.mpr h₃), hLast]
      rw [List.getLast?_eq_getElem?] at hSuffix
      exact (hr.no_exit hSuffix).elim
  obtain ⟨s, hs, hPs, hFs, h32, h16, h80, h56, h112, h96, h144, h208, h192, h320, h224, h336,
      hSubS, hAccS, hFrame⟩ :=
    nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t hWarp (warpIndex_lt hp g)
      hPc hFault hIndex hBase
  have hFenceOut : out kernel [] l g s = .ev (.fenceMbarInit (next s)) := by
    unfold out
    rw [hPs, hFs, Flow.code_172]
    rfl
  have hFence : Next kernel Assumptions.all l g t s (.fenceMbarInit (next s)) :=
    ⟨run_rtg hs, startupOut (.inl (by rw [hPs]; decide)) hFenceOut⟩
  obtain ⟨e, u, he, hf, hu⟩ := hFence.continuing_at (by
    rintro e ⟨_, h⟩
    cases h) hRun
  obtain ⟨rfl, hU⟩ := hf
  obtain rfl := Option.some.inj hU
  have hPu : (next s).pc = 173 := by change s.pc + 1 = 173; rw [hPs]
  have hBarOut : out kernel [] l g (next s) = .ev (.bar 0 (next (next s)) none .sync) := by
    unfold out
    have hf : (next s).fault = none := hFs
    rw [hPu, hf, Flow.code_173]
    rfl
  have hBar : Next kernel Assumptions.all l g (next s) (next s)
      (.bar 0 (next (next s)) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hPu]; decide)) hBarOut⟩
  obtain ⟨f, v, hf, hFire, hv⟩ := hBar.continuing_at (pos := 4) (by
    rintro e ⟨_, h⟩
    cases h) hu
  obtain ⟨rfl, hV⟩ := hFire
  obtain rfl := Option.some.inj hV
  rw [hPs] at he
  rw [hPu] at hf
  refine ⟨next (next s), ⟨?_, hSubS.trans hSub, hAccS.trans hAcc, hFs, ?_⟩,
    (hFrame 1061 (by decide)).trans hTid, he, hf, hv⟩
  · change (next s).pc + 1 = 174
    rw [hPu]
  · exact ⟨(hFrame 1062 (by decide)).trans hIndex, (hFrame 2535 (by decide)).trans hBase,
      h32, h16, h80, h56, h112, h96, h144, h208, h192, h320, h224, h336,
      preservesAbi hAbi hFrame⟩

/-- A nonzero lane with at least five actual records passes the common barrier and has
its exact ABI and shared layout, whether the rest of the run finishes or stops early. -/
private theorem nonzeroCommonPrefixUsing {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g)
    (hThree : 3 ≤ (X.tr g).length)
    (hAvailable : ∀ n ≤ 4,
      (n = 4 → X.get (g, 3) = some ⟨172, .fenceMbarInit⟩) → n < (X.tr g).length) :
    ∃ t o, At t 174 (nonzeroBarrierFacts p l g) ∧ t.regs 1061 = some (b32 (g % l.block)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 5) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o ∧
      (∀ j < 5, ∀ e, X.get (g, j) = some e → e.pc < 174) ∧
      X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧
      X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ := by
  have h0 : 0 < (X.tr g).length := by omega
  have h1 : 1 < (X.tr g).length := by omega
  have h2 : 2 < (X.tr g).length := by omega
  have earlier3 (j : Nat) (hj : j < 3) (e : Event) (he : X.get (g, j) = some e) :
      e.pc < 174 := by
    interval_cases j
    · rw [firstSharedValue hp hX g hg he]; exact (by decide : (25 : Nat) < 174)
    · rw [secondWarpValue hp hX g hg he]; exact (by decide : (34 : Nat) < 174)
    · rw [thirdWarpValue hp hX g hg he]; exact (by decide : (35 : Nat) < 174)
  have h3 := hAvailable 3 (by decide) (fun h => ((by decide : (3 : Nat) ≠ 4) h).elim)
  let e₀ := (X.tr g)[0]
  let e₁ := (X.tr g)[1]
  let e₂ := (X.tr g)[2]
  have hTrace : X.tr g = e₀ :: e₁ :: e₂ :: (X.tr g).drop 3 := by
    have ha := List.drop_eq_getElem_cons h0
    have hb := List.drop_eq_getElem_cons h1
    have hc := List.drop_eq_getElem_cons h2
    rw [hc] at hb
    rw [hb] at ha
    exact ha
  obtain ⟨t, o, hPc, hFault, hBase, hIndex, hTid, hAbi, hSub, hAcc, hTail, hPrefix⟩ :=
    broadcastPrefixRun hp hX g hg hTrace
  obtain ⟨s, hs, hPs, hFs, h32, h16, h80, h56, h112, h96, h144, h208, h192, h320, h224, h336,
      hSubS, hAccS, hFrame⟩ :=
    nonzeroWarpWith (A := Assumptions.all) hp g (warpIndex l g) t hWarp (warpIndex_lt hp g)
      hPc hFault hIndex hBase
  have hFenceOut : out kernel [] l g s = .ev (.fenceMbarInit (next s)) := by
    unfold out
    rw [hPs, hFs, Flow.code_172]
    rfl
  have hFence : Next kernel Assumptions.all l g t s (.fenceMbarInit (next s)) :=
    ⟨run_rtg hs, startupOut (.inl (by rw [hPs]; decide)) hFenceOut⟩
  rw [List.drop_eq_getElem_cons h3] at hTail
  obtain ⟨u, ⟨he, hu⟩, hRest⟩ := hFence.continuing_event (by
    rintro ⟨_, hh⟩
    cases hh) hTail
  obtain rfl := Option.some.inj hu
  have hPu : (next s).pc = 173 := by change s.pc + 1 = 173; rw [hPs]
  have hBarOut : out kernel [] l g (next s) = .ev (.bar 0 (next (next s)) none .sync) := by
    unfold out
    have hf : (next s).fault = none := hFs
    rw [hPu, hf, Flow.code_173]
    rfl
  have hBar : Next kernel Assumptions.all l g (next s) (next s)
      (.bar 0 (next (next s)) none .sync) :=
    ⟨.refl, startupOut (.inl (by rw [hPu]; decide)) hBarOut⟩
  have hFenceGet : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ := by
    rw [show X.get (g, 3) = some (X.tr g)[3] from List.getElem?_eq_getElem h3, he, hPs]
  have earlier4 (j : Nat) (hj : j < 4) (e : Event) (he : X.get (g, j) = some e) :
      e.pc < 174 := by
    by_cases heq : j = 3
    · subst j
      rw [hFenceGet] at he
      obtain rfl := Option.some.inj he
      decide
    · exact earlier3 j (by omega) e he
  have h4 := hAvailable 4 (by decide) (fun _ => hFenceGet)
  rw [List.drop_eq_getElem_cons h4] at hRest
  obtain ⟨v, ⟨hf, hv⟩, hRest⟩ := hBar.continuing_event (by
    rintro ⟨_, hh⟩
    cases hh) hRest
  obtain rfl := Option.some.inj hv
  have hTake : (X.tr g).take 3 = [e₀, e₁, e₂] := by
    conv_lhs => rw [hTrace]
    rfl
  have hRun : Run kernel Assumptions.all l g {} ((X.tr g).take 3) (some t) :=
    hTake ▸ hPrefix
  have heStep : EStep kernel Assumptions.all l g s (X.tr g)[3] (some (next s)) :=
    ⟨_, hFence.stop, he, rfl⟩
  have hfStep : EStep kernel Assumptions.all l g (next s) (X.tr g)[4] (some (next (next s))) :=
    ⟨_, hBar.stop, hf, rfl⟩
  have h4Run : Run kernel Assumptions.all l g {} ((X.tr g).take 4) (some (next s)) := by
    rw [show 4 = 3 + 1 by decide, List.take_succ_eq_append_getElem h3]
    exact hRun.snoc hFence.steps heStep
  have h5Run : Run kernel Assumptions.all l g {} ((X.tr g).take 5) (some (next (next s))) := by
    rw [show 5 = 4 + 1 by decide, List.take_succ_eq_append_getElem h4]
    exact h4Run.snoc .refl hfStep
  have hBarGet : X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ := by
    rw [show X.get (g, 4) = some (X.tr g)[4] from List.getElem?_eq_getElem h4, hf, hPu]
  have earlier5 (j : Nat) (hj : j < 5) (e : Event) (he : X.get (g, j) = some e) :
      e.pc < 174 := by
    by_cases heq : j = 4
    · subst j
      rw [hBarGet] at he
      obtain rfl := Option.some.inj he
      decide
    · exact earlier4 j (by omega) e he
  refine ⟨next (next s), o, ⟨?_, hSubS.trans hSub, hAccS.trans hAcc, hFs, ?_⟩,
    (hFrame 1061 (by decide)).trans hTid, h5Run, hRest, earlier5, hFenceGet, hBarGet⟩
  · change (next s).pc + 1 = 174
    rw [hPu]
  · exact ⟨(hFrame 1062 (by decide)).trans hIndex, (hFrame 2535 (by decide)).trans hBase,
      h32, h16, h80, h56, h112, h96, h144, h208, h192, h320, h224, h336,
      preservesAbi hAbi hFrame⟩

/-- A nonzero lane with at least five actual records passes the common barrier and has
its exact ABI and shared layout, whether the rest of the run finishes or stops early. -/
theorem nonzeroCommonPrefix {g : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g)
    (hl : 5 ≤ (X.tr g).length) :
    ∃ t o, At t 174 (nonzeroBarrierFacts p l g) ∧ t.regs 1061 = some (b32 (g % l.block)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 5) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o := by
  obtain ⟨t, o, ht, hTid, hPrefix, hTail, _⟩ :=
    nonzeroCommonPrefixUsing hp hX hg hWarp (by omega) (fun _ h _ => by omega)
  exact ⟨t, o, ht, hTid, hPrefix, hTail⟩

/-- A later event, exit, or fourth shuffle forces the nonzero lane through the common barrier. -/
theorem nonzeroCommonPrefixOfDemand {g index : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g)
    {e : Event} (he : X.get (g, index) = some e)
    (hDemand : 173 < e.pc ∨ e.kind = .exit ∨ 3 ≤ index ∧ Execution.isShfl e = true) :
    ∃ t o, 5 ≤ index ∧ At t 174 (nonzeroBarrierFacts p l g) ∧
      t.regs 1061 = some (b32 (g % l.block)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o ∧
      X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧ X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ := by
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hEarly {k : Nat} {other : Event} (hr : X.get (g, k) = some other)
      (hPc : other.pc ≤ 173) (hExit : other.kind ≠ .exit)
      (hShfl : k < 3 ∨ Execution.isShfl other = false) : index ≠ k := by
    intro hk
    subst k
    obtain rfl := Option.some.inj (he.symm.trans hr)
    rcases hDemand with h | h | ⟨hj, h⟩
    · omega
    · exact hExit h
    · rcases hShfl with hearly | hFalse
      · omega
      · cases hFalse.symm.trans h
  have hFirst : 3 ≤ index := by
    by_contra h
    have hi : index < 3 := by omega
    interval_cases index
    · exact hEarly (firstSharedValue hp hX g hg he ▸ he) (by change 25 ≤ 173; decide)
        (by intro h; cases h) (.inl (by decide)) rfl
    · exact hEarly (secondWarpValue hp hX g hg he ▸ he) (by change 34 ≤ 173; decide)
        (by intro h; cases h) (.inl (by decide)) rfl
    · exact hEarly (thirdWarpValue hp hX g hg he ▸ he) (by change 35 ≤ 173; decide)
        (by intro h; cases h) (.inl (by decide)) rfl
  have hFenceBefore (h : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩) : 4 ≤ index := by
    have hNe := hEarly h (by decide) (by intro h; cases h) (.inr rfl)
    omega
  have hAvailable (n : Nat) (hn : n ≤ 4)
      (hFence : n = 4 → X.get (g, 3) = some ⟨172, .fenceMbarInit⟩) :
      n < (X.tr g).length := by
    by_cases h : n = 4
    · have := hFenceBefore (hFence h)
      omega
    · omega
  obtain ⟨t, o, ht, hTid, _, hr, _, hFence, hBar⟩ :=
    nonzeroCommonPrefixUsing hp hX hg hWarp (by omega) hAvailable
  have hFour := hFenceBefore hFence
  have hNe := hEarly hBar (by decide) (by intro h; cases h) (.inr rfl)
  exact ⟨t, o, by omega, ht, hTid, hr, hFence, hBar⟩


/-- An observed event past startup establishes the actual role entry for a nonzero warp. -/
theorem nonzeroCommonPrefixOfLateEvent {g index : Nat} (hg : g < l.threads)
    (hWarp : 0 < warpIndex l g) {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ t o, 5 ≤ index ∧ At t 174 (nonzeroBarrierFacts p l g) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o := by
  obtain ⟨t, o, hi, ht, _, hr, _, _⟩ := nonzeroCommonPrefixOfDemand hp hX hg hWarp he (.inl hPc)
  exact ⟨t, o, hi, ht, hr⟩


/-- The startup cursor also retains the issuing lane's CTA-local thread index. -/
theorem nonzeroCommonPrefixOfLateEventWithTid {g index : Nat} (hg : g < l.threads)
    (hWarp : 0 < warpIndex l g) {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    ∃ t o, 5 ≤ index ∧ At t 174 (nonzeroBarrierFacts p l g) ∧
      t.regs 1061 = some (b32 (g % l.block)) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) o := by
  obtain ⟨t, o, hi, ht, hTid, hr, _, _⟩ := nonzeroCommonPrefixOfDemand hp hX hg hWarp he (.inl hPc)
  exact ⟨t, o, hi, ht, hTid, hr⟩

/-- A nonzero lane that issues a role instruction has already passed the common barrier. -/
theorem nonzeroStartupBar {g index : Nat} (hg : g < l.threads) (hWarp : 0 < warpIndex l g)
    {e : Event} (he : X.get (g, index) = some e) (hPc : 173 < e.pc) :
    4 < index ∧ X.IsBarrier (g, 4) 0 none 173 ∧
      (∀ k < 4, ∀ e, X.get (g, k) = some e → e.pc < 173) := by
  obtain ⟨_, _, hi, _, _, _, hFence, hBar⟩ :=
    nonzeroCommonPrefixOfDemand hp hX hg hWarp he (.inl hPc)
  refine ⟨by omega, hBar, ?_⟩
  intro k hk ev hGet
  interval_cases k
  · rw [firstSharedValue hp hX g hg hGet]; exact (show 25 < 173 by decide)
  · rw [secondWarpValue hp hX g hg hGet]; exact (show 34 < 173 by decide)
  · rw [thirdWarpValue hp hX g hg hGet]; exact (show 35 < 173 by decide)
  · rw [hFence] at hGet
    obtain rfl := Option.some.inj hGet
    decide

theorem nonzeroAfterCommonBarrier (hComplete : Complete l X) {g : Nat} (hg : g < l.threads)
    (hWarp : 0 < warpIndex l g) :
    ∃ t, At t 174 (nonzeroBarrierFacts p l g) ∧
      X.get (g, 3) = some ⟨172, .fenceMbarInit⟩ ∧ X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩ ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 5) none := by
  obtain ⟨t, ht, _, hf, hb, hr⟩ := nonzeroAfterCommonBarrierWithTid hp hX hComplete hg hWarp
  exact ⟨t, ht, hf, hb, hr⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
