-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputFootprint
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Tracked

@[expose] public section

/-! # Each actual non-coherent load stays in a declared input array -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NcInputTrace

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def wg0Bound (P : Params) : Wg0.Site → Prop
  | .sink => P.sinkBase.isSome = true
  | .lenOrig => P.topkLenBase.isSome = true
  | .lenExtra => P.extraTopkLenBase.isSome = true
  | _ => True

private theorem wg0_init (P : Params) (L : Launch) (g : Nat) :
    wg0Bound P (Wg0.init P L g).site := by
  simp only [Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen]
  repeat' split
  all_goals simp_all [wg0Bound]

set_option maxHeartbeats 1000000 in
private theorem wg0_next {g : Nat} {d d' : Wg0.D} {e : Event}
    (hn : Wg0.next P L g d e = some (some d')) : wg0Bound P d'.site := by
  cases hd : d.site <;> simp only [Wg0.next, Wg0.nextSite, hd, Wg0.waitStep,
    Wg0.writeStep, Option.bind, Option.map] at hn
  all_goals repeat' split at hn
  all_goals
    first
    | cases hn
    | (have hNext := Option.some.inj hn
       clear hn
       dsimp only at hNext
       split at hNext <;> cases hNext)
  all_goals try rw [hd]
  all_goals try simp only [Wg0.afterSink, Wg0.afterLen, Wg0.epiAfterBar, Wg0.afterScoreSite]
  all_goals repeat' split
  all_goals simp_all [wg0Bound]

private def idleBound (L : Launch) : Thread.Site → Prop
  | .loadTopk => Thread.ptrIsNull L 80 = false
  | .loadExtra => Thread.ptrIsNull L 144 = false
  | _ => True

private theorem idle_init (L : Launch) (g : Nat) :
    idleBound L (Thread.startSite L g) := by
  unfold Thread.startSite
  repeat' split
  all_goals simp_all [idleBound]

private theorem idle_next {s s' : Thread.Site} {e : Event}
    (hn : Thread.next L s e = some (some s')) : idleBound L s' := by
  cases s <;> simp only [Thread.next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [idleBound]

private def bindings (P : Params) (L : Launch) : Option Machine.ThreadD → Prop
  | some (.wg0 d) => wg0Bound P d.site
  | some (.idle s) => idleBound L s
  | _ => True

private theorem bindings_next {g : Nat} {d d' : Option Machine.ThreadD} {e : Event}
    (hn : (Machine.machine P L g).next d e = some d') : bindings P L d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> first | exact wg0_init P L g | trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first | exact idle_init L g | trivial
    case wg0 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d0 h
        cases hn
        exact wg0_next h
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case idle s =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i s' h
        cases hn
        exact idle_next h
      · cases hn
        trivial
      · split_ifs at hn
        cases hn
        trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals first | exact idle_init L g | trivial

private theorem bindings_at {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    bindings P L (some d) :=
  (hs.produces (hX.thr g (Frame.lt_of_get hX he))).prefix_induction
    (fun q _ => bindings P L q) trivial (fun _ _ _ _ _ _ _ hn => bindings_next hn)
    i (some d) hState

private theorem wg0_footprint {g i : Nat} {d : Wg0.D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hFire : (Machine.machine P L g).Fired (some (.wg0 d)) e o)
    (hSite : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) :
    NcInputEvent P e := by
  have hB : wg0Bound P d.site := bindings_at hX hs he hState
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  have hf : (Wg0.code P L g).toMachine.Fired (some d) e o := hFire
  rcases hSite with h | h | h
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (show P.sinkBase.isSome = true by simpa only [h, wg0Bound] using hB)
    obtain ⟨_, hr⟩ := LaunchReads.fired_sink hpre hp h hf
    exact NcInputEvent.sink hp (Wg0.head_lt L g) hr.1
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (show P.topkLenBase.isSome = true by simpa only [h, wg0Bound] using hB)
    obtain ⟨_, hr⟩ := LaunchReads.fired_main hpre hb hp h hf
    exact NcInputEvent.mainLength hp hb hr.1
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
      (show P.extraTopkLenBase.isSome = true by simpa only [h, wg0Bound] using hB)
    obtain ⟨_, hr⟩ := LaunchReads.fired_extra hpre hb hp h hf
    exact NcInputEvent.extraLength hp hb hr.1

/-- The idle role reads the optional length word for its actual batch row. -/
theorem idle_length_event {g i : Nat} {s : Thread.Site} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.idle s)))
    (hSite : s = .loadTopk ∨ s = .loadExtra) :
    ∃ ptr bs, (s = .loadTopk ∧ P.topkLenBase = some ptr ∨
      s = .loadExtra ∧ P.extraTopkLenBase = some ptr) ∧
      LaunchReads.ReadsLaunchWord e (ptr + 4 * Thread.ctaidY L g) bs := by
  have hg := Frame.lt_of_get hX he
  have hB : idleBound L s := bindings_at hX (hs g hg).machine he hState
  have hb : Thread.ctaidY L g < P.b := Wg1Mma.eOf_lt_b (g := g) hpre
  obtain ⟨t, ins, o, hAt, _, hCode, hFire⟩ := Frame.fired_site hs hX he hState
  change kernel.code[s.pc]? = some ins at hCode
  rcases hSite with h | h
  · subst s
    have hNonNull : Thread.ptrIsNull L 80 = false := hB
    cases hp : P.topkLenBase with
    | none => rw [Wg0.ptrIsNull_80_none hpre hp] at hNonNull; cases hNonNull
    | some ptr =>
      obtain rfl := Option.some.inj (hCode.symm.trans Flow.code_2596)
      rw [Thread.event_loadTopk hpre hAt] at hFire
      obtain ⟨bs, _, hKind, _⟩ := hFire
      have hn := hpre.topkLenBaseLt ptr hp
      have hSpan := (hpre.topkLenAddressable ptr hp).2.2
      have hAddr : ptr + 4 * Thread.ctaidY L g < 2 ^ 64 := by omega
      have hPtr := Thread.paramWord_80_some hpre hp
      rw [Nat.mod_eq_of_lt hn] at hPtr
      have hk := congrArg Event.kind hKind
      rw [hPtr, Nat.mod_eq_of_lt hAddr] at hk
      exact ⟨ptr, bs, .inl ⟨rfl, rfl⟩, hk, by rw [congrArg Event.pc hKind]; rfl⟩
  · subst s
    have hNonNull : Thread.ptrIsNull L 144 = false := hB
    cases hp : P.extraTopkLenBase with
    | none => rw [Wg0.ptrIsNull_144_none hpre hp] at hNonNull; cases hNonNull
    | some ptr =>
      obtain rfl := Option.some.inj (hCode.symm.trans Flow.code_2601)
      rw [Thread.event_loadExtra hpre hAt] at hFire
      obtain ⟨bs, _, hKind, _⟩ := hFire
      have hn := hpre.extraTopkLenBaseLt ptr hp
      have hSpan := (hpre.extraTopkLenAddressable ptr hp).2.2
      have hAddr : ptr + 4 * Thread.ctaidY L g < 2 ^ 64 := by omega
      have hPtr := Thread.paramWord_144_some hpre hp
      rw [Nat.mod_eq_of_lt hn] at hPtr
      have hk := congrArg Event.kind hKind
      rw [hPtr, Nat.mod_eq_of_lt hAddr] at hk
      exact ⟨ptr, bs, .inr ⟨rfl, rfl⟩, hk, by rw [congrArg Event.pc hKind]; rfl⟩

private theorem idle_footprint {g i : Nat} {s : Thread.Site} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.idle s)))
    (hSite : s = .loadTopk ∨ s = .loadExtra) : NcInputEvent P e := by
  obtain ⟨_, _, hPtr, hEvent⟩ := idle_length_event hpre hX hs he hState hSite
  have hb : Thread.ctaidY L g < P.b := Wg1Mma.eOf_lt_b (g := g) hpre
  rcases hPtr with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact NcInputEvent.mainLength hp hb hEvent.1
  · exact NcInputEvent.extraLength hp hb hEvent.1

private def NcRole : Machine.ThreadD → Prop
  | .wg0 d => d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra
  | .mma d => d.site = .loadTopk ∨ d.site = .loadExtra
  | .tma d => d.site = .lenOrig ∨ d.site = .lenExtra
  | .index d => d.site = .lenOrig ∨ d.site = .lenExtra ∨
      ∃ extra first hi, d.site = .pair extra first hi
  | .wg2 d => d.site = .lenOrig ∨ d.site = .lenExtra
  | .idle s => s = .loadTopk ∨ s = .loadExtra
  | _ => False

local macro "exclude_nc " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

private theorem nc_role {g : Nat} {d : Machine.ThreadD}
    (h : ncLoads.contains ((Machine.code P L g).pc d) = true) : NcRole d := by
  cases d
  case wg0 d =>
    change ncLoads.contains d.site.pc = true at h
    change d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first
      | exact .inl rfl
      | exact .inr (.inl rfl)
      | exact .inr (.inr rfl)
      | exclude_nc h
  case mma d =>
    change ncLoads.contains d.site.pc = true at h
    change d.site = .loadTopk ∨ d.site = .loadExtra
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | exact .inl rfl | exact .inr rfl | exclude_nc h
  case tma d =>
    change ncLoads.contains d.site.pc = true at h
    change d.site = .lenOrig ∨ d.site = .lenExtra
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | exact .inl rfl | exact .inr rfl | exclude_nc h
  case index d =>
    change ncLoads.contains d.site.pc = true at h
    change d.site = .lenOrig ∨ d.site = .lenExtra ∨ ∃ extra first hi, d.site = .pair extra first hi
    generalize d.site = s at h ⊢
    clear d
    cases s
    case lenOrig => exact .inl rfl
    case lenExtra => exact .inr (.inl rfl)
    case pair extra first hi => exact .inr (.inr ⟨extra, first, hi, rfl⟩)
    all_goals exclude_nc h
  case wg2 d =>
    change ncLoads.contains d.site.pc = true at h
    change d.site = .lenOrig ∨ d.site = .lenExtra
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | exact .inl rfl | exact .inr rfl | exclude_nc h
  case idle s =>
    change ncLoads.contains s.pc = true at h
    change s = .loadTopk ∨ s = .loadExtra
    cases s <;> first | exact .inl rfl | exact .inr rfl | exclude_nc h
  case prologue s =>
    change ncLoads.contains s.pc = true at h
    cases s <;> exclude_nc h
  case head =>
    change ncLoads.contains 1843 = true at h
    exclude_nc h
  case done =>
    change ncLoads.contains 3611 = true at h
    exclude_nc h

/-- The footprint of an actual non-coherent read selected by the kernel's read-only rule. -/
theorem footprint {g i : Nat} {e : Event} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hNc : ncLoads.contains e.pc = true)
    (hk : e.kind = .nc a bs) : NcInputFootprint P a := by
  have hg := Frame.lt_of_get hX he
  have hSound := (hs g hg).machine
  obtain ⟨d, hState⟩ := Frame.event_state hs hX ht he (by
    intro tag fault h
    have hKind := congrArg Event.kind h
    rw [hk] at hKind
    cases hKind)
  obtain ⟨o, hFire⟩ := RingEvents.fired_of_trace hX hSound he hState
  have hTag : e.pc = (Machine.code P L g).pc d := by
    obtain ⟨t, hAt, hf⟩ := hFire
    exact (fires_pc hf).trans hAt.1.1
  have hr := nc_role (P := P) (L := L) (g := g) (d := d) (hTag ▸ hNc)
  apply (show NcInputEvent P e from ?_) a bs hk
  cases d with
  | wg0 d => exact wg0_footprint hpre hX hSound he hState hFire hr
  | mma d => exact MmaTracking.length_footprint hpre (PTX.len_of_get he) hState hr hFire
  | tma d => exact TmaTracking.length_footprint hpre hr hFire
  | index d => exact Wg1Index.nc_input_footprint hpre hX hSound he hState hr
  | wg2 d => exact Wg2.length_footprint hpre hX hSound he hState hr hFire
  | idle s => exact idle_footprint hpre hX hs he hState hr
  | prologue _ | head | done => exact (show False from hr).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NcInputTrace
