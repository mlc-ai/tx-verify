-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
public import Lemmas.Flow.NotInit
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # Initializations originate in the prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingInitSources

open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000 in
private theorem init_sites : OpPcsFast kernel.code initOp Flow.mbarInit.toList = true := by
  decide +kernel

private theorem init_pc_of_fired {P : Params} {L : Launch} {g : Nat}
    {d : Machine.ThreadD} {e : Event} {o : Option TState} {m : Loc} {count : Nat}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .mbInit m count) :
    (Machine.code P L g).pc d ∈ Flow.mbarInit.toList := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    cases hop : initOp ins.op
    · exact (notInit_of_op hop hf m count hk).elim
    · exact OpPcsFast.mem init_sites hc hop

local macro "decide_site" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private theorem role_start_after_init {P : Params} {L : Launch} {g : Nat} (d : Machine.ThreadD) :
    match d with
    | .prologue _ => True
    | _ => 100 ≤ (Machine.code P L g).pc d := by
  cases d
  case prologue => trivial
  case wg0 q =>
    change 100 ≤ q.site.pc
    cases q.site <;> decide_site
  case mma q =>
    change 100 ≤ q.site.pc
    cases q.site <;> decide_site
  case tma q =>
    change 100 ≤ q.site.pc
    cases q.site <;> decide_site
  case index q =>
    change 100 ≤ q.site.pc
    cases q.site <;> decide_site
  case wg2 q =>
    change 100 ≤ q.site.pc
    cases q.site <;> decide_site
  case idle q =>
    change 100 ≤ q.pc
    cases q <;> decide
  case head => change 100 ≤ 1843; decide
  case done => change 100 ≤ 3611; decide

private theorem prologue_init_site (s : Site) (h : s.pc ∈ Flow.mbarInit.toList) :
    ∃ j, s = .init j := by
  cases s
  case init j => exact ⟨j, rfl⟩
  all_goals
    revert h
    decide_site

/-- An initialization in a followed machine state is one of its prologue entries. -/
theorem init_site {P : Params} {L : Launch} {g : Nat}
    {d : Machine.ThreadD} {e : Event} {o : Option TState} {m : Loc} {count : Nat}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .mbInit m count) :
    ∃ j, d = .prologue (.init j) := by
  have hm := init_pc_of_fired hf hk
  have hlt : (Machine.code P L g).pc d < 100 :=
    of_decide_eq_true (List.all_eq_true.mp (show Flow.mbarInit.toList.all
      (fun site => decide (site < 100)) = true by decide) _ hm)
  have hge := role_start_after_init (P := P) (L := L) (g := g) d
  cases d
  case prologue s =>
    obtain ⟨j, rfl⟩ := prologue_init_site s hm
    exact ⟨j, rfl⟩
  all_goals
    change 100 ≤ _ at hge
    omega

variable {P : Params} {L : Launch}

/-- A traced initialization identifies the prologue's entry and its exact object and count. -/
theorem init_from_trace {mem0 : Mem0} {X : Execution} {g i : Nat} {e : Event} {m : Loc}
    {count : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (htracked : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .mbInit m count) :
    ∃ j, Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))) ∧
      m = ⟨.shared, g / L.block, L.sharedBase + initOff j⟩ ∧ count = initCount j := by
  have hg := Frame.lt_of_get hX he
  rcases (hs.produces (hX.thr g hg)).fired he with ⟨s, o, hst, hf⟩ | ⟨_, _, _, rfl⟩
  · cases s with
    | none => exact ((htracked g i hg) hst).elim
    | some d =>
      obtain ⟨j, rfl⟩ := init_site hf hk
      exact ⟨j, hst, Kind.mbInit.inj (hk.symm.trans (RingEvents.barrier_init hpre hf))⟩
  · contradiction


private def prologueRank : Site → Nat
  | .shfl0 => 0
  | .shfl1 => 1
  | .elect0 => 2
  | .elect1 => 3
  | .init j => 4 + j.val
  | .fence => 27
  | .alloc => 28
  | .allocStore => 29
  | .allocRead => 30
  | .relinquish => 31
  | .barrier => 32
  | .handoff _ => 33

private def rank : Option (Option Machine.ThreadD) → Nat
  | some (some (.prologue s)) => prologueRank s
  | _ => 34

private theorem next_nondecreasing {g : Nat} (d : Machine.ThreadD) (e : Event) :
    rank (some (some d)) ≤ rank (Machine.next P L g d e) := by
  generalize hn : Machine.next P L g d e = nextState
  cases d
  case prologue st =>
    cases st
    case init j =>
      have hj := j.isLt
      simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
      split at hn <;> cases hn <;> simp [rank, prologueRank]
      omega
    case handoff wg =>
      simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
      split at hn
      · fin_cases wg <;> cases hn <;> simp [rank, prologueRank, Machine.roleStart]
      · cases hn
        simp [rank, prologueRank]
    all_goals
      cases hk : e.kind <;> simp only [Machine.next,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at hn
    case shfl1.shfl mode a b c recv ok =>
      cases recv <;> try dsimp only at hn
      all_goals repeat' first | split_ifs at hn | split at hn
      all_goals cases hn
      all_goals simp_all [rank, prologueRank]
      all_goals subst_vars
      all_goals decide
    case alloc.tc k =>
      cases k
      case resource group dst req =>
        cases req <;> simp at hn
        all_goals try split_ifs at hn
        all_goals cases hn
        all_goals simp [rank, prologueRank]
      all_goals simp at hn
      all_goals cases hn
      all_goals simp [rank, prologueRank]
    case allocRead.rd a bs =>
      cases hreb : rebuild 3 bs >>= allocWord L g <;> simp only [hreb] at hn
      all_goals repeat' first | split_ifs at hn | split at hn
      all_goals cases hn
      all_goals simp_all [rank, prologueRank]
      all_goals subst_vars
      all_goals decide
    all_goals
      repeat' split at hn
      all_goals cases hn
      all_goals simp [rank, prologueRank]
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, Machine.headStart, hk] at hn
    case shfl => split_ifs at hn <;> cases hn <;> simp [rank]
    all_goals cases hn
    all_goals simp [rank]
  all_goals
    simp only [Machine.next] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals simp [rank]

private theorem rank_step {g : Nat} (state : Option (Option Machine.ThreadD)) (e : Event) :
    rank state ≤ rank (state.bind fun s => (Machine.machine P L g).next s e) := by
  cases state with
  | none => exact Nat.le_refl _
  | some s =>
    cases s with
    | none =>
      change rank (some none) ≤ rank (some none)
      decide
    | some d => exact next_nondecreasing (P := P) (L := L) (g := g) d e

private theorem rank_mono {X : Execution} {g : Nat} :
    Monotone (fun k => rank (Frame.stateAt (Machine.code P L) X g k)) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < (X.tr g).length
  · have he := List.getElem?_eq_getElem hk
    rw [Frame.stateAt_succ he]
    exact rank_step (P := P) (L := L) (g := g) _ _
  · rw [Frame.stateAt_of_le (by omega : (X.tr g).length ≤ k),
      Frame.stateAt_of_le (by omega : (X.tr g).length ≤ k + 1)]

private theorem init_rank_succ {X : Execution} {g i : Nat} {j : Fin 23} {e : Event}
    (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j)))) :
    rank (Frame.stateAt (Machine.code P L) X g (i + 1)) = 4 + j.val + 1 := by
  rw [Frame.stateAt_succ he, hst]
  change rank (Machine.next P L g (.prologue (.init j)) e) = _
  have hj := j.isLt
  simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]
  split <;> simp [rank, prologueRank] <;> omega

/-- A followed thread reaches a prologue initialization entry at most once in its event trace. -/
theorem init_entry_unique {X : Execution} {g i k : Nat} {j : Fin 23} {e f : Event}
    (he : X.get (g, i) = some e) (hf : X.get (g, k) = some f)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))))
    (hk : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue (.init j)))) :
    i = k := by
  have before {a b : Nat} {evt : Event} (hab : a < b) (ha : X.get (g, a) = some evt)
      (hStateA : Frame.stateAt (Machine.code P L) X g a = some (some (.prologue (.init j))))
      (hStateB : Frame.stateAt (Machine.code P L) X g b = some (some (.prologue (.init j)))) :
      False := by
    have hr := rank_mono (P := P) (L := L) (X := X) (g := g) (Nat.succ_le_of_lt hab)
    change rank (Frame.stateAt (Machine.code P L) X g (a + 1)) ≤
      rank (Frame.stateAt (Machine.code P L) X g b) at hr
    rw [init_rank_succ ha hStateA, hStateB] at hr
    simp [rank, prologueRank] at hr
  rcases Nat.lt_trichotomy i k with h | h | h
  · exact (before h he hi hk).elim
  · exact h
  · exact (before h hf hk hi).elim

private theorem first_crossing {X : Execution} {g i q : Nat} (hq : 0 < q) (hq' : q ≤ 34)
    (hi : i < (X.tr g).length) (hr : q ≤ rank (Frame.stateAt (Machine.code P L) X g i)) :
    ∃ k e d, k < i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some d) ∧
      rank (some (some d)) < q ∧
      q ≤ rank (Machine.next P L g d e) ∧
      rank (Machine.next P L g d e) ≤ rank (Frame.stateAt (Machine.code P L) X g i) := by
  let condition := fun t => q ≤ rank (Frame.stateAt (Machine.code P L) X g t)
  have hExists : ∃ t, condition t := ⟨i, hr⟩
  have hLeast : Nat.find hExists ≤ i := Nat.find_min' hExists hr
  have hZero : ¬ condition 0 := by
    unfold condition
    rw [Frame.stateAt_zero]
    change ¬ q ≤ 0
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Nat.find hExists ≠ 0 from fun h => hZero (h ▸ Nat.find_spec hExists))
  have hki : k < i := by omega
  have hkr : rank (Frame.stateAt (Machine.code P L) X g k) < q :=
    Nat.lt_of_not_ge (Nat.find_min hExists (by omega : k < Nat.find hExists))
  have hcut := Nat.find_spec hExists
  rw [hk] at hcut
  change q ≤ rank (Frame.stateAt (Machine.code P L) X g (k + 1)) at hcut
  have hupper := rank_mono (P := P) (L := L) (X := X) (g := g) (by omega : k + 1 ≤ i)
  change rank (Frame.stateAt (Machine.code P L) X g (k + 1)) ≤ _ at hupper
  have hkl : k < (X.tr g).length := Nat.lt_trans hki hi
  have he : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hkl
  cases hD : Frame.stateAt (Machine.code P L) X g k with
  | none =>
    rw [hD] at hkr
    change 34 < q at hkr
    omega
  | some s =>
    cases s with
    | none =>
      rw [hD] at hkr
      change 34 < q at hkr
      omega
    | some d =>
      rw [Frame.stateAt_succ he, hD] at hcut hupper
      rw [hD] at hkr
      exact ⟨k, _, d, hki, he, hD, hkr, hcut, hupper⟩

private theorem elect1_on_enter {g : Nat} {d : Machine.ThreadD} {e : Event}
    (hb : rank (some (some d)) < 4) (hl : 4 ≤ rank (Machine.next P L g d e))
    (hu : rank (Machine.next P L g d e) < 27) :
    d = .prologue .elect1 ∧ ∃ mask inst, e.kind = .elect mask inst (laneOf L g) := by
  generalize hn : Machine.next P L g d e = ns at hl hu
  cases d <;> try (simp [rank] at hb)
  rename_i q
  cases q <;> simp only [prologueRank] at hb
  all_goals try omega
  all_goals
    cases hk : e.kind <;> simp only [Machine.next,
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at hn
  case shfl0.shfl mode a b c recv ok | shfl1.shfl mode a b c recv ok =>
    cases recv <;> try dsimp only at hn
    all_goals repeat' first | split_ifs at hn | split at hn
    all_goals cases hn
    all_goals simp_all [rank, prologueRank]
    all_goals subst_vars
    all_goals simp_all
  case elect1.elect mask inst ld =>
    split_ifs at hn with hld
    · cases hn
      exact ⟨rfl, mask, inst, by rw [hld]⟩
    · cases hn
      simp [rank, prologueRank] at hu
  all_goals cases hn
  all_goals simp [rank, prologueRank] at hl hu

private theorem warp_zero_on_enter {g : Nat} {d : Machine.ThreadD} {e : Event}
    (hb : rank (some (some d)) < 2) (hl : 2 ≤ rank (Machine.next P L g d e))
    (hu : rank (Machine.next P L g d e) < 4) : warpOf L g = 0 := by
  generalize hn : Machine.next P L g d e = ns at hl hu
  cases d <;> try (simp [rank] at hb)
  rename_i q
  cases q <;> simp only [prologueRank] at hb
  all_goals try omega
  all_goals
    cases hk : e.kind <;> simp only [Machine.next,
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at hn
  case shfl0.shfl mode a b c recv ok | shfl1.shfl mode a b c recv ok =>
    cases recv <;> try dsimp only at hn
    all_goals repeat' first | split_ifs at hn | split at hn
    all_goals cases hn
    all_goals simp_all [rank, prologueRank]
    all_goals subst_vars
    all_goals simp_all
  all_goals cases hn
  all_goals simp [rank] at hl hu


private theorem elect1_full_mask {g mask inst leader : Nat} {e : Event} {o : Option TState}
    (h : (Machine.machine P L g).Fired (some (.prologue .elect1)) e o)
    (hk : e.kind = .elect mask inst leader) : mask = 4294967295 := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := h
  change (Machine.code P L g).AtD (.prologue .elect1) t at hat
  change Fires t.pc (match kernel.code[31]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [Flow.code_elect_1] at hf
  have ht : Holds t.regs (facts L g .elect1) := hat.2.2.2.2
  have hr : t.regs 525 = some (b32 4294967295) :=
    holds_mem ht (mem_factsFrom (val := valueOf L g)
      (by decide +kernel : 525 ∈ liveAll Site.elect1.pc))
  have hread := readBits_b32 (L := L) (g := g) hr (by decide)
  rcases fires_elect_mask hread hf with ⟨_, _, he⟩ | ⟨_, he⟩
  · rw [he] at hk
    exact (Kind.elect.inj hk).1.symm
  · rw [he] at hk
    cases hk

private theorem init_elected {mem0 : Mem0} {X : Execution} {g i : Nat} {j : Fin 23}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hi : i < (X.tr g).length)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j)))) :
    warpOf L g = 0 ∧ ∃ k pc inst, X.Elect (g, k) pc 4294967295 inst (laneOf L g) := by
  have hlow : 4 ≤ rank (Frame.stateAt (Machine.code P L) X g i) := by
    rw [hst]
    simp [rank, prologueRank]
  obtain ⟨k, e, d, hki, he, hdk, hb, hl, hu⟩ :=
    first_crossing (by decide) (by decide) hi hlow
  have hupper : rank (Machine.next P L g d e) < 27 := by
    rw [hst] at hu
    change rank (Machine.next P L g d e) ≤ 4 + j.val at hu
    have := j.isLt
    omega
  obtain ⟨rfl, mask, inst, hk⟩ := elect1_on_enter hb hl hupper
  have hlo : 2 ≤ rank (Frame.stateAt (Machine.code P L) X g k) := by rw [hdk]; change 2 ≤ 3; decide
  obtain ⟨_, _, _, _, _, _, hb2, hl2, hu2⟩ :=
    first_crossing (by decide) (by decide) (Nat.lt_trans hki hi) hlo
  have hwarp := warp_zero_on_enter hb2 hl2 (lt_of_le_of_lt hu2 (by rw [hdk]; change 3 < 4; decide))
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX hs he hdk
  have hmask := elect1_full_mask hf hk
  refine ⟨hwarp, k, e.pc, inst, ?_⟩
  change X.get (g, k) = some ⟨e.pc, .elect 4294967295 inst (laneOf L g)⟩
  rw [he, ← hmask, ← hk]

/-- The prologue initialization entries of one CTA are reached only by its elected lane. -/
theorem init_threads_eq {mem0 : Mem0} {X : Execution} {g h i k : Nat} {j j' : Fin 23} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : (Machine.machine P L g).Sound) (hh : (Machine.machine P L h).Sound)
    (he : X.get (g, i) = some e) (hf : X.get (h, k) = some f) (hc : ctaOf L g = ctaOf L h)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))))
    (hk : Frame.stateAt (Machine.code P L) X h k = some (some (.prologue (.init j')))) :
    g = h := by
  have hgi : i < (X.tr g).length := List.getElem?_eq_some_iff.mp he |>.choose
  have hhk : k < (X.tr h).length := List.getElem?_eq_some_iff.mp hf |>.choose
  obtain ⟨hwg, x, s, u, helect⟩ := init_elected hX hg hgi hi
  obtain ⟨hwh, y, t, v, helect'⟩ := init_elected hX hh hhk hk
  have hWarp : SameWarp L g h := by
    refine ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX hf, hc⟩, ?_⟩
    simpa [warpOf, tidOf_eq hpre, hpre.block] using hwg.trans hwh.symm
  have heq := hX.elect.2.2 (g, x) (h, y) s t 4294967295 u v
    (laneOf L g) (laneOf L h) helect helect' hWarp
  simp only [laneOf, tidOf_eq hpre] at heq
  simp only [warpOf, tidOf_eq hpre] at hwg hwh
  simp only [ctaOf, hpre.block] at hc
  omega


private theorem on_enter_handoff {g : Nat} {d d' : Machine.ThreadD} {e : Event}
    (hb : rank (some (some d)) < 33) (ha : 33 ≤ rank (some (some d')))
    (hn : Machine.next P L g d e = some (some d')) :
    d = .prologue .barrier := by
  cases d <;> try (simp [rank] at hb)
  rename_i q
  cases q
  case barrier => rfl
  case handoff => simp [prologueRank] at hb
  case init j =>
    have hj := j.isLt
    simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
    split at hn <;> cases hn <;> simp [rank, prologueRank] at ha
    omega
  all_goals
    cases hk : e.kind <;> simp only [Machine.next,
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at hn
  case shfl0.shfl mode a b c recv ok | shfl1.shfl mode a b c recv ok =>
    cases recv <;> try dsimp only at hn
    all_goals repeat' first | split_ifs at hn | split at hn
    all_goals cases hn
    all_goals simp_all [rank, prologueRank]
    all_goals subst_vars
    all_goals simp_all
  case alloc.tc k =>
    cases k
    case resource group dst req =>
      cases req <;> simp at hn
      all_goals try split_ifs at hn
      all_goals cases hn
      all_goals simp [rank, prologueRank] at ha
    all_goals simp at hn
  case allocRead.rd a bs =>
    cases hreb : rebuild 3 bs >>= allocWord L g <;> simp only [hreb] at hn
    all_goals repeat' first | split_ifs at hn | split at hn
    all_goals cases hn
    all_goals simp_all [rank, prologueRank]
    all_goals subst_vars
    all_goals simp_all
  all_goals
    repeat' split at hn
    all_goals cases hn
    all_goals simp [rank, prologueRank] at ha

private theorem gate_event {g : Nat} {e : Event} {o : Option TState}
    (hf : (Machine.machine P L g).Fired (some (.prologue .barrier)) e o) :
    e.kind = .bar 0 none .sync := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[97]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [Flow.code_bar_0] at hf
  exact congrArg Event.kind hf.1

/-- Each role event follows the thread's arrival at the prologue CTA barrier. -/
theorem gate_before_role {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Machine.ThreadD} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some d)) (hrole : ∀ s, d ≠ .prologue s) :
    ∃ k ev, k + 1 < i ∧ X.get (g, k) = some ev ∧ ev.kind = .bar 0 none .sync ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier)) := by
  have hlow : 33 ≤ rank (Frame.stateAt (Machine.code P L) X g i) := by
    rw [hst]
    cases d
    case prologue s => exact ((hrole s) rfl).elim
    all_goals change 33 ≤ 34; decide
  have hi : i < (X.tr g).length := List.getElem?_eq_some_iff.mp he |>.choose
  obtain ⟨k, ev, v, hki, hev, hsv, hb, hl, _⟩ :=
    first_crossing (by decide) (by decide) hi hlow
  obtain ⟨v', hsv'⟩ := Frame.stateAt_live ht (Frame.lt_of_get hX he) hst
    (show k + 1 ≤ i by omega)
  have hn := Frame.stateAt_succ (C := Machine.code P L) hev
  rw [hsv, hsv'] at hn
  change some (some v') = Machine.next P L g v ev at hn
  rw [← hn] at hl
  obtain rfl := on_enter_handoff hb hl hn.symm
  have hlt : k + 1 < i := by
    by_contra hnlt
    have hEq : i = k + 1 := by omega
    rw [hEq, hsv'] at hst
    obtain rfl := Option.some.inj (Option.some.inj hst)
    simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hn
    cases hn
    exact hrole _ rfl
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX hs hev hsv
  exact ⟨k, ev, hlt, hev, gate_event hf, hsv⟩

/-- The prologue gate state occurs at most once in a thread's event trace. -/
theorem gate_state_unique {X : Execution} {g i k : Nat} {e f : Event} (he : X.get (g, i) = some e)
    (hf : X.get (g, k) = some f)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)))
    (hk : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) :
    i = k := by
  have before {a b : Nat} {evt : Event} (hab : a < b) (ha : X.get (g, a) = some evt)
      (hA : Frame.stateAt (Machine.code P L) X g a = some (some (.prologue .barrier)))
      (hB : Frame.stateAt (Machine.code P L) X g b = some (some (.prologue .barrier))) :
      False := by
    have hr := rank_mono (P := P) (L := L) (X := X) (g := g) (Nat.succ_le_of_lt hab)
    change rank (Frame.stateAt (Machine.code P L) X g (a + 1)) ≤
      rank (Frame.stateAt (Machine.code P L) X g b) at hr
    rw [Frame.stateAt_succ ha, hA, hB] at hr
    change rank (Machine.next P L g (.prologue .barrier) evt) ≤ 32 at hr
    simp only [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next] at hr
    split_ifs at hr <;> simp [rank, prologueRank] at hr
  rcases Nat.lt_trichotomy i k with h | h | h
  · exact (before h he hi hk).elim
  · exact h
  · exact (before h hf hk hi).elim

/-- Each initialization of the thread comes before its own prologue gate. -/
theorem init_before_gate {X : Execution} {g i k : Nat} {j : Fin 23}
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))))
    (hk : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) :
    i < k := by
  by_contra h
  have hr := rank_mono (P := P) (L := L) (X := X) (g := g) (Nat.le_of_not_gt h)
  change rank (Frame.stateAt (Machine.code P L) X g k) ≤
    rank (Frame.stateAt (Machine.code P L) X g i) at hr
  rw [hi, hk] at hr
  change 32 ≤ 4 + j.val at hr
  have := j.isLt
  omega

/-- The allocation result is read before the same thread arrives at the prologue gate. -/
theorem alloc_read_before_gate {X : Execution} {g i k : Nat}
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocRead)))
    (hk : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) :
    i < k := by
  by_contra h
  have hr := rank_mono (P := P) (L := L) (X := X) (g := g) (Nat.le_of_not_gt h)
  change rank (Frame.stateAt (Machine.code P L) X g k) ≤
    rank (Frame.stateAt (Machine.code P L) X g i) at hr
  rw [hi, hk] at hr
  exact (by decide : ¬ 32 ≤ 30) hr


private theorem warp_zero_passes_elect1 {g : Nat} {d d' : Machine.ThreadD} {e : Event}
    (hw : warpOf L g = 0) (hb : rank (some (some d)) < 4) (ha : 4 ≤ rank (some (some d')))
    (hn : Machine.next P L g d e = some (some d')) :
    d = .prologue .elect1 ∧ ∃ mask inst leader, e.kind = .elect mask inst leader := by
  cases d <;> try (simp [rank] at hb)
  rename_i q
  cases q <;> simp only [prologueRank] at hb
  all_goals try omega
  all_goals
    cases hk : e.kind <;> simp only [Machine.next,
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hk] at hn
  case shfl0.shfl mode a b c recv ok | shfl1.shfl mode a b c recv ok =>
    cases recv <;> try dsimp only at hn
    all_goals repeat' first | split_ifs at hn | split at hn
    all_goals cases hn
    all_goals simp_all [rank, prologueRank]
    all_goals subst_vars
    all_goals simp_all
  case elect1.elect mask inst leader =>
    exact ⟨rfl, mask, inst, leader, rfl⟩
  all_goals cases hn
  all_goals simp [rank, prologueRank] at ha

/-- Each warp-zero arrival at the prologue gate follows its lane's initialization election. -/
theorem gate_election_followed {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, k) = some e) (hw : warpOf L g = 0)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) :
    ∃ x f inst leader, x < k ∧ X.get (g, x) = some f ∧
      f.kind = .elect 4294967295 inst leader ∧
      Frame.stateAt (Machine.code P L) X g x = some (some (.prologue .elect1)) := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).choose
  have hlow : 4 ≤ rank (Frame.stateAt (Machine.code P L) X g k) := by
    rw [hst]
    change 4 ≤ 32
    decide
  obtain ⟨x, f, v, hxk, hf, hsv, hb, hl, _⟩ :=
    first_crossing (by decide) (by decide) hk hlow
  obtain ⟨v', hsv'⟩ := FollowedPrefix.state_at hst
    (show x + 1 ≤ k by omega)
  have hn := Frame.stateAt_succ (C := Machine.code P L) hf
  rw [hsv, hsv'] at hn
  change some (some v') = Machine.next P L g v f at hn
  rw [← hn] at hl
  obtain ⟨rfl, mask, inst, leader, hElect⟩ := warp_zero_passes_elect1 hw hb hl hn.symm
  obtain ⟨_, hFired⟩ := RingEvents.fired_of_trace hX hs hf hsv
  rw [elect1_full_mask hFired hElect] at hElect
  exact ⟨x, f, inst, leader, hxk, hf, hElect, hsv⟩

/-- The tracked launch form of the prologue gate's preceding election. -/
theorem gate_election {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, k) = some e) (hw : warpOf L g = 0)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) :
    ∃ x f inst leader, x < k ∧ X.get (g, x) = some f ∧
      f.kind = .elect 4294967295 inst leader ∧
      Frame.stateAt (Machine.code P L) X g x = some (some (.prologue .elect1)) :=
  gate_election_followed hX hs he hw hst

/-- The elected thread's prologue gate certifies that it executed every table initialization. -/
theorem gate_initializes {mem0 : Mem0} {X : Execution} {g x k inst : Nat} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, x) = some e) (hf : X.get (g, k) = some f)
    (hElect : e.kind = .elect 4294967295 inst (laneOf L g))
    (hElectState : Frame.stateAt (Machine.code P L) X g x = some (some (.prologue .elect1)))
    (hGate : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .barrier))) (j : Fin 23)
    :
    ∃ i u, i < k ∧ X.get (g, i) = some u ∧
      u.kind = .mbInit ⟨.shared, ctaOf L g, L.sharedBase + initOff j⟩ (initCount j) ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue (.init j))) := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).choose
  have hr : ∀ n (hn : n < 23),
      Frame.stateAt (Machine.code P L) X g (x + 1 + n) =
        some (some (.prologue (.init ⟨n, hn⟩))) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [Nat.add_zero, Frame.stateAt_succ he, hElectState]
      change Machine.next P L g (.prologue .elect1) e = _
      simp [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hElect]
      rfl
    | succ n ih =>
      intro hn
      have hSt := ih (by omega : n < 23)
      have hlt := init_before_gate hSt hGate
      have hlen : x + 1 + n < (X.tr g).length := Nat.lt_trans hlt hk
      have hget : X.get (g, x + 1 + n) = some (X.tr g)[x + 1 + n] :=
        List.getElem?_eq_getElem hlen
      rw [← Nat.add_assoc, Frame.stateAt_succ hget, hSt]
      change Machine.next P L g (.prologue (.init ⟨n, by omega⟩)) (X.tr g)[x + 1 + n] = _
      simp [Machine.next, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, hn]
      rfl
  obtain ⟨n, hn⟩ := j
  have hSt := hr n hn
  have hlt := init_before_gate hSt hGate
  have hlen : x + 1 + n < (X.tr g).length := Nat.lt_trans hlt hk
  have hget : X.get (g, x + 1 + n) = some (X.tr g)[x + 1 + n] :=
    List.getElem?_eq_getElem hlen
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX hs hget hSt
  exact ⟨_, _, hlt, hget, RingEvents.barrier_init hpre hFire, hSt⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingInitSources
