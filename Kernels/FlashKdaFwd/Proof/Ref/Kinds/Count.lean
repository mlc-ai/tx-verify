-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Event
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Flow.BulkCount
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.Polls
public import Lemmas.Kernel.CountClosed

@[expose] public section

/-! # Counts of a class of events do not change where no site can fire the class

Part of `Ref/Kinds.lean` (read its header first). A *class* of events is a Boolean predicate
`c : Event → Bool`; a contract counts it along a thread's trace as
`((X.tr g).take k).countP c` (the events of class `c` among the thread's first `k`).

* `FiredOnly c K`: events of class `c` are fired only at sites whose kind is in the list `K`.
  Proved for the classes the contracts count (`firedOnly_isBar`, `firedOnly_isBarId`,
  `firedOnly_okPoll`, `firedOnly_arrivesOn`, `firedOnly_issuesTo`, `firedOnly_isMatrix`,
  `firedOnly_isShfl`, `firedOnly_isTensorStore`, `firedOnly_isCommit`, `firedOnly_isExit`); for
  a class of your own, defined by a `match e.kind with`, the tactic `fired_only` proves it.
* `count_transport`: **the count of class `c` is the same at positions `j ≤ k` if, at every
  position `i` in between, the state before the thread's event `i` is followed and either the
  kind of its site is not in `K` or the event fired there is not of class `c`.** The second
  alternative is what a phase proves from its closed-form event shapes (the poll at this site
  is on another mbarrier; the tensor copy at this site completes on another mbarrier).
  `count_transport_of_state` is the same when a later state is known to be followed, which
  makes every earlier one followed (`followed_of_le`; no tracking hypothesis);
  `count_zero_of_state` is the case `j = 0`.
* The specializations, one per class: `count_isBar`, `count_isBarId`, `count_bar0Before`
  (the protocol layer's `bar0Before`), `count_okPoll`,
  `count_arrivesOn`, `count_issuesTo`, `count_isMatrix`, `count_isShfl`,
  `count_isTensorStore`, `count_isCommit`, `count_isExit`.
* For the second alternative: `okPoll_other`, `arrivesOn_other`, `issuesTo_other` (an event on
  mbarrier `m₁` is not of the class of another mbarrier `m₂`), `isTensorStore_load`,
  `issuesTo_store` (a tensor copy on the load side fires no tensor store, one on the store
  side no load issue, whatever the phase knows).
* `first_exit`: from a phase invariant in the form `phase_inv` gives it ("the invariant holds,
  or the exit condition held at an earlier position"), the first position at which the exit
  condition holds, with the invariant at every position before it. This is how "the state
  at every position in between is at a site of the phase" is obtained. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

/-! ### Followed states, without tracking -/

section Frame
variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g k n : Nat}

/-- A machine that gave up has given up at every later position. -/
theorem stateAt_giveUp_mono (h : Frame.stateAt C X g k = some none) (hkn : k ≤ n) :
    Frame.stateAt C X g n = some none := by
  induction n with
  | zero => rwa [show k = 0 by omega] at h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkn with heq | hlt
    · rwa [← heq]
    have ih' := ih (by omega)
    by_cases hn : n < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[n]? = some e := ⟨_, List.getElem?_eq_getElem hn⟩
      rw [Frame.stateAt_succ he, ih']
      rfl
    · rw [Frame.stateAt_of_le (by omega)]
      rwa [Frame.stateAt_of_le (by omega)] at ih'

/-- **Before a followed state the machine is at a state**: a machine that stopped or gave up
stays so. No tracking hypothesis. -/
theorem followed_of_le {d : (C g).D} (hσ : Frame.stateAt C X g n = some (some d))
    (hk : k ≤ n) : ∃ d', Frame.stateAt C X g k = some (some d') := by
  cases h : Frame.stateAt C X g k with
  | none => rw [Frame.stateAt_none_mono h hk] at hσ; cases hσ
  | some σ =>
    cases σ with
    | none => rw [stateAt_giveUp_mono h hk] at hσ; cases hσ
    | some d' => exact ⟨d', rfl⟩

open Classical in
/-- **The first exit of a phase.** A phase invariant in the form of `phase_inv` (`I` holds, or
the exit condition `E` held at an earlier position) gives, at a followed state: `I` holds, or
`E` holds at a first position `j`, before which `I` holds at every followed state. -/
theorem first_exit {I E : Nat → (C g).D → Prop}
    (hinv : ∀ k s, k < (X.tr g).length → Frame.stateAt C X g k = some (some s) →
      I k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt C X g j = some (some s0) ∧ E j s0)
    {s : (C g).D} (hk : k < (X.tr g).length) (hσ : Frame.stateAt C X g k = some (some s)) :
    I k s ∨ ∃ j ≤ k, ∃ s0, Frame.stateAt C X g j = some (some s0) ∧ E j s0 ∧
      ∀ i < j, ∀ si, Frame.stateAt C X g i = some (some si) → I i si := by
  rcases hinv k s hk hσ with h | hex
  · exact .inl h
  · have hex' : ∃ j, j ≤ k ∧ ∃ s0, Frame.stateAt C X g j = some (some s0) ∧ E j s0 := hex
    refine .inr ⟨Nat.find hex', (Nat.find_spec hex').1, ?_⟩
    obtain ⟨s0, h1, h2⟩ := (Nat.find_spec hex').2
    refine ⟨s0, h1, h2, fun i hi si hsi => ?_⟩
    have hjk := (Nat.find_spec hex').1
    rcases hinv i si (by omega) hsi with h | ⟨j', hj', s', h1', h2'⟩
    · exact h
    · exact absurd ⟨by omega, s', h1', h2'⟩ (Nat.find_min hex' (show j' < Nat.find hex' by omega))

end Frame

/-! ### Counts along a trace -/

/-- The count of a class over two prefixes of a list is the same if no element in between is
of the class. -/
theorem countP_take_eq (c : Event → Bool) {l : List Event} {j k : Nat} (hjk : j ≤ k)
    (h : ∀ i e, j ≤ i → i < k → l[i]? = some e → c e = false) :
    (l.take k).countP c = (l.take j).countP c := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih fun i e h1 h2 he => h i e h1 (by omega) he]
    cases he : l[k]? with
    | none =>
      have hl : l.length ≤ k := List.getElem?_eq_none_iff.mp he
      rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
    | some e =>
      rw [Frame.countP_take_succ_ite c he, h k e hk (by omega) he]
      simp

/-- **Events of class `c` are fired only at sites whose kind is in `K`**: a kind of site that
can fire an event of the class is in the list. -/
def FiredOnly (c : Event → Bool) (K : List SiteKind) : Prop :=
  ∀ e κ, c e = true → firedAt e.kind κ = true → κ ∈ K

/-- `fired_only`: prove `FiredOnly c K` for a class `c` that is defined by a `match e.kind with`
(pass the names to unfold: `fired_only [isInit]`). It tries every kind of event and, for those
in the class, every kind of site. -/
syntax "fired_only" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fired_only) => `(tactic| fired_only [])
  | `(tactic| fired_only [$ls,*]) => `(tactic| (
      rintro ⟨pc, k⟩ κ hc hf
      cases k <;> first
        | (exfalso; revert hc; simp [$ls,*]; done)
        | (cases κ <;> first
            | (exfalso; revert hf; simp [PTX.Kernels.FlashKdaFwd.Proof.Ref.firedAt]; done)
            | decide)))

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

section
variable (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X)
include hC hX

/-- At a site whose kind cannot fire the class, the event is not of the class. -/
theorem not_class_of_kind {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    {k : Nat} {e : Event} {d : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hκ : d.site.kind ∉ K) :
    c e = false := by
  cases hc : c e
  · rfl
  · exact absurd (hK e _ hc (site_fires hC hX he hσ)) hκ

/-- **Count transport.** The number of events of class `c` among the thread's first `k` events
is the number among its first `j ≤ k` if, at every position `i` in between, the state before
the event is followed and either the kind of its site is not in `K` (the kinds of sites that
fire the class) or the event fired there is not of class `c`. -/
theorem count_transport {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    {j k : Nat} (hjk : j ≤ k)
    (h : ∀ i, j ≤ i → i < k → i < (X.tr g).length →
      ∃ d, Frame.stateAt (code L) X g i = some (some d) ∧
        (d.site.kind ∉ K ∨ ∀ e, X.get (g, i) = some e → c e = false)) :
    ((X.tr g).take k).countP c = ((X.tr g).take j).countP c := by
  refine countP_take_eq c hjk fun i e hji hik he => ?_
  obtain ⟨d, hσ, hd⟩ := h i hji hik (List.getElem?_eq_some_iff.mp he).1
  rcases hd with hκ | hc
  · exact not_class_of_kind hC hX hK he hσ hκ
  · exact hc e he

/-- **Count transport below a followed state.** As `count_transport`, when the state before
some event `n` with `k ≤ n + 1` is followed: every state before it is then followed, and the
condition is asked of the states. Typical uses: `n = k` (the state at the end of the stretch is
known), and `n + 1 = k` (the stretch ends with the thread's last event). -/
theorem count_transport_of_state {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    {j k n : Nat} {dn : D} (hjk : j ≤ k) (hn : Frame.stateAt (code L) X g n = some (some dn))
    (hkn : k ≤ n + 1)
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ K ∨ ∀ e, X.get (g, i) = some e → c e = false) :
    ((X.tr g).take k).countP c = ((X.tr g).take j).countP c := by
  refine count_transport hC hX hK hjk fun i hji hik _ => ?_
  obtain ⟨d, hσ⟩ := followed_of_le hn (show i ≤ n by omega)
  exact ⟨d, hσ, h i d hji hik hσ⟩

/-- **No event of the class before a followed state**: `count_transport_of_state` from the
start of the trace. -/
theorem count_zero_of_state {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    {k n : Nat} {dn : D} (hn : Frame.stateAt (code L) X g n = some (some dn)) (hkn : k ≤ n + 1)
    (h : ∀ i d, i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ K ∨ ∀ e, X.get (g, i) = some e → c e = false) :
    ((X.tr g).take k).countP c = 0 := by
  rw [count_transport_of_state hC hX hK (Nat.zero_le k) hn hkn fun i d _ => h i d]
  rfl

end

/-! ### The classes the contracts count -/

/-- Whether an event is a thread's exit. -/
def isExit (e : Event) : Bool := match e.kind with
  | .exit => true
  | _ => false

/-- The kinds of sites that fire a matrix event: the second event of an `ldmatrix`, an `mma`, a
`movmatrix`, the first event of a `stmatrix`. -/
def matrixKinds : List SiteKind := [.matrixLoadMx, .warpMma, .matrixMove, .matrixStore]

/-- The kinds of sites that fire a memory read. -/
def readKinds : List SiteKind := [.load, .loadEl1, .loadEl2, .loadEl3, .matrixLoad]

/-- The kinds of sites that fire a memory write. -/
def writeKinds : List SiteKind := [.store, .matrixStoreWr]

theorem firedOnly_isBar : FiredOnly Execution.isBar [.bar] := by
  fired_only [Execution.isBar]

theorem firedOnly_isBarId (id : Nat) : FiredOnly (Execution.isBarId id) [.bar] := by
  fired_only [Execution.isBarId]

theorem firedOnly_okPoll (m : Loc) : FiredOnly (okPoll m) [.mbarWait] := by
  fired_only [okPoll, sourceWaitSuccess]

theorem firedOnly_arrivesOn (m : Loc) : FiredOnly (arrivesOn m) [.mbarArrive] := by
  fired_only [arrivesOn, sourceArrive]

theorem firedOnly_issuesTo (m : Loc) : FiredOnly (issuesTo m) [.tensorCopy] := by
  fired_only [issuesTo]

theorem firedOnly_isMatrix : FiredOnly isMatrix matrixKinds := by
  fired_only [isMatrix]

theorem firedOnly_isShfl : FiredOnly Execution.isShfl [.shfl] := by
  fired_only [Execution.isShfl]

theorem firedOnly_isTensorStore : FiredOnly isTensorStore [.tensorCopy] := by
  fired_only [isTensorStore]

theorem firedOnly_isCommit : FiredOnly isCommit [.bulkCommit] := by
  fired_only [isCommit]

theorem firedOnly_isExit : FiredOnly isExit [.exit] := by
  fired_only [isExit]

section
variable (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X) {j k n : Nat} {dn : D} (hjk : j ≤ k)
  (hn : Frame.stateAt (code L) X g n = some (some dn)) (hkn : k ≤ n + 1)
include hC hX hjk hn hkn

/-- The barrier arrivals of a thread do not change where it is at no `bar` site. -/
theorem count_isBar
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.bar] ∨ ∀ e, X.get (g, i) = some e → Execution.isBar e = false) :
    ((X.tr g).take k).countP Execution.isBar = ((X.tr g).take j).countP Execution.isBar :=
  count_transport_of_state hC hX firedOnly_isBar hjk hn hkn h

/-- The arrivals of a thread at barrier `id` do not change where it is at no `bar` site, or at
`bar` sites of another barrier. -/
theorem count_isBarId (id : Nat)
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.bar] ∨
        ∀ e, X.get (g, i) = some e → Execution.isBarId id e = false) :
    ((X.tr g).take k).countP (Execution.isBarId id) =
      ((X.tr g).take j).countP (Execution.isBarId id) :=
  count_transport_of_state hC hX (firedOnly_isBarId id) hjk hn hkn h

/-- The same for the protocol layer's count of `bar.sync 0` (`Protocol.bar0Before`). At a
`bar.sync 0` site the class is decided by `isBarId_bar0`. -/
theorem count_bar0Before
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.bar] ∨
        ∀ e, X.get (g, i) = some e → Execution.isBarId 0 e = false) :
    Protocol.bar0Before X (g, k) = Protocol.bar0Before X (g, j) :=
  count_transport_of_state hC hX (firedOnly_isBarId 0) hjk hn hkn h

/-- The successful polls of mbarrier `m` do not change where the thread is at no `mbarWait`
site, or at polls of another mbarrier. -/
theorem count_okPoll (m : Loc)
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.mbarWait] ∨ ∀ e, X.get (g, i) = some e → okPoll m e = false) :
    okPolls m ((X.tr g).take k) = okPolls m ((X.tr g).take j) :=
  count_transport_of_state hC hX (firedOnly_okPoll m) hjk hn hkn h

/-- The arrivals on mbarrier `m` do not change where the thread is at no `mbarArrive` site, or
at arrivals on another mbarrier. -/
theorem count_arrivesOn (m : Loc)
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.mbarArrive] ∨
        ∀ e, X.get (g, i) = some e → arrivesOn m e = false) :
    arrivals m ((X.tr g).take k) = arrivals m ((X.tr g).take j) :=
  count_transport_of_state hC hX (firedOnly_arrivesOn m) hjk hn hkn h

/-- The tensor loads that complete on mbarrier `m` do not change where the thread is at no
`tensorCopy` site, or at copies that complete elsewhere. -/
theorem count_issuesTo (m : Loc)
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.tensorCopy] ∨
        ∀ e, X.get (g, i) = some e → issuesTo m e = false) :
    ((X.tr g).take k).countP (issuesTo m) = ((X.tr g).take j).countP (issuesTo m) :=
  count_transport_of_state hC hX (firedOnly_issuesTo m) hjk hn hkn h

/-- The matrix events of a thread do not change where it is at no matrix site. -/
theorem count_isMatrix
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ matrixKinds ∨ ∀ e, X.get (g, i) = some e → isMatrix e = false) :
    ((X.tr g).take k).countP isMatrix = ((X.tr g).take j).countP isMatrix :=
  count_transport_of_state hC hX firedOnly_isMatrix hjk hn hkn h

/-- The shuffles of a thread do not change where it is at no `shfl` site. -/
theorem count_isShfl
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.shfl] ∨ ∀ e, X.get (g, i) = some e → Execution.isShfl e = false) :
    ((X.tr g).take k).countP Execution.isShfl = ((X.tr g).take j).countP Execution.isShfl :=
  count_transport_of_state hC hX firedOnly_isShfl hjk hn hkn h

/-- The tensor stores of a thread do not change where it is at no `tensorCopy` site, or at
tensor loads. -/
theorem count_isTensorStore
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.tensorCopy] ∨
        ∀ e, X.get (g, i) = some e → isTensorStore e = false) :
    ((X.tr g).take k).countP isTensorStore = ((X.tr g).take j).countP isTensorStore :=
  count_transport_of_state hC hX firedOnly_isTensorStore hjk hn hkn h

/-- The bulk-group commits of a thread do not change where it is at no `bulkCommit` site. -/
theorem count_isCommit
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.bulkCommit] ∨ ∀ e, X.get (g, i) = some e → isCommit e = false) :
    ((X.tr g).take k).countP isCommit = ((X.tr g).take j).countP isCommit :=
  count_transport_of_state hC hX firedOnly_isCommit hjk hn hkn h

/-- A thread does not exit where it is not at the `exit` site. -/
theorem count_isExit
    (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
      d.site.kind ∉ [SiteKind.exit] ∨ ∀ e, X.get (g, i) = some e → isExit e = false) :
    ((X.tr g).take k).countP isExit = ((X.tr g).take j).countP isExit :=
  count_transport_of_state hC hX firedOnly_isExit hjk hn hkn h

end

/-! ### Finer than the kind: the object an event names -/

/-- A poll of mbarrier `m₁` is no successful poll of another mbarrier. -/
theorem okPoll_other {e : Event} {m₁ m₂ : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m₁ p ok acq sc) (hne : m₁ ≠ m₂) : okPoll m₂ e = false := by
  obtain ⟨pc, kd⟩ := e
  obtain rfl : kd = .wait m₁ p ok acq sc := hk
  rw [okPoll_wait rfl]
  simp [hne]

/-- An arrival on mbarrier `m₁` is no arrival on another mbarrier. -/
theorem arrivesOn_other {e : Event} {m₁ m₂ : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive m₁ tx c rel sc) (hne : m₁ ≠ m₂) : arrivesOn m₂ e = false := by
  obtain ⟨pc, kd⟩ := e
  obtain rfl : kd = .arrive m₁ tx c rel sc := hk
  rw [arrivesOn_arrive rfl]
  simp [hne]

/-- A tensor load that completes on mbarrier `m₁` is no tensor load of another mbarrier. -/
theorem issuesTo_other {e : Event} {m : Loc} {a : Nat} {sp : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a sp) (hne : sp.mbar ≠ m) : issuesTo m e = false := by
  obtain ⟨pc, kd⟩ := e
  obtain rfl : kd = .tensorIssue a sp := hk
  rw [issuesTo_tensorIssue]
  simp [hne]

section
variable (hC : ∀ g < L.threads, (code L g).Sound)
  (hX : Consistent L kernel Assumptions.all mem0 X) {k : Nat} {e : Event} {d : D}
  (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
include hC hX he hσ

/-- A tensor copy on the load side (before `firstStoreCopy`) fires no tensor store. -/
theorem isTensorStore_load {j : Fin 258} (hs : d.site = .tensorCopy j)
    (hj : j.val < firstStoreCopy) : isTensorStore e = false := by
  have h := tensorCopy_load_event hC hX he hσ hs hj
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first | rfl | exact absurd rfl (h _ _)

/-- A tensor copy on the store side (from `firstStoreCopy` on) fires no tensor load issue. -/
theorem issuesTo_store {j : Fin 258} (hs : d.site = .tensorCopy j)
    (hj : firstStoreCopy ≤ j.val) (m : Loc) : issuesTo m e = false :=
  issuesTo_notTensor (tensorCopy_store_event hC hX he hσ hs hj)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
