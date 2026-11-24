-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory
public import Lemmas.Execution.NoBarArrive
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-! # Named-barrier ledgers over checked CTA histories

A named CTA barrier resource is completed by `n` participant warps. Each participant
passes one thread-count operand `count` which the object decodes to `n` warps
(`target block count = .ok n`), so the slot records `n` as its expected count: `some (32 * n)`
for a group of `n` warps (`target_some_mul`), `none` for all warps of the CTA. The participant
warps are full warps of a CTA of `block` threads, `w < block / 32`.

`Ledger block n p id counts s` relates the state of resource `id` in the object state
`s` to the participant set `p`: the arrived set and generation of the slot, and the
per-warp arrival counts `counts` of every participant warp that is still live. A
generation completes when every live participant warp has arrived (by its count, or by
`CtaBarrier.exitThread` releasing a generation that waits only for exited warps), so a
live participant warp has arrived exactly once in each completed generation; an exited
participant warp makes no further arrival. `Protocol count p id h` is a property of a checked
history `h`: every arrival on `id` is by a participant warp with operand `count`; it permits
arbitrary other resources and any exit. Replaying a protocol-respecting history establishes
the ledger for its actual state. Each real arrival then has a resource key fixed by its
source ordinal, and the source-side lemmas below record those keys. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

/-- The state of named resource `id` relative to the participant warps `p`, in a CTA of
`block` threads where `n` warps complete each generation. `counts w` is the number of
actual arrivals of warp `w` at this resource; it is fixed for live warps. -/
structure Ledger (block n : Nat) (participants : Finset Nat) (id : Nat) (counts : Nat → Nat)
    (s : CtaBarrier.State) : Prop where
  owners : (s.slots id).arrived ⊆ participants
  card_lt : (s.slots id).arrived.card < n
  expected : (s.slots id).expected =
    if (s.slots id).arrived = ∅ then none else some n
  balance : ∀ w ∈ participants, warpLive block s.exited w →
    counts w = (s.slots id).generation + if w ∈ (s.slots id).arrived then 1 else 0

theorem Ledger.initial {block n : Nat} (p : Finset Nat) (hn : 0 < n) (id : Nat) :
    Ledger block n p id (fun _ => 0) {} :=
  ⟨by simp, by simpa using hn, by simp, fun w _ _ => by simp⟩

/-- A live warp of the exited set of a later state was live before. -/
theorem warpLive_mono {block w : Nat} {e e' : Finset Nat} (hsub : e ⊆ e')
    (h : warpLive block e' w) : warpLive block e w := by
  obtain ⟨lane, hl, hlt, hn⟩ := h
  exact ⟨lane, hl, hlt, fun hm => hn (hsub hm)⟩

/-- A completion of a slot whose arrivals are participants, with `n` requested warps,
has every live participant warp arrived. -/
private theorem complete_live {block n : Nat} {p : Finset Nat} {exited : Finset Nat}
    {slot : CtaBarrier.Slot} (hcard : p.card = n) (hbound : ∀ w ∈ p, w < block / 32)
    (hsub : slot.arrived ⊆ p) (hexp : slot.expected = some n)
    (hd : complete block exited slot = true) :
    ∀ w ∈ p, warpLive block exited w → w ∈ slot.arrived := by
  intro w hw hl
  simp only [complete, hexp, decide_eq_true_eq] at hd
  rcases hd with hc | ⟨-, hall⟩
  · have heq : slot.arrived = p :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact heq ▸ hw
  · have hb := hbound w hw
    exact hall w (by simp only [Finset.mem_range, warps]; omega) hl

private theorem arrive_not_mem {block : Nat} {s t : CtaBarrier.State} {id warp : Nat}
    {count : Option Nat} (h : arrive block s id warp count = .ok t) :
    warp ∉ (s.slots id).arrived := by
  by_contra ha
  cases ht : target block count <;>
    simp only [arrive, ht, ha, bind, Except.bind, pure, Except.pure, throw] at h
  all_goals split_ifs at h

/-- A nonzero explicit count decodes to its warp count when it is a multiple of `32`. -/
theorem target_some_ne_zero {block k : Nat} (hk : k ≠ 0) :
    target block (some k) =
      if k < 2 ^ 32 ∧ k % 32 = 0 then .ok (k / 32) else .error .badCount := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k => rfl

/-- The count `32 * n` of `n > 0` warps, below `2 ^ 32`, decodes to exactly `n` warps. -/
theorem target_some_mul {block n : Nat} (hn : 0 < n) (hn32 : 32 * n < 2 ^ 32) :
    target block (some (32 * n)) = .ok n := by
  rw [target_some_ne_zero (by omega), ite_eq_left ⟨hn32, by omega⟩]
  congr 1
  omega

/-- One actual arrival of a participant preserves the ledger. An arrival completing the
generation advances it and clears all arrival marks. -/
theorem Ledger.arrival {block n : Nat} {p : Finset Nat} {id warp : Nat} {counts : Nat → Nat}
    {count : Option Nat} {s t : CtaBarrier.State} (h : Ledger block n p id counts s) (hn : 0 < n)
    (hcount : target block count = .ok n)
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < block / 32) (hw : warp ∈ p)
    (ha : arrive block s id warp count = .ok t) :
    Ledger block n p id (increment counts warp) t := by
  have hmiss := arrive_not_mem ha
  have hwl := (arrive_live ha).2
  obtain ⟨m, hm, hexit, hslots⟩ := arrive_shape ha
  have hmn : m = n := Except.ok.inj (hm.symm.trans hcount)
  subst m
  have hslot : t.slots id = settle block s.exited
      {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} := by
    simpa only [↓reduceIte] using hslots id
  have hsub : insert warp (s.slots id).arrived ⊆ p := Finset.insert_subset hw h.owners
  have hc : (insert warp (s.slots id).arrived).card = (s.slots id).arrived.card + 1 :=
    Finset.card_insert_of_notMem hmiss
  have hle : (insert warp (s.slots id).arrived).card ≤ n := by
    simpa only [hcard] using Finset.card_le_card hsub
  have hbw := h.balance warp hw hwl
  simp only [hmiss, ↓reduceIte, Nat.add_zero] at hbw
  by_cases hd : complete block s.exited
      {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} = true
  · have hin := complete_live hcard hbound hsub rfl hd
    rw [settle_complete hd] at hslot
    refine ⟨by rw [hslot]; simp, by rw [hslot]; simpa using hn, by rw [hslot]; simp, ?_⟩
    intro w hwp hwl'
    rw [hexit] at hwl'
    have hm := hin w hwp hwl'
    by_cases hew : w = warp
    · subst w
      simp [increment, hslot, hbw]
    · have hm' : w ∈ (s.slots id).arrived := (Finset.mem_insert.mp hm).resolve_left hew
      have hb := h.balance w hwp hwl'
      simp only [hm', ↓reduceIte] at hb
      simp [increment, hew, hslot, hb]
  · have hd' : complete block s.exited
        {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} =
          false := by simpa using hd
    have hlt : (insert warp (s.slots id).arrived).card < n := by
      by_contra hge
      exact hd (complete_of_count rfl (show n ≤ (insert warp (s.slots id).arrived).card by omega))
    rw [settle_pending hd'] at hslot
    refine ⟨by simpa only [hslot] using hsub, by simpa only [hslot] using hlt,
      by rw [hslot]; simp, ?_⟩
    intro w hwp hwl'
    rw [hexit] at hwl'
    have hb := h.balance w hwp hwl'
    by_cases hew : w = warp
    · subst w
      simp [increment, hslot, hbw]
    · simpa [increment, hew, hslot, Finset.mem_insert] using hb

theorem Ledger.other_arrival {block n : Nat} {p : Finset Nat} {id other warp : Nat}
    {count : Option Nat} {counts : Nat → Nat} {s t : CtaBarrier.State}
    (h : Ledger block n p id counts s) (hne : id ≠ other)
    (ha : arrive block s other warp count = .ok t) : Ledger block n p id counts t := by
  obtain ⟨_, _, hexit, hslots⟩ := arrive_shape ha
  have hs : t.slots id = s.slots id := by simpa only [ite_eq_right hne] using hslots id
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hs] using h.owners
  · simpa only [hs] using h.card_lt
  · simpa only [hs] using h.expected
  · intro w hw hl
    rw [hexit] at hl
    simpa only [hs] using h.balance w hw hl

/-- An exit preserves the ledger. It may complete the generation, but only when every live
participant warp has arrived, so the live warps' counts stay balanced; the exited thread's
warp may stop being live, after which its count is no longer tracked. -/
theorem Ledger.exit {block n : Nat} {p : Finset Nat} {id g : Nat} {counts : Nat → Nat}
    {s t : CtaBarrier.State} (h : Ledger block n p id counts s) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < block / 32) (he : exitThread block s g = .ok t) :
    Ledger block n p id counts t := by
  unfold exitThread at he
  split_ifs at he with hg
  · simp only [pure, Except.pure, Except.ok.injEq] at he
    subst he
    have hmono : s.exited ⊆ insert g s.exited := Finset.subset_insert _ _
    by_cases hd : complete block (insert g s.exited) (s.slots id) = true
    · have hexp : (s.slots id).expected = some n := by
        rw [h.expected]
        split_ifs with h0
        · simp [complete, h.expected, h0] at hd
        · rfl
      have hin := complete_live hcard hbound h.owners hexp hd
      refine ⟨by simp [settle_complete hd], by have := h.card_lt; simp [settle_complete hd]; omega,
        by simp [settle_complete hd], ?_⟩
      intro w hw hl
      have hb := h.balance w hw (warpLive_mono hmono hl)
      simp only [hin w hw hl, ↓reduceIte] at hb
      simp [settle_complete hd, hb]
    · have hd' : complete block (insert g s.exited) (s.slots id) = false := by simpa using hd
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [settle_pending hd'] using h.owners
      · simpa only [settle_pending hd'] using h.card_lt
      · simpa only [settle_pending hd'] using h.expected
      · intro w hw hl
        simpa only [settle_pending hd'] using h.balance w hw (warpLive_mono hmono hl)
  · simp [bind, Except.bind, throw] at he

/-- A selected participant's pre-arrival count is the real resource generation,
not a separately supplied source-phase assignment. -/
theorem Ledger.arrival_generation {block n : Nat} {p : Finset Nat} {id warp : Nat}
    {counts : Nat → Nat} {count : Option Nat} {s t : CtaBarrier.State}
    (h : Ledger block n p id counts s)
    (hw : warp ∈ p) (ha : arrive block s id warp count = .ok t) :
    counts warp = (s.slots id).generation := by
  have hm := arrive_not_mem ha
  simpa only [hm, ↓reduceIte, Nat.add_zero] using h.balance warp hw (arrive_live ha).2

/-- A CTA-local thread below the block size lies below the launch's thread count. -/
theorem cta_thread_lt {L : Launch} {c g : Nat} (hc : c < L.grid) (hg : g < L.block) :
    c * L.block + g < L.threads := by
  unfold Launch.threads
  calc
    c * L.block + g < c * L.block + L.block := by omega
    _ = (c + 1) * L.block := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ L.grid * L.block := Nat.mul_le_mul_right _ (by omega)

/-- Any thread of the launch lies in a CTA of positive block size. -/
theorem block_pos_of_thread_lt {L : Launch} {g : Nat} (hg : g < L.threads) :
    0 < L.block := by
  unfold Launch.threads at hg
  rcases Nat.eq_zero_or_pos L.block with h0 | h0
  · rw [h0, Nat.mul_zero] at hg
    omega
  · exact h0

variable {α : Type}

/-- A property of a checked history: every arrival on `id` is by a participant warp with
thread-count operand `count`. It allows all unrelated resources and all exits, and fixes no
resource generation. -/
def Protocol (count : Option Nat) (p : Finset Nat) (id : Nat) (h : List (Record α)) : Prop :=
  ∀ r ∈ h, match r with
    | .arrival other warp cnt _ => other = id → warp ∈ p ∧ cnt = count
    | .exit _ _ => True

theorem Protocol.prefix {count : Option Nat} {p : Finset Nat} {id : Nat}
    {xs ys : List (Record α)}
    (h : Protocol count p id (xs ++ ys)) : Protocol count p id xs := by
  intro r hr
  exact h r (List.mem_append_left _ hr)

/-- Replaying the actual resource records establishes the absolute generation
ledger. There is no canonical arrival order or caller-supplied phase. -/
theorem Protocol.run_ledger {block n : Nat} {count : Option Nat} {p : Finset Nat} {id : Nat}
    {h : List (Record α)} {s : CtaBarrier.State} (hp : Protocol count p id h) (hn : 0 < n)
    (hcount : target block count = .ok n) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < block / 32) (hr : run block {} h = .ok s) :
    Ledger block n p id (idArrivals h id) s := by
  induction h using List.reverseRecOn generalizing s with
  | nil =>
    cases hr
    exact Ledger.initial p hn id
  | @append_singleton xs r ih =>
    obtain ⟨u, hu⟩ := run_prefix hr
    have hs := ih hp.prefix hu
    have hf : r.perform block u = .ok s := by
      rw [run_append, hu] at hr
      cases hf : r.perform block u with
      | error err => simp [run, hf, Except.bind] at hr
      | ok v => simpa only [run, hf, Except.bind, Except.ok.injEq, throw, throwThe,
          MonadExceptOf.throw] using hr
    have hsource := hp r (List.mem_append_right _ (List.mem_singleton_self r))
    cases r with
    | arrival other warp cnt lanes =>
      simp only [Record.perform] at hf
      split_ifs at hf with hlanes
      by_cases hother : other = id
      · obtain ⟨hw, hcnt⟩ := hsource hother
        subst other
        subst cnt
        have heq : idArrivals (xs ++ [Record.arrival id warp count lanes]) id =
            increment (idArrivals xs id) warp := by
          funext w
          by_cases hw' : w = warp
          · subst w
            simp [idArrivals, isWarpIdArrival, increment]
          · simp [idArrivals, isWarpIdArrival, increment, hw', Ne.symm hw']
        rw [heq]
        exact hs.arrival hn hcount hcard hbound hw hf
      · have heq : idArrivals (xs ++ [Record.arrival other warp cnt lanes]) id =
            idArrivals xs id := by
          funext w
          simp [idArrivals, isWarpIdArrival, hother]
        rw [heq]
        exact hs.other_arrival (Ne.symm hother) hf
    | exit g e =>
      have heq : idArrivals (xs ++ [Record.exit g e]) id = idArrivals xs id := by
        funext w
        simp [idArrivals, isWarpIdArrival]
      rw [heq]
      exact hs.exit hcard hbound hf

/-- At the actual current arrival, the preceding number of occurrences of this
ID and warp is exactly the slot's true generation. -/
theorem generation_at_record {block n : Nat} {count : Option Nat} {p : Finset Nat}
    {id warp index : Nat} {h : List (Record α)} {lanes : List (Nat × α)} {s t : CtaBarrier.State}
    (hp : Protocol count p id (h.take index)) (hn : 0 < n) (hcount : target block count = .ok n)
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < block / 32) (hw : warp ∈ p)
    (hs : At block h index s)
    (ht : Record.perform block s (.arrival id warp count lanes) = .ok t) :
    idArrivals (h.take index) id warp = (s.slots id).generation := by
  have hl := hp.run_ledger hn hcount hcard hbound hs
  simp only [Record.perform] at ht
  split_ifs at ht
  exact hl.arrival_generation hw ht

/-- An exited thread of a checked history has an exit record in it. -/
theorem run_exited_mem {block : Nat} {h : List (Record α)} {s : CtaBarrier.State}
    (hr : run block {} h = .ok s) {g : Nat} (hm : g ∈ s.exited) : ∃ a, Record.exit g a ∈ h := by
  induction h using List.reverseRecOn generalizing s with
  | nil =>
    cases hr
    simp at hm
  | @append_singleton xs r ih =>
    obtain ⟨u, hu⟩ := run_prefix hr
    have hf : r.perform block u = .ok s := by
      rw [run_append, hu] at hr
      cases hf : r.perform block u with
      | error err => simp [run, hf, Except.bind] at hr
      | ok v => simpa only [run, hf, Except.bind, Except.ok.injEq, throw, throwThe,
          MonadExceptOf.throw] using hr
    cases r with
    | arrival other warp count lanes =>
      simp only [Record.perform] at hf
      split_ifs at hf
      rw [arrive_exited hf] at hm
      obtain ⟨a, ha⟩ := ih hu hm
      exact ⟨a, List.mem_append_left _ ha⟩
    | exit g' a =>
      change exitThread block u g' = .ok s at hf
      unfold exitThread at hf
      split_ifs at hf
      · simp only [pure, Except.pure, Except.ok.injEq] at hf
        subst hf
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · exact ⟨a, by simp⟩
        · obtain ⟨b, hb⟩ := ih hu hm'
          exact ⟨b, List.mem_append_left _ hb⟩
      · simp [bind, Except.bind, throw] at hf

/-- Every lane in the participant warps remains live in a prefix without their exits. -/
theorem run_protected {block : Nat} {p : Finset Nat} {h : List (Record α)} {s : CtaBarrier.State}
    (hx : ∀ g a, Record.exit g a ∈ h → g / 32 ∉ p) (hr : run block {} h = .ok s) :
    ∀ g < block, g / 32 ∈ p → g ∉ s.exited := by
  intro g hg hgp hm
  obtain ⟨a, ha⟩ := run_exited_mem hr hm
  exact hx g a ha hgp

/-- A live lane of a participant warp makes the warp live. -/
theorem warpLive_of_lane {block g : Nat} {e : Finset Nat} (hg : g < block) (hn : g ∉ e) :
    warpLive block e (g / 32) :=
  ⟨g % 32, Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), by omega, by
    rwa [show g / 32 * 32 + g % 32 = g by omega]⟩

/-- A participant warp none of whose lanes has exited is live. -/
theorem lane_live {block : Nat} {p : Finset Nat} {s : CtaBarrier.State}
    (hbound : ∀ w ∈ p, w < block / 32)
    (hlive : ∀ g < block, g / 32 ∈ p → g ∉ s.exited) {w : Nat} (hw : w ∈ p) :
    warpLive block s.exited w := by
  have hb := hbound w hw
  have h := warpLive_of_lane (block := block) (e := s.exited) (g := w * 32) (by omega)
    (hlive _ (by omega) (by rwa [Nat.mul_div_cancel _ (by decide)]))
  rwa [Nat.mul_div_cancel _ (by decide)] at h

/-- Advancing beyond a generation records every participant lane that is still live in that
generation. This uses count saturation in the checked history. -/
theorem completed_participant_record {block n : Nat} {count : Option Nat} {p : Finset Nat}
    {id phase : Nat} {h : List (Record α)} {s : CtaBarrier.State}
    (hp : Protocol count p id h) (hn : 0 < n) (hcount : target block count = .ok n)
    (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < block / 32)
    (hr : run block {} h = .ok s) (hphase : phase < (s.slots id).generation)
    {g : Nat} (hg : g < block) (hw : g / 32 ∈ p) (hlive : g ∉ s.exited) :
    ∃ (index : Nat) (lanes : List (Nat × α)) (e : α),
      h[index]? = some (.arrival id (g / 32) count lanes) ∧
      (g, e) ∈ lanes ∧ GenerationOf block h e id phase := by
  have hl := hp.run_ledger hn hcount hcard hbound hr
  have hb := hl.balance (g / 32) hw (warpLive_of_lane hg hlive)
  have hocc : phase < h.countP (isWarpIdArrival id (g / 32)) := by
    change phase < idArrivals h id (g / 32)
    omega
  obtain ⟨index, r, hi, hsel, hprior⟩ := countP_index hocc
  cases r with
  | exit _ _ => simp [isWarpIdArrival] at hsel
  | arrival other warp cnt lanes =>
    have hfields : other = id ∧ warp = g / 32 := by
      simpa only [isWarpIdArrival, Bool.and_eq_true, beq_iff_eq] using hsel
    obtain ⟨hid, hwarp⟩ := hfields
    subst other
    subst warp
    have hsource := hp _ (List.mem_of_getElem? hi) rfl
    have hcnt := hsource.2
    subst cnt
    obtain ⟨before, after, hbefore, hafter⟩ := run_at_record hr hi
    have hpref : Protocol count p id (h.take index) := by
      have hh : Protocol count p id (h.take index ++ h.drop index) := by simpa using hp
      exact hh.prefix
    have hil := (List.getElem?_eq_some_iff.mp hi).1
    have hnot : g ∉ before.exited := fun hm => hlive (exited_prefix (j := h.length) hil.le hbefore
      (by unfold At; rw [List.take_length]; exact hr) hm)
    have hmembers := perform_arrival_lanes hafter
    obtain ⟨pair, hpair, hpairg⟩ := List.mem_map.mp (hmembers.2.2 g hg rfl hnot)
    have hpge : (g, pair.2) = pair := by rw [← hpairg]
    have hgmember : (g, pair.2) ∈ lanes := hpge.symm ▸ hpair
    have hgeneration := generation_at_record hpref hn hcount hcard hbound hw hbefore hafter
    have hprior' : idArrivals (h.take index) id (g / 32) = phase := hprior
    refine ⟨index, lanes, pair.2, hi, hgmember, index, before, g / 32,
      count, lanes, g, hi, hbefore, hgmember, ?_, after, hafter⟩
    omega

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- A recorded participant arrival has the key determined by its actual
named-resource source occurrence count. All history generation premises are
conclusions of replay, rather than chosen source phases. -/
theorem source_key [hK : Fact K.NoBarArrive] (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {c index id warp : Nat} {lanes : List (Nat × EvId)} {e : EvId}
    (hc : c < L.grid)
    (hr : (X.barriers c)[index]? = some (.arrival id warp count lanes))
    (he : e ∈ (Record.arrival id warp count lanes).refs)
    (hp : Protocol count p id ((X.barriers c).take index))
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) (hw : warp ∈ p) :
    CtaBarK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
  obtain ⟨s, t, hs, ht⟩ := run_at_record hlast hr
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp he
  have hsrc := ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hr)) q hq
  have hlane := (perform_arrival_lanes ht).2.1 q hq
  have hthread : e.1 = c * L.block + q.1 := by rw [← hqe]; exact hsrc.2.1
  have hocc := cta_prefix_id_arrival_count (id := id) hX hc hr he hs hlane.1 hthread hlane.2.2 rfl
  rw [hlane.2.1] at hocc
  have hgen := generation_at_record hp hn hcount hcard hbound hw hs ht
  have hord : ((X.tr e.1).take e.2).countP (Execution.isBarId id) = (s.slots id).generation :=
    hocc.symm.trans hgen
  have hg : e.1 < L.threads := by
    rw [hthread]
    exact cta_thread_lt hc hlane.1
  have hcta := cta_ref_cta hX hc hr he
  have ha : arrive L.block s id warp count = .ok t := by
    simp only [Record.perform] at ht
    split_ifs at ht
    exact ht
  have hid : id < 16 := by
    by_contra hnid
    simp [arrive, hnid, bind, Except.bind, throw] at ha
  apply hX.ctaBarK_of_arrival hK.out
  apply CtaBarArrivalK.of_generation hX.ctaBar hg hid
  rw [hcta]
  refine ⟨index, s, warp, count, lanes, q.1, hr, hs, ?_, hord.symm, t, ht⟩
  have hpair : (q.1, e) = q := by rw [← hqe]
  rw [hpair]
  exact hq

/-- The source protocol is required only before the record containing this event.
It says nothing about exits after the current shared cursor. -/
def PrefixFor (L : Launch) (X : Execution) (count : Option Nat) (p : Finset Nat) (id : Nat)
    (e : EvId) : Prop :=
  ∀ index warp cnt lanes,
    (X.barriers (e.1 / L.block))[index]? = some (.arrival id warp cnt lanes) →
    e ∈ (Record.arrival id warp cnt lanes).refs →
    Protocol count p id ((X.barriers (e.1 / L.block)).take index) ∧
      warp ∈ p ∧ cnt = count

/-- Passing a real participant barrier supplies its history witness. Its resource key
is then computed from its actual source ordinal, with no key or phase input. -/
theorem passed_key [Fact K.NoBarArrive] (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {e : EvId} {id pc : Nat}
    (he : X.IsBarrier e id count pc)
    (hpassed : e.2 + 1 < (X.tr e.1).length) (hp : PrefixFor L X count p id e)
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) :
    CtaBarK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  obtain ⟨key, hkey, _⟩ := ctaBarDone_of_returned hX he hpassed
  obtain ⟨_, _, he'⟩ := hkey.2.1
  have hid : key % 16 = id :=
    (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans he))).2).1
  have hgen := hkey.2.2
  rw [hid] at hgen
  obtain ⟨index, _, warp, count', lanes, g, hr, _, hm, _, _, _⟩ := hgen
  have href : e ∈ (Record.arrival id warp count' lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩
  obtain ⟨hprotocol, hw, hcnt⟩ := hp index warp count' lanes hr href
  subst count'
  have hc : e.1 / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul (block_pos_of_thread_lt hkey.1)).mpr hkey.1
  exact source_key hX hn hcount hc hr href hprotocol hcard hbound hw

private theorem source_ordinal_strict {g i j id pc : Nat} {count : Option Nat}
    (he : X.IsBarrier (g, i) id count pc) (hij : i < j) :
    ((X.tr g).take i).countP (Execution.isBarId id) <
      ((X.tr g).take j).countP (Execution.isBarId id) := by
  have hget : (X.tr g)[i]? = some ⟨pc, .bar id count⟩ := he
  have hs : ((X.tr g).take (i + 1)).countP (Execution.isBarId id) =
      ((X.tr g).take i).countP (Execution.isBarId id) + 1 := by
    rw [List.take_add_one, hget]
    simp [Execution.isBarId]
  have hm := (List.take_sublist_take_left (l := X.tr g) (by omega : i + 1 ≤ j)).countP_le
    (p := Execution.isBarId id)
  omega

/-- Two real occurrences of one named barrier in one source thread have unique
occurrence ordinals, even if other IDs interleave in that trace. -/
theorem source_ordinal_unique {g i j id pc pc' : Nat} {count count' : Option Nat}
    (he : X.IsBarrier (g, i) id count pc) (hf : X.IsBarrier (g, j) id count' pc')
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr g).take j).countP (Execution.isBarId id)) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have hh := source_ordinal_strict he h
    omega
  · exact h
  · have hh := source_ordinal_strict hf h
    omega

end
end PTX.NamedBar
