-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarSync
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-!
# The early generations of a named barrier that has several groups

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/BarEarly.lean`, the
generic part of its barrier-0 analysis).
The library's generation lemmas (`NamedBar.Sources`) ask one `(count, p)` for every arrival on a
barrier id. Of a barrier id that several groups use in turn (Inkling's barrier 0 has three),
what is true is a statement about the arrivals of small source ordinal: *the arrivals of a
thread's first `N + 1` events on the barrier are the group's*. This file proves what that needs
on the barrier's resource history:

* `idArrivals_le`: along `CtaBarrier.run`, the number of a warp's arrival records on barrier `id`
  is at most the resource's generation plus one if the warp has arrived in the open generation (a
  warp cannot arrive twice in one generation);
* `idArrivals_le_generation`: so the number of a warp's arrival records before an arrival record is
  at most the generation just before it;
* `completes_below`, `released_of_lt`: every generation below the final one is completed by an
  update of the history;
* `EarlySources`: the premise, that the arrivals on the barrier of source ordinal at most `N` are
  the group's (participant warp, the group's count);
* `early_protocol`: the history records before the completion of generation `φ ≤ N` follow the
  group's protocol (`NamedBar.Protocol`), because a record's source ordinal is at most its
  generation;
* **`early_same_ordinal_baseCausality`**: a reached arrival and a passed arrival of the same source
  ordinal `≤ N` in one CTA synchronize (`baseCausality` from what the first did before to what the
  second does after), whatever the barrier's later arrivals (other counts, other warps) are.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {α : Type}

/-- A successful arrival of warp `w` found `w` not arrived in the open generation. -/
theorem arrive_not_arrived {block id w : Nat} {cnt : Option Nat} {s t : State}
    (h : arrive block s id w cnt = .ok t) : w ∉ (s.slots id).arrived := by
  by_cases hid : id < 16
  · by_cases hw : w < warps block ∧ warpLive block s.exited w
    · cases hn : target block cnt with
      | error err => simp [arrive, hid, hw, hn, bind, Except.bind] at h
      | ok n =>
        by_cases ha : w ∈ (s.slots id).arrived
        · simp [arrive, hid, hw, hn, ha, bind, Except.bind, pure, Except.pure, throw] at h
        · exact ha
    · simp [arrive, hid, hw, bind, Except.bind, pure, Except.pure, throw] at h
  · simp [arrive, hid, bind, Except.bind, pure, Except.pure, throw] at h

/-- The measure of a slot for one warp: its generation, plus one if the warp has arrived. -/
def slotMeasure (s : State) (id w : Nat) : Nat :=
  (s.slots id).generation + if w ∈ (s.slots id).arrived then 1 else 0

/-- **One update never lowers the measure, and an arrival of the warp on the barrier raises it.** -/
theorem perform_measure {block id w : Nat} {r : Record α} {s t : State}
    (h : r.perform block s = .ok t) :
    slotMeasure s id w + (if isWarpIdArrival id w r = true then 1 else 0) ≤
      slotMeasure t id w := by
  cases r with
  | exit g e =>
    simp only [Record.perform, exitThread] at h
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp only [hg, not_false_eq_true, and_self, bind, Except.bind, pure,
        Except.pure] at h
      cases h
      simp only [slotMeasure, isWarpIdArrival]
      by_cases hc : complete block (insert g s.exited) (s.slots id) = true
      · simp [settle, hc]
        split_ifs <;> omega
      · simp [settle, hc]
    · simp [hg, bind, Except.bind, throw] at h
  | arrival id' w' cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h with hl
    have hna := arrive_not_arrived h
    obtain ⟨n, -, -, hslots⟩ := arrive_shape h
    simp only [slotMeasure, isWarpIdArrival, hslots]
    by_cases hi : id = id'
    · subst hi
      by_cases hww : w = w'
      · subst hww
        by_cases hc : complete block s.exited
            { s.slots id with expected := some n, arrived := insert w (s.slots id).arrived } = true
        · simp [settle, hc, hna]
        · simp [settle, hc, hna]
      · by_cases hc : complete block s.exited
            { s.slots id with expected := some n, arrived := insert w' (s.slots id).arrived } = true
        · simp [settle, hc]
          split_ifs <;> omega
        · simp [settle, hc, Ne.symm hww]
          split_ifs <;> simp_all
    · simp [hi, Ne.symm hi]

/-- **A warp's arrival records on a barrier number at most the resource's measure.** -/
theorem idArrivals_le {block id w : Nat} :
    ∀ (h : List (Record α)) {s t : State}, run block s h = .ok t →
      idArrivals h id w + slotMeasure s id w ≤ slotMeasure t id w := by
  intro h
  induction h with
  | nil =>
    intro s t ht
    simp only [run, Except.ok.injEq] at ht
    subst ht
    simp [idArrivals]
  | cons r rs ih =>
    intro s t ht
    simp only [run] at ht
    cases hp : r.perform block s with
    | error err => simp [hp, Except.bind] at ht
    | ok u =>
      have ht' : run block u rs = .ok t := by simpa [hp, Except.bind] using ht
      have h1 := perform_measure (id := id) (w := w) hp
      have h2 := ih ht'
      have h3 : idArrivals (r :: rs) id w =
          idArrivals rs id w + (if isWarpIdArrival id w r = true then 1 else 0) := by
        simp only [idArrivals, List.countP_cons]
      omega

/-- **The records of a warp before an arrival record number at most the generation just before it**:
at the state `s` before the record at `k`, which is an arrival of the warp on the barrier. -/
theorem idArrivals_le_generation {block id w k : Nat} {h : List (Record α)} {s : State}
    {last : State} (hrun : run block {} h = .ok last) (hs : At block h k s)
    {cnt : Option Nat} {lanes : List (Nat × α)}
    (hk : h[k]? = some (.arrival id w cnt lanes)) :
    idArrivals (h.take k) id w ≤ (s.slots id).generation := by
  obtain ⟨s', t, hat, hp⟩ := run_at_record hrun hk
  have hss : s' = s := by
    have h1 : run block {} (h.take k) = .ok s' := hat
    have h2 : run block {} (h.take k) = .ok s := hs
    exact Except.ok.inj (h1.symm.trans h2)
  subst hss
  have h0 := idArrivals_le (id := id) (w := w) (h.take k) (s := {}) hat
  have hmeas : slotMeasure ({} : State) id w = 0 := by simp [slotMeasure]
  have hna : w ∉ (s'.slots id).arrived := by
    simp only [Record.perform] at hp
    split_ifs at hp
    exact arrive_not_arrived hp
  have hs' : slotMeasure s' id w = (s'.slots id).generation := by simp [slotMeasure, hna]
  omega

/-- One update raises the generation of a barrier by at most one. -/
theorem perform_generation_le {block id : Nat} {r : Record α} {s t : State}
    (h : r.perform block s = .ok t) :
    (t.slots id).generation ≤ (s.slots id).generation + 1 := by
  cases r with
  | exit g e =>
    simp only [Record.perform, exitThread] at h
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp only [hg, not_false_eq_true, and_self, bind, Except.bind, pure, Except.pure] at h
      cases h
      have := settle_generation block (insert g s.exited) (s.slots id)
      change (settle block (insert g s.exited) (s.slots id)).generation ≤ _
      omega
    · simp [hg, bind, Except.bind, throw] at h
  | arrival id' w cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h with hl
    obtain ⟨n, -, -, hslots⟩ := arrive_shape h
    rw [hslots]
    by_cases hi : id = id'
    · subst hi
      simp only [↓reduceIte]
      have key : ∀ sl : Slot, sl.generation = (s.slots id).generation →
          (settle block s.exited sl).generation ≤ (s.slots id).generation + 1 := by
        intro sl hsl
        have := settle_generation block s.exited sl
        omega
      exact key _ rfl
    · simp [hi]

/-- **Every generation below the current one has been completed by an update of the history.** -/
theorem completes_below {block id : Nat} {h : List (Record α)} :
    ∀ (k : Nat) {s : State}, At block h k s → ∀ φ, φ < (s.slots id).generation →
      ∃ i, i < k ∧ CompletesAt block h i id φ := by
  intro k
  induction k with
  | zero =>
    intro s hs φ hφ
    unfold At at hs
    simp only [List.take_zero, run, Except.ok.injEq] at hs
    subst hs
    simp at hφ
  | succ k ih =>
    intro s hs φ hφ
    by_cases hlt : k < h.length
    · obtain ⟨r, hr⟩ : ∃ r, h[k]? = some r := ⟨h[k], List.getElem?_eq_getElem hlt⟩
      have hs' := hs
      unfold At at hs'
      rw [List.take_succ_eq_append_getElem hlt, run_append] at hs'
      obtain ⟨s0, hs0⟩ : ∃ s0, run block {} (h.take k) = .ok s0 := by
        cases hq : run block {} (h.take k) with
        | error e => rw [hq] at hs'; simp [Except.bind] at hs'
        | ok s0 => exact ⟨s0, rfl⟩
      rw [hs0] at hs'
      have hr' : h[k] = r := by
        have := List.getElem?_eq_getElem hlt
        rw [hr] at this
        exact (Option.some.inj this).symm
      rw [hr'] at hs'
      simp only [Except.bind, run] at hs'
      cases hp : r.perform block s0 with
      | error e => rw [hp] at hs'; cases hs'
      | ok u =>
        rw [hp] at hs'
        simp only [Except.ok.injEq] at hs'
        have hu : u = s := by simpa using hs'
        subst hu
        have hle := perform_generation_le (id := id) hp
        by_cases hlo : φ < (s0.slots id).generation
        · obtain ⟨i, hi, hc⟩ := ih hs0 φ hlo
          exact ⟨i, by omega, hc⟩
        · refine ⟨k, Nat.lt_succ_self k, r, s0, u, hr, hs0, hp, ?_, ?_⟩ <;> omega
    · have hk : h.take (k + 1) = h.take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have hs' : At block h k s := by
        unfold At at hs ⊢
        rwa [hk] at hs
      obtain ⟨i, hi, hc⟩ := ih hs' φ hφ
      exact ⟨i, by omega, hc⟩

/-- **A generation below the final one is released.** -/
theorem released_of_lt {block id φ : Nat} {h : List (Record α)} {last : State}
    (hrun : run block {} h = .ok last) (hφ : φ < (last.slots id).generation) :
    Released block h id φ := by
  have hat : At block h h.length last := by
    unfold At
    rwa [List.take_length]
  obtain ⟨i, -, hc⟩ := completes_below h.length hat φ hφ
  exact ⟨i, hc⟩

/-! ### The source side -/

section Source

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **The arrivals on barrier `id` of source ordinal at most `N` are the group's**: a lane of a
participant warp passing the group's count. -/
def EarlySources (L : Launch) (X : Execution) (count : Option Nat) (p : Finset Nat)
    (id N : Nat) : Prop :=
  ∀ e pc cnt, X.IsBarArrival e id cnt pc → e.1 < L.threads →
    ((X.tr e.1).take e.2).countP (Execution.isBarId id) ≤ N →
    (e.1 % L.block) / 32 ∈ p ∧ cnt = count

/-- The record at `k` of a CTA's history that has a lane `q`: the lane's source event is in the CTA
(`e.1 = c * block + q.1`), is an arrival on the barrier, and its source ordinal is the number of
the warp's arrival records before `k`. -/
theorem record_ordinal (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid) {k id w : Nat}
    {cnt : Option Nat} {lanes : List (Nat × EvId)} {last : State}
    (hlast : run L.block {} (X.barriers c) = .ok last)
    (hr : (X.barriers c)[k]? = some (.arrival id w cnt lanes)) {s : State}
    (hat : At L.block (X.barriers c) k s) {q : Nat × EvId} (hq : q ∈ lanes) :
    q.1 < L.block ∧ q.2.1 = c * L.block + q.1 ∧ q.1 / 32 = w ∧
      (∃ pc, X.IsBarArrival q.2 id cnt pc) ∧
      idArrivals ((X.barriers c).take k) id w =
        ((X.tr q.2.1).take q.2.2).countP (Execution.isBarId id) ∧
      idArrivals ((X.barriers c).take k) id w ≤ (s.slots id).generation := by
  obtain ⟨s', t, hat', hp⟩ := run_at_record hlast hr
  have hss : s' = s := by
    have h1 : run L.block {} ((X.barriers c).take k) = .ok s' := hat'
    have h2 : run L.block {} ((X.barriers c).take k) = .ok s := hat
    exact Except.ok.inj (h1.symm.trans h2)
  subst hss
  obtain ⟨-, hl2, -⟩ := perform_arrival_lanes hp
  obtain ⟨hql, hqw, hqx⟩ := hl2 q hq
  have hmem : (Record.arrival id w cnt lanes) ∈ X.barriers c := List.mem_of_getElem? hr
  obtain ⟨-, hsrcs, -⟩ := hX.ctaBar.2 c hc
  obtain ⟨-, hq2, hq3⟩ := hsrcs _ hmem q hq
  have href : q.2 ∈ (Record.arrival id w cnt lanes).refs := List.mem_map.mpr ⟨q, hq, rfl⟩
  have hord := cta_prefix_id_arrival_count hX hc hr href hat' hql hq2 hqx rfl
  rw [hqw] at hord
  exact ⟨hql, hq2, hqw, hq3, hord, idArrivals_le_generation hlast hat' hr⟩

/-- **The records before the completion of generation `φ ≤ N` follow the group's protocol.** -/
theorem early_protocol (hX : Consistent L K A mem0 X) {count : Option Nat} {p : Finset Nat}
    {id N : Nat} (hS : EarlySources L X count p id N) {c : Nat} (hc : c < L.grid)
    {idx φ : Nat} (hφ : φ ≤ N) (hcomp : CompletesAt L.block (X.barriers c) idx id φ) :
    Protocol count p id ((X.barriers c).take (idx + 1)) := by
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 c hc
  intro r hr
  obtain ⟨k, hrk⟩ := List.mem_iff_getElem?.mp hr
  have hkidx : k < idx + 1 := by
    have := (List.getElem?_eq_some_iff.mp hrk).1
    simp only [List.length_take] at this
    omega
  have hr' : (X.barriers c)[k]? = some r := by
    rw [List.getElem?_take_of_lt hkidx] at hrk
    exact hrk
  cases r with
  | exit _ _ => trivial
  | arrival other w cnt lanes =>
    intro hother
    subst hother
    obtain ⟨s0, t0, hat, hp⟩ := run_at_record hlast hr'
    obtain ⟨e, he⟩ := perform_ref_exists hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨hql, hq2, hqw, ⟨pc, hbar⟩, hord, hle⟩ := record_ordinal hX hc hlast hr' hat hq
    obtain ⟨r2, s2, t2, -, hat2, -, hgen2, -⟩ := hcomp
    have hmono : (s0.slots other).generation ≤ (s2.slots other).generation := by
      have hat0 : At L.block ((X.barriers c).take idx) k s0 := by
        unfold At at hat ⊢
        rwa [List.take_take, Nat.min_eq_left (by omega : k ≤ idx)]
      exact at_generation_mono hat0 hat2 other
    have hthr : q.2.1 < L.threads := by
      rw [hq2]
      exact cta_thread_lt hc hql
    have hmod : q.2.1 % L.block = q.1 := by
      rw [hq2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hql]
    have := hS q.2 pc cnt hbar hthr (by omega)
    rw [hmod, hqw] at this
    exact this

/-- **A thread's arrival record has a generation at least its source ordinal.** -/
theorem ordinal_le_generation (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {e : EvId} {id G : Nat} (hgen : GenerationOf L.block (X.barriers c) e id G) :
    ((X.tr e.1).take e.2).countP (Execution.isBarId id) ≤ G := by
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 c hc
  obtain ⟨i, s, warp, cnt, lanes, g, hi, hat, hm, hG, -⟩ := hgen
  have href : (g, e) ∈ lanes := hm
  obtain ⟨-, -, -, -, hord, hle⟩ := record_ordinal hX hc hlast hi hat href
  rw [← hG]
  exact hord ▸ hle

end Source

/-! ### The synchronization of the early ordinals -/

section Sync

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [hK : Fact K.NoBarArrive]

/-- **Two arrivals of the same early source ordinal synchronize** on a barrier whose arrivals of
source ordinal at most `N` are the group's (`EarlySources`), whatever the later arrivals are. A
reached arrival of one CTA-local thread and a passed arrival of another thread in the same CTA at
equal source ordinals `≤ N`: what the first thread did before its arrival happens before what the
second does after passing its own. -/
theorem early_same_ordinal_baseCausality (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n) {p : Finset Nat}
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) {id N : Nat} (hid : id < 16)
    (hS : EarlySources L X count p id N) {g h i j before after pc pc' : Nat}
    (hsame : SameCta L g h) (he : X.IsBarrier (g, i) id count pc)
    (hf : X.IsBarrier (h, j) id count pc') (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hN : ((X.tr h).take j).countP (Execution.isBarId id) ≤ N)
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  have hh : h < L.threads := hsame.2.1
  have hc : h / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul (block_pos_of_thread_lt hh)).mpr hh
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 (h / L.block) hc
  set φ := ((X.tr h).take j).countP (Execution.isBarId id) with hφ
  -- the generation of the passed arrival, and the release of generation `φ`
  obtain ⟨key, hkf0, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkid : key % 16 = id := by
    obtain ⟨count', pc'', he'⟩ := hkf0.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hf))).2).1
  have hgen := hkf0.2.2
  rw [hkid] at hgen
  have hφG : φ ≤ key / 16 := ordinal_le_generation hX hc hgen
  have hrel : Released L.block (X.barriers (h / L.block)) id (key / 16) := by
    have hd' := hdone
    unfold CtaBarDone at hd'
    rw [hkid] at hd'
    exact hd'
  have hlt : key / 16 < (last.slots id).generation := released_generation_lt hlast hrel
  have hrelφ : Released L.block (X.barriers (h / L.block)) id φ :=
    released_of_lt hlast (by omega)
  have hp : ∀ idx, CompletesAt L.block (X.barriers (h / L.block)) idx id φ →
      Protocol count p id ((X.barriers (h / L.block)).take (idx + 1)) :=
    fun idx hcomp => early_protocol hX hS hc hN hcomp
  have hwf : (h % L.block) / 32 ∈ p := (hS (h, j) pc' count ⟨.sync, hf⟩ hh hN).1
  have hwe : (g % L.block) / 32 ∈ p :=
    (hS (g, i) pc count ⟨.sync, he⟩ hsame.1 (by rw [hordinal]; exact hN)).1
  have hkf : CtaBarK L X (h, j) (id + 16 * φ) :=
    reached_key_of_release hX hn hcount hid hf hh hwf rfl hrelφ hp hcard hbound
  have hrelg : Released L.block (X.barriers (g / L.block)) id φ := by
    rw [hsame.2.2]
    exact hrelφ
  have hpg : ∀ idx, CompletesAt L.block (X.barriers (g / L.block)) idx id φ →
      Protocol count p id ((X.barriers (g / L.block)).take (idx + 1)) := by
    rw [hsame.2.2]
    exact hp
  have hke : CtaBarK L X (g, i) (id + 16 * φ) :=
    reached_key_of_release hX hn hcount hid he hsame.1 hwe hordinal hrelg hpg hcard hbound
  have hs : CtaBarSync L X (g, before) (h, after) :=
    ⟨hsame, id + 16 * φ, i, j, CtaBarK.arrival hke, hkf, hbefore, hafter, hlen⟩
  exact Relation.TransGen.single (Or.inr (Or.inl hs))

end Sync

end
end PTX.NamedBar
