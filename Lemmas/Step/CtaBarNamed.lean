-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBar
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Step.Released
public import Lemmas.Snoc.ExtensionSnocFrame
public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.CtaBarrier.CtaBarrierRoundCompletion

@[expose] public section

/-! # Finishing a named barrier generation whose participants have all arrived

A proof tool. In a named resource of `n` participant warps, a generation whose every participant
lane has made its arrival as the last event of its thread can be completed by appending the
records of the participant warps that have none (`finish_named`). The records form an
arrival-only suffix of the CTA's history that the object accepts and that completes the generation
(`released_of_arrival_run_cnt`).

At a thread blocked at its arrival on a named barrier, not released, either a participant lane of
its CTA has made fewer arrivals on the barrier, or every participant has an arrival of the blocked
one's ordinal, and appending the missing records releases the thread (`wait_cases`). -/

namespace PTX.CtaBarrier
open PTX
variable {α : Type}

/-- The record of all lanes of a warp is performed as the warp's arrival when no lane has exited. -/
theorem fullLanes_perform_of {block warp id : Nat} {cnt : Option Nat} {s : State}
    (hlive : ∀ g < block, g / 32 = warp → g ∉ s.exited) (event : Nat → α) :
    Record.perform block s (.arrival id warp cnt (fullLanes block warp event)) =
      arrive block s id warp cnt := by
  apply ite_eq_left
  constructor
  · simp only [fullLanes, List.map_map, Function.comp_def]
    exact (List.nodup_range.filter _).map (fun a b h => Nat.add_left_cancel h)
  · constructor
    · intro p hp
      obtain ⟨lane, hlane, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hr, hbound⟩ := List.mem_filter.mp hlane
      have hl32 := List.mem_range.mp hr
      exact ⟨of_decide_eq_true hbound, by omega, hlive _ (of_decide_eq_true hbound) (by omega)⟩
    · intro lane hlane
      dsimp only
      intro hg _
      simp only [fullLanes, List.map_map, Function.comp_def]
      apply List.mem_map.mpr
      refine ⟨lane, ?_, rfl⟩
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hlane), by simpa using hg⟩

/-- A successful suffix of arrivals to one resource with one count cannot advance the resource's
generation without an actual record completing the preceding generation. -/
theorem released_of_arrival_run_cnt {block id : Nat} {cnt : Option Nat} {xs ys : List (Record α)}
    {s t : State} (hplain : ∀ r ∈ ys, ∃ w lanes, r = .arrival id w cnt lanes)
    (hx : run block {} xs = .ok s) (hy : run block s ys = .ok t)
    (hlt : (s.slots id).generation < (t.slots id).generation) :
    Released block (xs ++ ys) id (s.slots id).generation := by
  induction ys generalizing xs s with
  | nil => simp only [run, Except.ok.injEq] at hy; subst t; omega
  | cons r ys ih =>
    obtain ⟨w, lanes, rfl⟩ := hplain r (by simp)
    let r : Record α := .arrival id w cnt lanes
    cases hu : r.perform block s with
    | error err =>
      dsimp only [r] at hu
      simp only [run, hu, Except.bind] at hy
      cases hy
    | ok u =>
      dsimp only [r] at hu
      have hy' : run block u ys = .ok t := by simpa only [run, hu, Except.bind] using hy
      have hperf : arrive block s id w cnt = .ok u := by
        have hh := hu
        simp only [Record.perform] at hh
        split_ifs at hh
        exact hh
      obtain ⟨n, _, _, hslots⟩ := arrive_shape hperf
      have hslot : u.slots id = settle block s.exited
          {s.slots id with expected := some n, arrived := insert w (s.slots id).arrived} := by
        simpa only [ite_true] using hslots id
      have hgen : (u.slots id).generation = (s.slots id).generation ∨
          (u.slots id).generation = (s.slots id).generation + 1 := by
        rw [hslot]
        exact settle_generation _ _ _
      rcases hgen with hg | hg
      · have hx' : run block {} (xs ++ [r]) = .ok u := by
          rw [run_append, hx]
          simp only [run, r, hu, Except.bind]
        have hh := ih (by intro q hq; exact hplain q (List.mem_cons_of_mem _ hq)) hx' hy'
          (by omega)
        rw [hg] at hh
        simpa only [List.append_assoc, List.singleton_append, r] using hh
      · refine ⟨xs.length, r, s, u, ?_, ?_, hu, rfl, hg⟩
        · simp [r]
        · unfold At
          rw [List.take_append_of_le_length le_rfl]
          simpa only [List.take_length] using hx

end PTX.CtaBarrier

namespace PTX.NamedBar
open PTX CtaBarrier
variable {α : Type}

/-- A participant warp that has not arrived can arrive. -/
theorem arrive_exists {block n id w : Nat} {count : Option Nat} {p : Finset Nat}
    {counts : Nat → Nat} {s : State}
    (h : Ledger block n p id counts s) (hid : id < 16) (hcount : target block count = .ok n)
    (hw : w ∈ p) (hbound : ∀ w ∈ p, w < block / 32) (ha : w ∉ (s.slots id).arrived)
    (hlive : warpLive block s.exited w) :
    ∃ t, arrive block s id w count = .ok t := by
  have hwb : w < warps block := by
    have := hbound w hw
    unfold warps
    omega
  have hl : w < warps block ∧ warpLive block s.exited w := ⟨hwb, hlive⟩
  have hexp : (s.slots id).expected = none ∨ (s.slots id).expected = some n := by
    rw [h.expected]
    split_ifs <;> simp
  rcases hexp with hx | hx <;>
    simp [arrive, hid, hl, ha, hx, hcount, bind, Except.bind, pure, Except.pure]

/-- **One arrival of a participant warp** either leaves the generation and adds the warp to the
arrived set, or completes the generation: the arrival of the last participant. -/
theorem Ledger.arrival_cases {block n : Nat} {count : Option Nat} {p : Finset Nat}
    {id warp : Nat} {counts : Nat → Nat} {s t : State} (h : Ledger block n p id counts s)
    (hn : 0 < n) (hcount : target block count = .ok n)
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < block / 32) (hw : warp ∈ p)
    (hlive : ∀ w ∈ p, warpLive block s.exited w)
    (ha : arrive block s id warp count = .ok t) :
    ((t.slots id).generation = (s.slots id).generation ∧
        (t.slots id).arrived = insert warp (s.slots id).arrived) ∨
      ((t.slots id).generation = (s.slots id).generation + 1 ∧ (t.slots id).arrived = ∅ ∧
        insert warp (s.slots id).arrived = p) := by
  have ht := h.arrival hn hcount hcard hbound hw ha
  have hlive' : ∀ w ∈ p, warpLive block t.exited w := by
    rw [arrive_exited ha]
    exact hlive
  have hmiss : warp ∉ (s.slots id).arrived := by
    by_contra hm
    obtain ⟨m, hm', -, -⟩ := arrive_shape ha
    simp only [arrive] at ha
    split_ifs at ha <;> simp_all [bind, Except.bind, throw, pure, Except.pure]
  have hsub : insert warp (s.slots id).arrived ⊆ p := Finset.insert_subset hw h.owners
  by_cases hB : insert warp (s.slots id).arrived = p
  · right
    have hbal : ∀ w' ∈ p, (t.slots id).generation +
        (if w' ∈ (t.slots id).arrived then 1 else 0) = (s.slots id).generation + 1 := by
      intro w' hw'
      have h1 := ht.balance w' hw' (hlive' w' hw')
      have h2 := h.balance w' hw' (hlive w' hw')
      have hm : w' ∈ insert warp (s.slots id).arrived := hB ▸ hw'
      rcases Finset.mem_insert.mp hm with rfl | hm'
      · simp only [increment, ↓reduceIte, hmiss, Nat.add_zero] at h1 h2
        omega
      · simp only [increment, hm', ↓reduceIte] at h1 h2
        by_cases hww : w' = warp
        · subst hww; exact absurd hm' hmiss
        · simp only [hww, ↓reduceIte] at h1
          omega
    obtain ⟨w0, hw0p, hw0⟩ : ∃ w0 ∈ p, w0 ∉ (t.slots id).arrived := by
      by_contra hall
      push Not at hall
      have := Finset.card_le_card (show p ⊆ (t.slots id).arrived from hall)
      have := ht.card_lt
      omega
    have hg := hbal w0 hw0p
    simp only [hw0, ↓reduceIte] at hg
    refine ⟨by omega, ?_, hB⟩
    ext w'
    simp only [Finset.notMem_empty, iff_false]
    intro hw'
    have := hbal w' (ht.owners hw')
    simp only [hw', ↓reduceIte] at this
    omega
  · left
    obtain ⟨w0, hw0p, hw0⟩ : ∃ w0 ∈ p, w0 ∉ insert warp (s.slots id).arrived := by
      by_contra hall
      push Not at hall
      exact hB (Finset.Subset.antisymm hsub hall)
    have hw0A : w0 ∉ (s.slots id).arrived := fun hm => hw0 (Finset.mem_insert_of_mem hm)
    have hw0w : w0 ≠ warp := fun hh => hw0 (hh ▸ Finset.mem_insert_self _ _)
    have h0 := ht.balance w0 hw0p (hlive' w0 hw0p)
    have h0' := h.balance w0 hw0p (hlive w0 hw0p)
    simp only [increment, hw0w, ↓reduceIte, hw0A] at h0 h0'
    have h1 := ht.balance warp hw (hlive' warp hw)
    have h1' := h.balance warp hw (hlive warp hw)
    simp only [increment, ↓reduceIte, hmiss] at h1 h1'
    have hgen : (t.slots id).generation = (s.slots id).generation := by
      split_ifs at h0 h1 <;> omega
    refine ⟨hgen, ?_⟩
    ext w'
    constructor
    · intro hw'
      have hp' := ht.owners hw'
      have := ht.balance w' hp' (hlive' w' hp')
      have := h.balance w' hp' (hlive w' hp')
      by_cases hww : w' = warp
      · simp [hww]
      · simp only [increment, hww, ↓reduceIte, hw', Nat.add_comm] at *
        by_cases hm : w' ∈ (s.slots id).arrived
        · simp [hm]
        · simp_all
    · intro hw'
      rcases Finset.mem_insert.mp hw' with rfl | hm
      · have := ht.balance w' hw (hlive' w' hw)
        simp only [increment, ↓reduceIte] at this
        by_contra hn'
        simp only [hn', ↓reduceIte] at this
        omega
      · have hp' := h.owners hm
        have := ht.balance w' hp' (hlive' w' hp')
        have := h.balance w' hp' (hlive w' hp')
        by_cases hww : w' = warp
        · subst hww
          exact absurd hm hmiss
        · simp only [increment, hww, ↓reduceIte, hm] at *
          by_contra hn'
          simp_all

/-- **Completing a generation.** From a ledger state in which no participant lane of the
participant warps has exited, the participant warps that have not arrived can arrive, each with all
its lanes, in any order, and the last of them completes the generation: the run is accepted and
the generation advances by one. -/
theorem finish_named {block n id : Nat} {count : Option Nat} {p : Finset Nat} (hid : id < 16)
    (hn : 0 < n) (hcount : target block count = .ok n) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < block / 32)
    (event : Nat → α) :
    ∀ (m : Nat) {counts : Nat → Nat} {s : State}, Ledger block n p id counts s →
      (∀ g < block, g / 32 ∈ p → g ∉ s.exited) → (p \ (s.slots id).arrived).card = m →
      ∃ (ws : List Nat) (t : State), ws.Nodup ∧ (∀ w ∈ ws, w ∈ p ∧ w ∉ (s.slots id).arrived) ∧
        (∀ w ∈ p, w ∉ (s.slots id).arrived → w ∈ ws) ∧
        CtaBarrier.run block s
          (ws.map (fun w => Record.arrival id w count (fullLanes block w event))) =
            .ok t ∧
        (t.slots id).generation = (s.slots id).generation + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro counts s hl hlive hm
    have hwl : ∀ w ∈ p, warpLive block s.exited w := fun w hw => lane_live hbound hlive hw
    have hpos : 0 < (p \ (s.slots id).arrived).card := by
      rw [Finset.card_sdiff_of_subset hl.owners, hcard]
      have := hl.card_lt
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    obtain ⟨hwp, hwA⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨t', ha⟩ := arrive_exists hl hid hcount hwp hbound hwA (hwl w hwp)
    have hperf : Record.perform block s
        (.arrival id w count (fullLanes block w event)) = .ok t' := by
      rw [fullLanes_perform_of (fun g hg hgw => hlive g hg (hgw ▸ hwp)) event]
      exact ha
    have hl' := hl.arrival hn hcount hcard hbound hwp ha
    rcases hl.arrival_cases hn hcount hcard hbound hwp hwl ha with ⟨hg, harr⟩ | ⟨hg, -, hins⟩
    · have hlive' : ∀ g < block, g / 32 ∈ p → g ∉ t'.exited := by
        rw [arrive_exited ha]
        exact hlive
      have hcard' : (p \ (t'.slots id).arrived).card = m - 1 := by
        rw [harr, Finset.sdiff_insert, Finset.card_erase_of_mem hw, hm]
      have hmlt : m - 1 < m := by omega
      obtain ⟨ws, t, hnd, hws, hcov, hr, hgen⟩ := ih (m - 1) hmlt hl' hlive' hcard'
      refine ⟨w :: ws, t, ?_, ?_, ?_, ?_, by omega⟩
      · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
        have := (hws w hmem).2
        rw [harr] at this
        exact this (Finset.mem_insert_self _ _)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨hwp, hwA⟩
        · have h2 := hws v hv
          rw [harr] at h2
          exact ⟨h2.1, fun hh => h2.2 (Finset.mem_insert_of_mem hh)⟩
      · intro v hvp hvA
        by_cases hvw : v = w
        · simp [hvw]
        · refine List.mem_cons_of_mem _ (hcov v hvp ?_)
          rw [harr]
          simpa [hvw] using hvA
      · simp only [List.map_cons, CtaBarrier.run, hperf, Except.bind]
        exact hr
    · refine ⟨[w], t', List.nodup_singleton _, ?_, ?_, ?_, by omega⟩
      · intro v hv
        rw [List.mem_singleton] at hv
        subst hv
        exact ⟨hwp, hwA⟩
      · intro v hvp hvA
        have : v ∈ insert w (s.slots id).arrived := hins ▸ hvp
        rcases Finset.mem_insert.mp this with h | h
        · simp [h]
        · exact absurd h hvA
      · simp only [List.map_cons, List.map_nil, CtaBarrier.run, hperf, Except.bind]

/-- The `r`-th element of a list with a property, counting from zero. -/
theorem exists_ordinal {β : Type} (q : β → Bool) :
    ∀ (l : List β) {r : Nat}, r < l.countP q →
      ∃ j e, l[j]? = some e ∧ q e = true ∧ (l.take j).countP q = r := by
  intro l
  induction l with
  | nil => intro r hr; simp at hr
  | cons a t ih =>
    intro r hr
    by_cases ha : q a = true
    · cases r with
      | zero => exact ⟨0, a, by simp, ha, by simp⟩
      | succ r =>
        have hr' : r < t.countP q := by simp [ha] at hr; omega
        obtain ⟨j, e, hj, he, hjr⟩ := ih hr'
        exact ⟨j + 1, e, by simpa using hj, he, by simp [ha, hjr]⟩
    · have ha' : q a = false := by simpa using ha
      have hr' : r < t.countP q := by simpa [ha'] using hr
      obtain ⟨j, e, hj, he, hjr⟩ := ih hr'
      exact ⟨j + 1, e, by simpa using hj, he, by simp [ha', hjr]⟩

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  [hK : Fact K.NoBarArrive]

/-- The participants of named resource `id` in CTA `c`, warps `p`: every arrival on `id` in
the CTA is a lane of a participant warp with thread-count operand `count`, and no participant
lane has an exit event. -/
structure Part (L : Launch) (X : Execution) (c : Nat) (count : Option Nat) (id : Nat)
    (p : Finset Nat) : Prop where
  src : ∀ e pc cnt, X.IsBarrier e id cnt pc → e.1 / L.block = c →
    (e.1 % L.block) / 32 ∈ p ∧ cnt = count
  noexit : ∀ y, y / L.block = c → (y % L.block) / 32 ∈ p → ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩

/-- A lane of CTA `c`, from its CTA-local index. -/
theorem lane_cta {L : Launch} {c g : Nat} (hb : 0 < L.block) (hg : g < L.block) :
    (c * L.block + g) / L.block = c ∧ (c * L.block + g) % L.block = g := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hg, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]

/-- The records of a CTA's history follow the protocol when every arrival on the resource in the
CTA is by a participant warp counting its threads. -/
theorem protocol_of_src (hX : Consistent L K A mem0 X) {c id : Nat} {count : Option Nat}
    {p : Finset Nat}
    (hsrc : ∀ e pc cnt, X.IsBarrier e id cnt pc → e.1 / L.block = c →
      (e.1 % L.block) / 32 ∈ p ∧ cnt = count)
    (hc : c < L.grid) (hb : 0 < L.block) : Protocol count p id (X.barriers c) := by
  intro r hr
  obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
  have hsrc' := (hX.ctaBar.2 c hc).2.1 r hr
  cases r with
  | arrival other w cnt lanes =>
    intro hother
    subst hother
    obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨s, t, -, hpf⟩ := run_at_record hlast hi
    obtain ⟨e, he⟩ := perform_ref_exists hpf
    obtain ⟨⟨g, f⟩, hm, hfe⟩ := List.mem_map.mp he
    obtain ⟨hg, hfg, pc, hbar⟩ := hsrc' (g, f) hm
    replace hbar := hX.isBarrier_of_arrival hK.out hbar
    have hwarp := ((perform_arrival_lanes hpf).2.1 (g, f) hm).2.1
    obtain ⟨h1, h2⟩ := lane_cta (c := c) hb hg
    have hf1 : f.1 = c * L.block + g := hfg
    have := hsrc f pc cnt hbar (by rw [hf1]; exact h1)
    rw [hf1, h2] at this
    simp only at hwarp
    exact ⟨hwarp ▸ this.1, this.2⟩
  | exit g e => trivial

/-- The records of a CTA's history for the participants follow the protocol: every arrival on the
resource is by a participant warp counting its threads. -/
theorem Part.protocol (hX : Consistent L K A mem0 X) {c id : Nat} {count : Option Nat}
    {p : Finset Nat} (hP : Part L X c count id p) (hc : c < L.grid) (hb : 0 < L.block) :
    Protocol count p id (X.barriers c) :=
  protocol_of_src hX hP.src hc hb

omit hK in
/-- No participant warp's thread has an exit record in the CTA's history. -/
theorem Part.exits (hX : Consistent L K A mem0 X) {c id : Nat} {count : Option Nat}
    {p : Finset Nat} (hP : Part L X c count id p) (hc : c < L.grid) (hb : 0 < L.block) :
    ∀ g e, Record.exit g e ∈ X.barriers c → g / 32 ∉ p := by
  intro g e hr hw
  obtain ⟨hg, he, pc, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ hr
  have hcta : e.1 / L.block = c := by rw [he]; exact (lane_cta hb hg).1
  have hmod : e.1 % L.block = g := by rw [he]; exact (lane_cta hb hg).2
  exact hP.noexit e.1 hcta (by rw [hmod]; exact hw) e.2 pc hget

/-- **A passed arrival's generation is released.** -/
theorem released_of_passed (hX : Consistent L K A mem0 X) {c n id : Nat} {count : Option Nat}
    {p : Finset Nat} (hP : Part L X c count id p) (hn : 0 < n)
    (hcount : target L.block count = .ok n) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < L.block / 32) (hid : id < 16) {f : EvId} {pc : Nat}
    (hf : X.IsBarrier f id count pc) (hfc : f.1 / L.block = c)
    (hpassed : f.2 + 1 < (X.tr f.1).length) :
    Released L.block (X.barriers c) id (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
  subst hfc
  have hge : f.1 < L.threads := by
    obtain ⟨key, hk, -⟩ := ctaBarDone_of_returned hX hf hpassed
    exact hk.1
  have hb : 0 < L.block := block_pos_of_thread_lt hge
  have hc : f.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hge
  have hproto := hP.protocol hX hc hb
  have hpre : PrefixFor L X count p id f := by
    intro index warp count lanes hr href
    refine ⟨fun r hr' => hproto r (List.mem_of_mem_take hr'), ?_⟩
    exact hproto _ (List.mem_of_getElem? hr) rfl
  have hk := passed_key hX hn hcount hf hpassed hpre hcard hbound
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have := CtaBarK.key_unique hX.ctaBar hkey hk
  subst this
  have h1 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id := by omega
  have h2 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by omega
  unfold CtaBarDone at hdone
  rw [h1, h2] at hdone
  exact hdone

/-- **A reached arrival of a released generation is recorded.** -/
theorem key_of_released (hX : Consistent L K A mem0 X) {c n id : Nat} {count : Option Nat}
    {p : Finset Nat} (hP : Part L X c count id p) (hn : 0 < n)
    (hcount : target L.block count = .ok n) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < L.block / 32) (hid : id < 16) {e : EvId} {pc : Nat}
    (he : X.IsBarrier e id count pc) (hec : e.1 / L.block = c) (hge : e.1 < L.threads)
    (hd : Released L.block (X.barriers c) id (((X.tr e.1).take e.2).countP (Execution.isBarId id)))
      :
    CtaBarK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  have hb : 0 < L.block := block_pos_of_thread_lt hge
  have hw := (hP.src e pc _ he hec).1
  subst hec
  have hc : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hge
  have hproto := hP.protocol hX hc hb
  exact reached_key_of_release hX hn hcount hid he hge hw rfl hd
    (fun i _ r hr => hproto r (List.mem_of_mem_take hr)) hcard hbound

/-- **Releasing a named barrier generation whose participants have all arrived.** In a maximal
execution, let every participant lane of CTA `c`, of the `n` participant warps `p` of named
resource `id` with thread-count operand `count`, have as its last event its arrival on `id` with
the same ordinal `G`. Then the
CTA's history, extended by arrival records of the participant warps that have none, is checked and
completes generation `G`: the extended execution is maximal, has the same traces and size, and every
participant lane's arrival is recorded in the completed generation. -/
theorem named_finish (hmax : Maximal L K A mem0 X) {c : Nat} (hc : c < L.grid) {n id : Nat}
    {count : Option Nat} {p : Finset Nat} (hn : 0 < n) (hcount : target L.block count = .ok n)
    (hid : id < 16) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < L.block / 32) (hP : Part L X c count id p) {G : Nat}
    (hlane : ∀ g, g < L.block → g / 32 ∈ p → ∃ pc,
      X.IsBarrier (c * L.block + g, (X.tr (c * L.block + g)).length - 1) id count pc ∧
      ((X.tr (c * L.block + g)).take ((X.tr (c * L.block + g)).length - 1)).countP
        (Execution.isBarId id) = G)
    (hasm : ∀ Y, ∀ a ∈ A, a.wf L mem0 Y) :
    ∃ Y, Maximal L K A mem0 Y ∧ X.le Y ∧ Y.size L = X.size L ∧ Y.tr = X.tr ∧
      CtaBarDone L Y c (id + 16 * G) ∧ ∀ g, g < L.block → g / 32 ∈ p →
        CtaBarK L Y (c * L.block + g, (X.tr (c * L.block + g)).length - 1) (id + 16 * G) := by
  have hX := hmax.1
  obtain ⟨w0, hw0⟩ : ∃ w, w ∈ p := Finset.card_pos.mp (by omega)
  have hb : 0 < L.block := by
    have := hbound w0 hw0
    omega
  have hmodid : (id + 16 * G) % 16 = id := by omega
  have hdivid : (id + 16 * G) / 16 = G := by omega
  have hdone_iff : ∀ Y : Execution, CtaBarDone L Y c (id + 16 * G) ↔
      Released L.block (Y.barriers c) id G := by
    intro Y
    unfold CtaBarDone
    rw [hmodid, hdivid]
  have hproto := hP.protocol hX hc hb
  -- the participant lane events
  have hev : ∀ g, g < L.block → g / 32 ∈ p →
      (c * L.block + g) < L.threads := fun g hg _ => cta_thread_lt hc hg
  by_cases hrel : Released L.block (X.barriers c) id G
  · refine ⟨X, hmax, Execution.le_refl X, rfl, rfl, (hdone_iff X).mpr hrel, fun g hg hgw => ?_⟩
    obtain ⟨pc, hbar, hord⟩ := hlane g hg hgw
    have hcta := (lane_cta (c := c) hb hg).1
    have := key_of_released hX hP hn hcount hcard hbound hid hbar (by simpa using hcta)
      (hev g hg hgw) (by simpa [hord] using hrel)
    simpa [hord] using this
  -- the final state of the history and its ledger
  obtain ⟨s, hs⟩ := (hX.ctaBar.2 c hc).2.2
  have hl := hproto.run_ledger hn hcount hcard hbound hs
  have hprot := run_protected (hP.exits hX hc hb) hs
  have hgs_le : (s.slots id).generation ≤ G := by
    by_contra hlt
    push Not at hlt
    exact hrel (Step.CtaBar.released_of_generation_lt hs hlt)
  have hgs_ge : G ≤ (s.slots id).generation := by
    rcases Nat.eq_zero_or_pos G with h0 | hpos
    · omega
    · have hw0b := hbound w0 hw0
      have hg0 : w0 * 32 < L.block := by omega
      obtain ⟨pc, hbar, hord⟩ := hlane (w0 * 32) hg0 (by simpa using hw0)
      set y := c * L.block + w0 * 32 with hy
      have hlen : 0 < (X.tr y).length := by
        have := len_of_get hbar
        simp only at this
        omega
      obtain ⟨j, e', hj, hq, hjr⟩ := exists_ordinal (Execution.isBarId id)
        ((X.tr y).take ((X.tr y).length - 1)) (r := G - 1) (by omega)
      have hjl : j < (X.tr y).length - 1 := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_take] at this
        omega
      rw [List.getElem?_take_of_lt hjl] at hj
      have htk : ((X.tr y).take ((X.tr y).length - 1)).take j = (X.tr y).take j := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [htk] at hjr
      obtain ⟨pc', cnt', rfl⟩ : ∃ pc cnt, e' = ⟨pc, .bar id cnt⟩ := by
        obtain ⟨pc', kd⟩ := e'
        cases kd <;> simp [Execution.isBarId] at hq
        rename_i id' cnt' m'
        cases m'
        · exact ⟨pc', cnt', by rw [hq]⟩
        · subst hq
          exact (hX.noBarArrive hK.out (y, j) _ _ _ hj).elim
      have hf : X.IsBarrier (y, j) id cnt' pc' := hj
      have hcta := (lane_cta (c := c) hb hg0).1
      have hcnt := (hP.src (y, j) pc' cnt' hf hcta).2
      subst cnt'
      have hrj := released_of_passed hX hP hn hcount hcard hbound hid hf hcta (by simp only; omega)
      simp only at hrj
      rw [hjr] at hrj
      have := released_generation_lt hs hrj
      omega
  have hgs : (s.slots id).generation = G := le_antisymm hgs_le hgs_ge
  -- the lane events of the participants that have not arrived are in no record
  have hnew : ∀ w ∈ p, w ∉ (s.slots id).arrived → ∀ g, g < L.block → g / 32 = w →
      (c * L.block + g, (X.tr (c * L.block + g)).length - 1) ∉
        (X.barriers c).flatMap Record.refs := by
    intro w hwp hwA g hg hgw hmem
    obtain ⟨pcg, hbarg, hordg⟩ := hlane g hg (hgw ▸ hwp)
    obtain ⟨r, hr, hgr⟩ := List.mem_flatMap.mp hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
    obtain ⟨si, ti, hat, hpf⟩ := run_at_record hlast hi
    have hsrc := (hX.ctaBar.2 c hc).2.1 r hr
    cases r with
    | exit g' e' =>
      obtain ⟨-, -, pc, hget⟩ := hsrc
      have he : (c * L.block + g, (X.tr (c * L.block + g)).length - 1) = e' := by
        simpa [Record.refs] using hgr
      rw [← he] at hget
      have h2 : X.get (c * L.block + g, (X.tr (c * L.block + g)).length - 1) =
          some ⟨pcg, .bar id count⟩ := hbarg
      rw [h2] at hget
      cases hget
    | arrival id' w' cnt' lanes =>
      obtain ⟨⟨g1, f1⟩, hm, hf1⟩ := List.mem_map.mp hgr
      obtain ⟨hg1, hfg1, pc1, hbar1⟩ := hsrc (g1, f1) hm
      replace hbar1 := hX.isBarrier_of_arrival hK.out hbar1
      have hf1e : f1 = (c * L.block + g, (X.tr (c * L.block + g)).length - 1) := hf1
      subst hf1e
      have hgg : g1 = g := by
        have : c * L.block + g = c * L.block + g1 := hfg1
        omega
      subst hgg
      have h2 : X.get (c * L.block + g1, (X.tr (c * L.block + g1)).length - 1) =
          some ⟨pcg, .bar id count⟩ := hbarg
      have h3 : X.get (c * L.block + g1, (X.tr (c * L.block + g1)).length - 1) =
          some ⟨pc1, .bar id' cnt'⟩ := hbar1
      rw [h2] at h3
      simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h3
      obtain ⟨-, rfl, -⟩ := h3
      have hwarp := ((perform_arrival_lanes hpf).2.1 (g1, _) hm).2.1
      simp only at hwarp
      have hwexit : g1 ∉ si.exited :=
        run_protected (fun g a ha => hP.exits hX hc hb g a (List.mem_of_mem_take ha)) hat g1 hg
          (hgw ▸ hwp)
      have hcount := cta_prefix_id_arrival_count hX (c := c) (i := i) (localg := g1) (id := id)
        hc hi hgr hat hg rfl hwexit rfl
      simp only at hcount
      rw [hordg] at hcount
      -- the record is the warp's arrival at generation `G`: the warp has `G + 1` arrivals
      have hge : G + 1 ≤ idArrivals (X.barriers c) id w := by
        have hr' : (X.barriers c)[i]? = some (Record.arrival id w' cnt' lanes) := hi
        have hsub : (X.barriers c).take (i + 1) =
            (X.barriers c).take i ++ [Record.arrival id w' cnt' lanes] := by
          rw [List.take_add_one, hr']
          rfl
        have hww : w' = w := by omega
        subst hww
        have h1 : idArrivals ((X.barriers c).take (i + 1)) id w' = G + 1 := by
          unfold idArrivals at hcount ⊢
          rw [hsub, List.countP_append, ← hgw, hcount]
          simp [isWarpIdArrival]
        have h2 := (List.take_sublist (i + 1) (X.barriers c)).countP_le
          (p := isWarpIdArrival id w')
        unfold idArrivals
        unfold idArrivals at h1
        omega
      have hbal := hl.balance w hwp (lane_live hbound hprot hwp)
      simp only [hwA, ↓reduceIte, Nat.add_zero] at hbal
      omega
  -- the missing participant warps arrive, completing the generation
  let event : Nat → EvId := fun g => (c * L.block + g, (X.tr (c * L.block + g)).length - 1)
  obtain ⟨ws, t, hnd, hws, hcov, hrun, hgen⟩ :=
    finish_named hid hn hcount hcard hbound event _ hl hprot rfl
  let suffix : List (Record EvId) :=
    ws.map (fun w => Record.arrival id w count (fullLanes L.block w event))
  have hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes := by
    intro r hr
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, _, _, _, rfl⟩
  have hinj : Function.Injective event := by
    intro g h hh
    have := congrArg Prod.fst hh
    simp only [event] at this
    omega
  have hhist : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)) := by
    constructor
    · intro d hd
      have hne : d ≠ c := by omega
      rw [withCtaHistory_barriers_ne X _ hne]
      exact hX.ctaBar.1 d hd
    · intro d hd
      by_cases hdc : d = c
      · subst hdc
        rw [withCtaHistory_barriers_self]
        refine ⟨?_, ?_, t, ?_⟩
        · rw [List.flatMap_append]
          refine List.nodup_append.mpr ⟨(hX.ctaBar.2 d hc).1, ?_, ?_⟩
          · have h := fullLanes_suffix_nodup (id := id) (block := L.block) (event := event) hnd hinj
            simpa [suffix, List.flatMap_map, Record.refs] using h
          · intro e he f hf hef
            subst hef
            obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.mp hf
            obtain ⟨w, hwws, rfl⟩ := List.mem_map.mp hr
            obtain ⟨g, hg, hgw, rfl⟩ := (mem_fullLanes_refs (id := id)).mp hfr
            have hw := hws w hwws
            exact hnew w hw.1 hw.2 g hg hgw he
        · intro r hr'
          rcases List.mem_append.mp hr' with hr | hr
          · exact (hX.ctaBar.2 d hc).2.1 r hr
          · obtain ⟨w, hwws, rfl⟩ := List.mem_map.mp hr
            intro q hq
            obtain ⟨hg, hw, heq⟩ := mem_fullLanes.mp hq
            obtain ⟨pc, hbar, -⟩ := hlane q.1 hg (hw ▸ (hws w hwws).1)
            refine ⟨hg, by rw [heq], pc, .sync, ?_⟩
            rw [heq]
            exact hbar
        · rw [run_append, hs]
          exact hrun
      · rw [withCtaHistory_barriers_ne X _ hdc]
        exact hX.ctaBar.2 d hd
  obtain ⟨hYc, hle, hsz, hmaxY⟩ := Step.CtaBar.release_append hmax hc hsuf hhist
    (fun a ha => hasm _ a ha)
  have hrec : Released L.block (X.barriers c ++ suffix) id G := by
    have := released_of_arrival_run_cnt (xs := X.barriers c) (ys := suffix) (s := s) (t := t)
      (id := id) (cnt := count) (fun r hr => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
        exact ⟨w, _, rfl⟩) hs hrun (by omega)
    rwa [hgs] at this
  have hYb : (X.withCtaHistory c (X.barriers c ++ suffix)).barriers c = X.barriers c ++ suffix :=
    withCtaHistory_barriers_self X c _
  refine ⟨_, hmaxY, hle, hsz, rfl, (hdone_iff _).mpr (by rw [hYb]; exact hrec), fun g hg hgw => ?_⟩
  obtain ⟨pc, hbar, hord⟩ := hlane g hg hgw
  have hcta := (lane_cta (c := c) hb hg).1
  have hPY : Part L (X.withCtaHistory c (X.barriers c ++ suffix)) c count id p := by
    refine ⟨hP.src, hP.noexit⟩
  have hd : Released L.block ((X.withCtaHistory c (X.barriers c ++ suffix)).barriers c) id
      (((X.tr (c * L.block + g)).take ((X.tr (c * L.block + g)).length - 1)).countP
        (Execution.isBarId id)) := by
    rw [hord, hYb]
    exact hrec
  have := key_of_released hYc hPY hn hcount hcard hbound hid (e := event g) hbar
    (by simpa [event] using hcta) (hev g hg hgw) hd
  change CtaBarK L _ (c * L.block + g, (X.tr (c * L.block + g)).length - 1)
    (id + 16 * (((X.tr (c * L.block + g)).take ((X.tr (c * L.block + g)).length - 1)).countP
      (Execution.isBarId id))) at this
  rw [hord] at this
  exact this

omit hK in
/-- **The participants of a barrier in a CTA**, from the sources of its arrivals and the absence
of participant exits. -/
theorem Sources.part (hX : Consistent L K A mem0 X) {c id : Nat} {count : Option Nat}
    {p : Finset Nat} (hS : Sources L X count p id)
    (hno : ∀ y, y / L.block = c → (y % L.block) / 32 ∈ p → ∀ j pc,
      X.get (y, j) ≠ some ⟨pc, .exit⟩) : Part L X c count id p := by
  refine ⟨fun e pc cnt he _ => hS.sync he ?_, hno⟩
  have hlt : e.2 < (X.tr e.1).length := (List.getElem?_eq_some_iff.mp he).1
  by_contra hn
  rw [hX.outside e.1 (by omega)] at hlt
  simp at hlt

omit hK in
/-- **The warp needs of a recorded barrier arrival are filled.** Each lane of the warp of an
arrival `e` of generation `gen` has its arrival in the record of `e`, or, when it had exited
before the record, its exit recorded before it: an arrival record holds every live lane of its
warp. -/
theorem warpNeeds_filled {Y : Execution} (hh : CtaBarHistoryOk L Y) {e : EvId} {id gen : Nat}
    (hlt : e.1 < L.threads)
    (hg : CtaBarrier.GenerationOf L.block (Y.barriers (e.1 / L.block)) e id gen) :
    ∀ n ∈ ctaBarWarpNeeds L Y e, match n with
      | .node fills => ∃ x, Y.RefPresent x ∧ fills x
      | .cond holds => holds := by
  have hb : 0 < L.block := block_pos_of_thread_lt hlt
  have hc : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hlt
  have hsrcs := (hh.2 _ hc).2.1
  -- a record reference is a present event
  have hpres : ∀ r ∈ Y.barriers (e.1 / L.block), ∀ y ∈ r.refs, Y.RefPresent (.thread y) := by
    intro r hr y hy
    have hsrc := hsrcs r hr
    cases r with
    | exit g a =>
      obtain ⟨-, -, pc', hget⟩ := hsrc
      simp only [Record.refs, List.mem_singleton] at hy
      subst hy
      exact ⟨_, hget⟩
    | arrival id' w' cnt' lanes =>
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      obtain ⟨-, -, pc', m', hget⟩ := hsrc q hq
      exact ⟨_, hget⟩
  intro n hw
  obtain ⟨h, hhm, rfl⟩ := List.mem_map.mp hw
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hhm
  have hl := List.mem_range.mp hl
  obtain ⟨i, s, w, count, lanes, g0, hi, hat, hmem, -, t, hperf⟩ := hg
  have hr := List.mem_of_getElem? hi
  obtain ⟨hg0, he1, -⟩ := hsrcs _ hr (g0, e) hmem
  simp only at hg0 he1
  have hlanes := perform_arrival_lanes hperf
  have hw0 : g0 / 32 = w := (hlanes.2.1 (g0, e) hmem).2.1
  have hmod : e.1 % L.block = g0 := by rw [he1]; exact (lane_cta hb hg0).2
  have hws : warpSize L e.1 = min 32 (L.block - g0 / 32 * 32) := by
    simp only [warpSize, hmod]
  have hlane : warpLane L e.1 l = e.1 / L.block * L.block + (w * 32 + l) := by
    simp only [warpLane, laneOf, hmod]
    have := Nat.mod_add_div g0 32
    omega
  have hgl : w * 32 + l < L.block := by
    rw [hws] at hl
    have := Nat.mod_add_div g0 32
    omega
  have hgw : (w * 32 + l) / 32 = w := by omega
  have heref : e ∈ (Record.arrival id w count lanes).refs :=
    List.mem_map.mpr ⟨(g0, e), hmem, rfl⟩
  by_cases hx : w * 32 + l ∈ s.exited
  · -- the lane had exited: its exit is recorded before the record
    obtain ⟨a, ha⟩ := run_exited_mem hat hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
    have hjl : j < i := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hjl] at hj
    obtain ⟨-, ha1, -⟩ := hsrcs _ (List.mem_of_getElem? hj)
    refine ⟨.thread a, hpres _ (List.mem_of_getElem? hj) a (by simp [Record.refs]), i, _, a,
      hi, heref, rfl, ?_, .inr ⟨j, _, hjl, hj⟩⟩
    rw [hlane, ha1]
  · -- the lane is live: it is a lane of the record
    obtain ⟨q, hq, hq1⟩ := List.mem_map.mp (hlanes.2.2 _ hgl hgw hx)
    obtain ⟨-, hq2, -⟩ := hsrcs _ hr q hq
    have hqref : q.2 ∈ (Record.arrival id w count lanes).refs :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    refine ⟨.thread q.2, hpres _ hr _ hqref, i, _, q.2, hi, heref, rfl, ?_, .inl hqref⟩
    rw [hlane, hq2, hq1]

omit hK in
/-- **A recorded `bar.sync` of a released generation is ready.** Each lane of its warp has its
arrival in the record, or, when it had exited before the record, its exit recorded before it (an
arrival record holds every live lane of its warp); the generation is released; and every counted
record reference is a present event. -/
theorem ready_of_released {Y : Execution} (hh : CtaBarHistoryOk L Y) {e : EvId} {pc id : Nat}
    {cnt : Option Nat} {key : Nat} (he : Y.get e = some ⟨pc, .bar id cnt .sync⟩)
    (hk : CtaBarK L Y e key) (hd : CtaBarDone L Y (e.1 / L.block) key) : Ready L Y e := by
  have hb : 0 < L.block := block_pos_of_thread_lt hk.1
  have hc : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hk.1
  have hsrcs := (hh.2 _ hc).2.1
  -- a record reference is a present event
  have hpres : ∀ r ∈ Y.barriers (e.1 / L.block), ∀ y ∈ r.refs, Y.RefPresent (.thread y) := by
    intro r hr y hy
    have hsrc := hsrcs r hr
    cases r with
    | exit g a =>
      obtain ⟨-, -, pc', hget⟩ := hsrc
      simp only [Record.refs, List.mem_singleton] at hy
      subst hy
      exact ⟨_, hget⟩
    | arrival id' w' cnt' lanes =>
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      obtain ⟨-, -, pc', m', hget⟩ := hsrc q hq
      exact ⟨_, hget⟩
  intro n hn
  simp only [Needs, he, KindNeeds, ctaBarNeeds, List.mem_append, List.mem_cons] at hn
  rcases hn with hw | rfl | hcount
  · exact warpNeeds_filled hh hk.1 hk.2.2 _ hw
  · exact ⟨key, hk, hd⟩
  · -- a counted reference is a present record reference
    obtain ⟨y, hy, hcy⟩ := List.mem_flatMap.mp hcount
    obtain ⟨r, hr, hyr⟩ := List.mem_flatMap.mp hy
    unfold needsIf at hcy
    split_ifs at hcy
    · cases List.mem_singleton.mp hcy
      exact ⟨_, hpres r hr y hyr, rfl⟩
    · cases hcy

omit hK in
/-- **A recorded `bar.arrive` is ready**: its needs are the warp needs. -/
theorem ready_of_arrivalK {Y : Execution} (hh : CtaBarHistoryOk L Y) {e : EvId} {pc id : Nat}
    {cnt : Option Nat} {key : Nat} (he : Y.get e = some ⟨pc, .bar id cnt .arrive⟩)
    (hk : CtaBarArrivalK L Y e key) : Ready L Y e := by
  intro n hn
  simp only [Needs, he, KindNeeds, ctaBarNeeds, List.append_nil] at hn
  exact warpNeeds_filled hh hk.1 hk.2.2 _ hn

omit hK in
/-- A thread whose last event is a recorded named barrier arrival of a released generation is
released. -/
theorem released_of_key {Y : Execution} (hh : CtaBarHistoryOk L Y) (htr : Y.tr = X.tr)
    {g pc id : Nat} {cnt : Option Nat} {key : Nat}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .sync⟩)
    (hk : CtaBarK L Y (g, (X.tr g).length - 1) key) (hd : CtaBarDone L Y (g / L.block) key) :
    Step.Released L Y g := by
  have hlastY : Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bar id cnt .sync⟩ := by
    simpa [Execution.get, htr] using hlast
  refine ⟨fun pc' k hget _ => ?_⟩
  have hkY : CtaBarK L Y (g, (Y.tr g).length - 1) key := by simpa [htr] using hk
  exact ready_of_released hh hlastY hkY hd

/-- **A blocked arrival has a lagging participant or can be released.** In a maximal execution of
a kernel without `bar.arrive`, let thread `g`'s last event be its arrival on named barrier `id`,
not released, with the participants `p` of its CTA (`Part`). Either a participant lane of the CTA
has made fewer arrivals on `id` than `g`, or every participant lane has an arrival of `g`'s
ordinal and, none of them passed, appending the records the CTA's history lacks gives a maximal
execution with the same traces in which `g` is released. -/
theorem wait_cases (hmax : Maximal L K A mem0 X) (hasm : ∀ Y, ∀ a ∈ A, a.wf L mem0 Y)
    {count : Option Nat} {p : Finset Nat} {id : Nat} (hG : Shape L count p id) {g pc : Nat}
    (hg : g < L.threads) (hP : Part L X (g / L.block) count id p)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hnr : ¬ Step.Released L X g) :
    (∃ h, h < L.threads ∧ h / L.block = g / L.block ∧ (h % L.block) / 32 ∈ p ∧
      (X.tr h).countP (Execution.isBarId id) < (X.tr g).countP (Execution.isBarId id)) ∨
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g := by
  have hX := hmax.1
  have hb : 0 < L.block := block_pos_of_thread_lt hg
  have hcta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  have hid := hG.id_lt
  have hlast' : (X.tr g)[(X.tr g).length - 1]? = some ⟨pc, .bar id count .sync⟩ := hlast
  have hNg := countP_last (id := id) hlast' (by simp [Execution.isBarId])
  set G := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) with hGdef
  by_cases hlag : ∃ h, h < L.threads ∧ h / L.block = g / L.block ∧ (h % L.block) / 32 ∈ p ∧
      (X.tr h).countP (Execution.isBarId id) < (X.tr g).countP (Execution.isBarId id)
  · exact .inl hlag
  right
  push Not at hlag
  -- every participant has an arrival of ordinal `G`
  have hlane : ∀ y, y / L.block = g / L.block → (y % L.block) / 32 ∈ p → y < L.threads →
      ∃ j pc', X.IsBarrier (y, j) id count pc' ∧
        ((X.tr y).take j).countP (Execution.isBarId id) = G := by
    intro y hyc hyw hy
    have hle := hlag y hy hyc hyw
    obtain ⟨j, e', hj, hq, hjr⟩ := exists_ordinal (Execution.isBarId id) (X.tr y) (r := G)
      (by omega)
    obtain ⟨pc', cnt', m', rfl⟩ := isBarId_form hq
    cases m'
    case arrive => exact (hX.noBarArrive hK.out (y, j) _ _ _ hj).elim
    have hcnt := (hP.src (y, j) pc' cnt' hj hyc).2
    subst hcnt
    exact ⟨j, pc', hj, hjr⟩
  by_cases hpass : ∃ y j pc', y / L.block = g / L.block ∧ (y % L.block) / 32 ∈ p ∧
      y < L.threads ∧ X.IsBarrier (y, j) id count pc' ∧
      ((X.tr y).take j).countP (Execution.isBarId id) = G ∧ j + 1 < (X.tr y).length
  · -- a participant has passed the generation: it is released, and so is the thread's arrival
    exfalso
    obtain ⟨y, j, pc', hyc, hyw, hy, hbar, hord, hpassed⟩ := hpass
    have hrel := released_of_passed hX hP hG.pos hG.target rfl hG.bound hid hbar hyc hpassed
    simp only at hrel
    rw [hord] at hrel
    have hkey := key_of_released hX hP hG.pos hG.target rfl hG.bound hid hlast rfl hg
      (by simp only; rw [← hGdef]; exact hrel)
    simp only at hkey
    rw [← hGdef] at hkey
    refine hnr (released_of_key hX.ctaBar rfl hlast hkey ?_)
    unfold CtaBarDone
    have h1 : (id + 16 * G) % 16 = id := by omega
    have h2 : (id + 16 * G) / 16 = G := by omega
    rw [h1, h2]
    exact hrel
  push Not at hpass
  -- every participant's arrival of ordinal `G` is the last event of its thread
  have hlanes : ∀ g', g' < L.block → g' / 32 ∈ p → ∃ pc',
      X.IsBarrier (g / L.block * L.block + g',
        (X.tr (g / L.block * L.block + g')).length - 1) id count pc' ∧
      ((X.tr (g / L.block * L.block + g')).take
        ((X.tr (g / L.block * L.block + g')).length - 1)).countP (Execution.isBarId id) = G := by
    intro g' hg' hw
    obtain ⟨hyc, hym⟩ := lane_cta (c := g / L.block) hb hg'
    have hy : g / L.block * L.block + g' < L.threads := cta_thread_lt hcta hg'
    obtain ⟨j, pc', hbar, hord⟩ := hlane _ hyc (by rw [hym]; exact hw) hy
    have hnp := hpass _ j pc' hyc (by rw [hym]; exact hw) hy hbar hord
    have hjl : j < (X.tr (g / L.block * L.block + g')).length :=
      (List.getElem?_eq_some_iff.mp hbar).1
    have hj : j = (X.tr (g / L.block * L.block + g')).length - 1 := by omega
    subst hj
    exact ⟨pc', hbar, hord⟩
  obtain ⟨Y, hmaxY, -, -, hYtr, hdone, hkeys⟩ := named_finish hmax hcta hG.pos hG.target hid rfl
    hG.bound hP hlanes hasm
  have hgl : g / L.block * L.block + g % L.block = g := Nat.div_add_mod' g L.block
  have hwg : (g % L.block) / 32 ∈ p := (hP.src _ pc count hlast rfl).1
  have hkey := hkeys (g % L.block) (Nat.mod_lt _ hb) hwg
  rw [hgl] at hkey
  exact ⟨Y, hmaxY, hYtr, released_of_key hmaxY.1.ctaBar hYtr hlast hkey hdone⟩

end PTX.NamedBar
