-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarSources
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # Named barriers with `bar.arrive` participants

The library's named-barrier lemmas (`NamedBarLedger`, `NamedBarSync`, `NamedBarSources`) assume a
kernel without `bar.arrive` (`Kernel.NoBarArrive`). This file gives the lemmas a group with
arrive-only participants needs, for a barrier whose arrivals follow its group (`Sources`, `Shape`)
and with no assumption on the forms the participants use.

* The generation of every recorded arrival, of either form, is its source ordinal
  (`Sources.arrival_key`); a passed `bar.sync` therefore releases the generation of its ordinal
  (`Sources.sync_released`).
* An arrival whose ordinal's generation is released is recorded in that generation
  (`Sources.key_of_released`): a lane that exits before the release has its `bar.arrive` recorded
  before its exit (`ArriveRecorded`), and a live lane has a record by the release.
* With a passed `bar.sync` partner of the same ordinal, an arrive-only participant's arrival is
  in the generation of its ordinal (`Sources.arrive_key_of_credit`), its generation is done before
  its next arrival (`Sources.arrive_done_of_partner`), and what it did before its arrival happens
  before what the partner does after its `bar.sync` (`Sources.arrive_sync_baseCausality`, Core
  `CtaBarSync` with a `bar.arrive` source).
* No arrival faults (`no_duplicate_arrival`): the counts of one CTA's arrivals on one barrier agree,
  and the generation of every `bar.arrive` is done before its thread arrives on that barrier again.
  The second premise is the credit chain of a kernel; `arrive_done_of_partner` discharges it from a
  passed partner of the same ordinal.

Not here: completing a generation whose arrive-only participants have moved on (a progress step
in the style of `Step.CtaBarNamed.finish_named`). -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

/-! ## Ordinals of barrier events -/

section
variable {X : Execution}

/-- Two events of one thread on barrier `id` with the same ordinal are the same event. -/
theorem ordinal_unique {g i j id : Nat} {ev ev' : Event} (hi : (X.tr g)[i]? = some ev)
    (hj : (X.tr g)[j]? = some ev') (hb : Execution.isBarId id ev = true)
    (hb' : Execution.isBarId id ev' = true)
    (hord : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr g).take j).countP (Execution.isBarId id)) : i = j := by
  have step : ∀ {a b : Nat} {e : Event}, (X.tr g)[a]? = some e →
      Execution.isBarId id e = true → a < b →
      ((X.tr g).take a).countP (Execution.isBarId id) <
        ((X.tr g).take b).countP (Execution.isBarId id) := by
    intro a b e ha hba hab
    have hs : ((X.tr g).take (a + 1)).countP (Execution.isBarId id) =
        ((X.tr g).take a).countP (Execution.isBarId id) + 1 := by
      rw [List.take_add_one, ha]
      simp [hba]
    have hm := (List.take_sublist_take_left (l := X.tr g) (by omega : a + 1 ≤ b)).countP_le
      (p := Execution.isBarId id)
    omega
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := step hi hb h
    omega
  · exact h
  · have := step hj hb' h
    omega

end

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- A recorded arrival has a key of its barrier. -/
theorem recorded_arrivalK (hX : Consistent L K A mem0 X) {e : EvId} {id pc : Nat}
    {cnt : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩)
    (hg : e.1 < L.threads) (hrec : e ∈ (X.barriers (e.1 / L.block)).flatMap Record.refs) :
    ∃ gen, CtaBarArrivalK L X e (id + 16 * gen) := by
  obtain ⟨r, hr, href⟩ := List.mem_flatMap.mp hrec
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  have hc := cta_lt hg
  obtain ⟨last, hlast⟩ := (hX.ctaBar.2 _ hc).2.2
  obtain ⟨s, t, hs, ht⟩ := run_at_record hlast hk
  cases r with
  | exit x y =>
    exfalso
    have hy : y = e := by simpa only [Record.refs, List.mem_singleton, eq_comm] using href
    obtain ⟨-, -, pc', hget⟩ := (hX.ctaBar.2 _ hc).2.1 _ hr
    rw [hy, he] at hget
    cases hget
  | arrival id' w cnt' lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp href
    obtain ⟨-, -, pcq, mq, hqbar⟩ := ((hX.ctaBar.2 _ hc).2.1 _ hr) q hq
    rw [hqe, he] at hqbar
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hqbar
    obtain ⟨-, hid', -, -⟩ := hqbar
    subst id'
    have hid : id < 16 := hX.ctaBar.arrival_id_lt hk
    have hqm : (q.1, e) ∈ lanes := by
      have : (q.1, e) = q := by rw [← hqe]
      rw [this]
      exact hq
    exact ⟨(s.slots id).generation, CtaBarArrivalK.of_generation hX.ctaBar hg hid
      ⟨k, s, w, cnt', lanes, q.1, hk, hs, hqm, rfl, t, ht⟩⟩

variable {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- **The generation of a recorded arrival is its source ordinal**, for either form. -/
theorem Sources.arrival_key (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {e : EvId} {pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) {key : Nat} (hk : CtaBarArrivalK L X e key) :
    key = id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id) := by
  have hid : key % 16 = id := by
    obtain ⟨count', pc', mode', he'⟩ := hk.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans he))).2).1
  have hg := hk.1
  have hc := cta_lt hg
  have hgen := hk.2.2
  rw [hid] at hgen
  obtain ⟨index, s, warp, cnt', lanes, g, hr, hs, hm, hphase, t, ht⟩ := hgen
  have href : e ∈ (Record.arrival id warp cnt' lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩
  obtain ⟨hprot, hw, hcnt⟩ := hS.prefixFor hX hg index warp cnt' lanes hr href
  subst cnt'
  have hgen := generation_at_record hprot hG.pos hG.target rfl hG.bound hw hs ht
  obtain ⟨hgl, hthread, -⟩ := ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hr)) (g, e) hm
  have hlane := (perform_arrival_lanes ht).2.1 (g, e) hm
  have hocc := cta_prefix_id_arrival_count (id := id) hX hc hr href hs hgl hthread hlane.2.2 rfl
  simp only at hlane
  rw [hlane.2.1] at hocc
  omega

/-- **A passed `bar.sync` releases the generation of its ordinal.** -/
theorem Sources.sync_released (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc) (hpassed : f.2 + 1 < (X.tr f.1).length) :
    Released L.block (X.barriers (f.1 / L.block)) id
      (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hk := hS.arrival_key hX hG hf (CtaBarK.arrival hkey)
  subst hk
  have := hG.id_lt
  unfold CtaBarDone at hdone
  rwa [show (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id by omega,
    show (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) by omega] at hdone

/-- A thread that exits before a generation is released has every barrier operation recorded
before its exit: its arrival `e` is recorded. -/
private theorem recorded_of_exited (hX : Consistent L K A mem0 X) {e : EvId} {pc index : Nat}
    {cnt : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩)
    (hg : e.1 < L.threads) {t0 : State}
    (hrun : run L.block {} ((X.barriers (e.1 / L.block)).take (index + 1)) = .ok t0)
    (hx : e.1 % L.block ∈ t0.exited) :
    e ∈ (X.barriers (e.1 / L.block)).flatMap Record.refs := by
  have hc := cta_lt hg
  obtain ⟨a, ha⟩ := run_exited_mem hrun hx
  have hmem := List.mem_of_mem_take ha
  obtain ⟨-, ha1, pcx, hget⟩ := (hX.ctaBar.2 _ hc).2.1 _ hmem
  have hae : a.1 = e.1 := by rw [ha1, Nat.mul_comm]; exact Nat.div_add_mod e.1 L.block
  have hlast := Execution.exit_last hX (hae ▸ hg) (show X.get (a.1, a.2) = _ from hget)
  have hel := len_of_get he
  have hne : e.2 ≠ a.2 := by
    intro h
    have h2 : X.get a = X.get e := by rw [show a = e from Prod.ext hae h.symm]
    rw [hget, he] at h2
    cases h2
  have hlen : a.2 + 1 = (X.tr e.1).length := by rw [← hae]; exact hlast
  have hlt : e.2 < a.2 := by omega
  have haref : a ∈ (X.barriers (e.1 / L.block)).flatMap Record.refs :=
    List.mem_flatMap.mpr ⟨_, hmem, by simp [Record.refs]⟩
  by_contra hrec
  cases m with
  | sync => exact barrier_unrecorded_last hX he hrec (by omega)
  | arrive => exact hrec ((ArriveRecorded.of_consistent hX) e id cnt pc he (by omega))

/-- **An arrival of a released generation is recorded in it.** An arrival of either form whose
ordinal's generation is released has that generation's key; the arriving thread need not have
passed it, and may have exited since. -/
theorem Sources.key_of_released (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {e : EvId} {pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) (hg : e.1 < L.threads)
    (hd : Released L.block (X.barriers (e.1 / L.block)) id
      (((X.tr e.1).take e.2).countP (Execution.isBarId id))) :
    CtaBarArrivalK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  have hc := cta_lt hg
  set c := e.1 / L.block with hcdef
  by_cases hrec : e ∈ (X.barriers c).flatMap Record.refs
  · obtain ⟨gen, hk⟩ := recorded_arrivalK hX he hg hrec
    rwa [hS.arrival_key hX hG he hk] at hk
  exfalso
  have hb := block_pos_of_thread_lt hg
  set l := e.1 % L.block with hldef
  have hl : l < L.block := Nat.mod_lt _ hb
  have hthr : c * L.block + l = e.1 := by rw [Nat.mul_comm]; exact Nat.div_add_mod e.1 L.block
  obtain ⟨index, r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩ := hd
  have hrun : run L.block {} ((X.barriers c).take (index + 1)) = .ok t0 := by
    rw [List.take_add_one, hr0, run_append, hs0]
    simp [run, ht0, Except.bind]
  have hw : l / 32 ∈ p := (hS e pc cnt ⟨m, he⟩ hg).1
  by_cases hx : l ∈ t0.exited
  · exact hrec (recorded_of_exited hX he hg hrun hx)
  obtain ⟨i, lanes, e', hrec', hm, hgen⟩ := completed_participant_record
    (phase := ((X.tr e.1).take e.2).countP (Execution.isBarId id))
    (hS.completed hX hc (index + 1)) hG.pos hG.target rfl hG.bound hrun
    (by rw [hafter]; omega) hl hw hx
  have hi : i < index + 1 := by
    have hh := (List.getElem?_eq_some_iff.mp hrec').1
    simp only [List.length_take] at hh
    omega
  have hreal : (X.barriers c)[i]? = some (.arrival id (l / 32) count lanes) := by
    simpa only [List.getElem?_take, ite_eq_left hi] using hrec'
  obtain ⟨-, he1', pc', m', he'⟩ :=
    ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hreal)) (l, e') hm
  simp only at he1'
  have hee : e'.1 = e.1 := he1'.trans hthr
  have hgenFull : GenerationOf L.block (X.barriers c) e' id
      (((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
    have hh := hgen.append (ys := (X.barriers c).drop (index + 1))
    simpa only [List.take_append_drop] using hh
  have hk' : CtaBarArrivalK L X e' (id + 16 * ((X.tr e.1).take e.2).countP
      (Execution.isBarId id)) := by
    apply CtaBarArrivalK.of_generation hX.ctaBar (hee ▸ hg) hG.id_lt
    rw [hee]
    exact hgenFull
  have hkey := hS.arrival_key hX hG he' hk'
  rw [hee] at hkey
  have hidx := ordinal_unique (X := X) (g := e.1) (id := id) (ev := ⟨pc, .bar id cnt m⟩)
    (ev' := ⟨pc', .bar id count m'⟩) he (by rw [← hee]; exact he')
    (by simp [Execution.isBarId]) (by simp [Execution.isBarId]) (by omega)
  have hef : e' = e := Prod.ext hee hidx.symm
  exact hrec (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hreal,
    List.mem_map.mpr ⟨(l, e'), hm, by rw [hef]⟩⟩)

/-- **A credited `bar.arrive` is in the generation of its ordinal.** If a `bar.sync` participant
of the same CTA passed its arrival of the same ordinal (the kernel's credit chain: the partner's
credit arrival follows its pass), the arrival has the key of its ordinal. -/
theorem Sources.arrive_key_of_credit (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id) {e f : EvId} {pc pc' : Nat}
    {cnt cnt' : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩)
    (hg : e.1 < L.threads) (hcta : f.1 / L.block = e.1 / L.block)
    (hf : X.IsBarrier f id cnt' pc') (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hordinal : ((X.tr f.1).take f.2).countP (Execution.isBarId id) =
      ((X.tr e.1).take e.2).countP (Execution.isBarId id)) :
    CtaBarArrivalK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  have hd := hS.sync_released hX hG hf hpassed
  rw [hcta, hordinal] at hd
  exact hS.key_of_released hX hG he hg hd

/-- **A credited `bar.arrive`'s generation is done**: the premise of `no_duplicate_arrival` for a
barrier whose arrive-only participants are credited by a passed `bar.sync` partner. -/
theorem Sources.arrive_done_of_partner (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id) {e f : EvId} {key pc pc' : Nat}
    {cnt cnt' : Option Nat} {m : BarMode} (hk : CtaBarArrivalK L X e key)
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) (hcta : f.1 / L.block = e.1 / L.block)
    (hf : X.IsBarrier f id cnt' pc') (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hordinal : ((X.tr f.1).take f.2).countP (Execution.isBarId id) =
      ((X.tr e.1).take e.2).countP (Execution.isBarId id)) :
    CtaBarDone L X (e.1 / L.block) key := by
  have hkey := hS.arrival_key hX hG he hk
  subst hkey
  have hd := hS.sync_released hX hG hf hpassed
  rw [hcta, hordinal] at hd
  have := hG.id_lt
  unfold CtaBarDone
  rwa [show (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) % 16 = id by omega,
    show (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) by omega]

/-- **`bar.arrive` → `bar.sync` synchronization.** An arrival of either form of one thread and a
passed `bar.sync` of another thread of the same CTA, with the same ordinal: what the first did
before its arrival happens before what the second does after its `bar.sync`. -/
theorem Sources.arrive_sync_baseCausality (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id)
    (hG : Shape L count p id) {g h i j before after pc pc' : Nat} {cnt cnt' : Option Nat}
    {m : BarMode} (hsame : SameCta L g h) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩)
    (hf : X.IsBarrier (h, j) id cnt' pc') (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  have hke := hS.arrive_key_of_credit hX hG he hsame.1 hsame.2.2.symm hf hpassed
    hordinal.symm
  obtain ⟨key, hkf, -⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  rw [hkey, ← hordinal] at hkf
  exact Relation.TransGen.single (Or.inr (Or.inl ⟨hsame, _, i, j, hke, hkf, hbefore, hafter, hlen⟩))

/-- Program-order edges around an arriving lane and a returned waiting lane induce a causal
edge when they meet in the same generation. The two records are identified by their event kinds. -/
theorem Sources.arrive_sync_kind_baseCausality (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id)
    {g h i j before after : Nat} {cnt cnt' : Option Nat} {mode : BarMode}
    (hsame : SameCta L g h)
    (he : ∃ e, X.get (g, i) = some e ∧ e.kind = .bar id cnt mode)
    (hf : ∃ e, X.get (h, j) = some e ∧ e.kind = .bar id cnt' .sync)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := he
  obtain ⟨⟨pc', kind'⟩, hf, hk'⟩ := hf
  change kind = _ at hk
  change kind' = _ at hk'
  subst kind kind'
  exact hS.arrive_sync_baseCausality hX hG hsame he hf (by omega) hordinal hbefore hafter hlen

/-- A recorded arrival's key is the ordinal of its kind in the issuing lane. -/
theorem Sources.arrival_kind_key (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id) (hG : Shape L count p id)
    {i : EvId} {key : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : ∃ e, X.get i = some e ∧ e.kind = .bar id cnt mode)
    (hk : CtaBarArrivalK L X i key) :
    key = id + 16 * ((X.tr i.1).take i.2).countP (Execution.isBarId id) := by
  obtain ⟨⟨pc, kind⟩, hi, he⟩ := he
  change kind = _ at he
  subst kind
  exact hS.arrival_key hX hG hi hk

/-- **No CTA barrier arrival faults** when the counts of one CTA's arrivals on one barrier agree
(`hcount`, either form) and the generation of every recorded `bar.arrive` is done before its thread
arrives on that barrier again (`hdone`). A pending arrival is then neither a `countMismatch` nor a
`duplicateArrival`: a recorded arrival of its warp in the open generation is an earlier one of the
same lane; a `bar.sync` one was passed, so its generation is released, and a `bar.arrive` one's
generation is done by `hdone`. -/
theorem no_duplicate_arrival (hX : Consistent L K A mem0 X)
    (hcount : ∀ e f id cnt cnt' pc pc' m m', e.1 / L.block = f.1 / L.block →
      X.get e = some ⟨pc, .bar id cnt m⟩ → X.get f = some ⟨pc', .bar id cnt' m'⟩ → cnt = cnt')
    (hdone : ∀ e key pc cnt j ev, CtaBarArrivalK L X e key →
      X.get e = some ⟨pc, .bar (key % 16) cnt .arrive⟩ → e.2 < j → X.get (e.1, j) = some ev →
      Execution.isBarId (key % 16) ev = true → CtaBarDone L X (e.1 / L.block) key) :
    ¬ CtaBarFault L X := by
  rintro ⟨c, hc, s, hrun, id, warp, count, lanes, err, hsrc, hfree, hp, hfault⟩
  obtain ⟨hnd, hsrcs, -⟩ := hX.ctaBar.2 c hc
  have hslot := (slotFrom_run hrun) id
  simp only [Record.perform] at hp
  split_ifs at hp with hl
  · obtain ⟨hlive, n, hn, hcase⟩ := arrive_error_cases hp hfault
    obtain ⟨lane, hlr, hgb, hgx⟩ := hlive
    have hlt := Finset.mem_range.mp hlr
    obtain ⟨⟨g, e⟩, hm, hge⟩ := List.mem_map.mp (hl.2.2 lane hlr hgb hgx)
    simp only at hge
    subst hge
    obtain ⟨-, he1, pc, mode, hb⟩ := hsrc _ hm
    simp only at he1 hb
    have hdiv : e.1 / L.block = c := by rw [he1]; exact lane_div hgb
    rcases hcase with hdup | ⟨k, hk, hkn⟩
    · obtain ⟨i, u, cnt', lanes', t, hi, ha, hgen, hp'⟩ := hslot.1 warp hdup
      have hxu : warp * 32 + lane ∉ u.exited := fun hx => hgx (at_exited_mono ha hrun hx)
      obtain ⟨⟨_, e'⟩, hm', hge'⟩ := List.mem_map.mp
        (perform_arrival_lane hp' hgb (by omega) hxu)
      simp only at hge'
      subst hge'
      obtain ⟨-, he1', pc', mode', hb'⟩ := hsrcs _ (List.mem_of_getElem? hi) (_, e') hm'
      simp only at he1' hb'
      have hrec' : e' ∈ (X.barriers c).flatMap Record.refs :=
        List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(_, e'), hm', rfl⟩⟩
      have hne : e ≠ e' := fun h => hfree _ hm (h ▸ hrec')
      have hsame : e.1 = e'.1 := he1.trans he1'.symm
      have hel := len_of_get hb
      have hel' := len_of_get hb'
      have hlt' : e'.2 < e.2 := by
        by_contra hge
        have hne2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext hsame h2)
        rw [← hsame] at hel'
        cases mode with
        | sync =>
          exact barrier_unrecorded_last hX hb (by rw [hdiv]; exact hfree _ hm) (by omega)
        | arrive =>
          exact hfree _ hm (by
            rw [← hdiv]
            exact (ArriveRecorded.of_consistent hX) e id count pc hb (by omega))
      have hge' : e'.1 < L.threads := by rw [he1']; exact cta_thread_lt hc hgb
      have hdiv' : e'.1 / L.block = c := by rw [← hsame]; exact hdiv
      have hgo := generationOf_of_record (L := L) hi ha hp' hm'
      have hid : id < 16 := hX.ctaBar.arrival_id_lt hi
      have hrel : Released L.block (X.barriers c) id (u.slots id).generation := by
        cases mode' with
        | sync =>
          have hpass : e'.2 + 1 < (X.tr e'.1).length := by rw [← hsame]; omega
          obtain ⟨key, hk, hdone'⟩ := ctaBarDone_of_returned hX hb' hpass
          have hgk := hk.2.2
          rw [hdiv'] at hgk
          obtain ⟨hid', hph⟩ := GenerationOf.unique hnd hgk hgo
          unfold CtaBarDone at hdone'
          rwa [hdiv', hid', hph] at hdone'
        | arrive =>
          have hk' : CtaBarArrivalK L X e' (id + 16 * (u.slots id).generation) := by
            apply CtaBarArrivalK.of_generation hX.ctaBar hge' hid
            rw [hdiv']
            exact hgo
          have hmod : (id + 16 * (u.slots id).generation) % 16 = id := by omega
          have hdv : (id + 16 * (u.slots id).generation) / 16 = (u.slots id).generation := by
            omega
          have hd := hdone e' _ pc' cnt' e.2 _ hk' (by rw [hmod]; exact hb') hlt'
            (by rw [← hsame]; exact hb) (by simp [hmod, Execution.isBarId])
          unfold CtaBarDone at hd
          rwa [hdiv', hmod, hdv] at hd
      have := released_generation_lt hrun hrel
      omega
    · obtain ⟨i, u, w2, cnt2, lanes2, t, hi, ha, hgen, htg, hp2⟩ := hslot.2 k hk
      obtain ⟨g2, e2, hm2⟩ := record_live_lane (L := L) hp2
      obtain ⟨hg2, he2, pc2, mode2, hb2⟩ := hsrcs _ (List.mem_of_getElem? hi) (g2, e2) hm2
      have hdiv2 : e2.1 / L.block = c := by rw [he2]; exact lane_div hg2
      have heq := hcount e e2 id count cnt2 pc pc2 mode mode2 (hdiv.trans hdiv2.symm) hb hb2
      subst heq
      rw [hn] at htg
      exact hkn (Except.ok.inj htg).symm
  · cases hp
    simp [Error.isFault] at hfault

end
end PTX.NamedBar
