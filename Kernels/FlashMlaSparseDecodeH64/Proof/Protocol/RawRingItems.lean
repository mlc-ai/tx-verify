-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingInitialized
public import Lemmas.Protocol.PairTmaRing.Attribution
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantRawOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate

@[expose] public section

/-! # The 17 item kinds of a raw-ready phase -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

noncomputable section

abbrev Item := Fin 17

/-- The one TMA issuer for a CTA's raw buffer. Already traced ready arrivals and gathers
identify this same thread. -/
def Issuer (P : Params) (L : Launch) (X : Execution) (cta : Nat) (g : Nat) : Prop :=
  ∀ h i (d : Wg1Tma.D), ctaOf L h = cta →
    Frame.stateAt (Machine.code P L) X h i = some (some (.tma d)) →
    (d.site = .rawReady ∨ ∃ k, d.site = .issue k) → h = g

/-- Item zero is the expectation arrival. The other sixteen items are the gather completions
of the use, in issue order. -/
def opFull (X : Execution) (m : Loc) (g : Nat) (k : Item) (u : Nat) : EvId :=
  (g, if k.val = 0 then nthEv X (arrivesOn m) g u
      else nthEv X (issuesTo m) g (16 * u + (k.val - 1)))

def itemFull (X : Execution) (m : Loc) (g : Nat) (k : Item) (u : Nat) : Ref :=
  if k.val = 0 then .thread (opFull X m g k u) else .async (opFull X m g k u) (.notify .load)

def actionFull (k : Item) : Action :=
  if k.val = 0 then .arrive 1 36864 else .completeTx 2304

open Classical in
def countedFull (X : Execution) (m : Loc) (g : Nat) : Finset (Item × Nat) :=
  (Finset.univ ×ˢ Finset.range ((X.tr g).length + 1)).filter fun x =>
    ∃ r ∈ X.objects m, r.id = itemFull X m g x.1 x.2 ∧
      r.fault = none ∧ r.action = actionFull x.1

def phaseFull (X : Execution) (m : Loc) (g : Nat) (x : Item × Nat) : Nat :=
  MbarRing.Poll.phaseOf X m (itemFull X m g x.1 x.2)

local notation "full" => ready
local notation "empty" => free

private theorem item_mem {X : Execution} {m : Loc} {g : Nat} {k : Item} {u : Nat}
    {r : Record Ref} (hr : r ∈ X.objects m) (hid : r.id = itemFull X m g k u)
    (hf : r.fault = none) (ha : r.action = actionFull k) (hu : u < (X.tr g).length + 1) :
    (k, u) ∈ countedFull X m g := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_univ _, Finset.mem_range.mpr hu⟩, r, hr, hid, hf, ha⟩

private theorem op_zero (X : Execution) (m : Loc) (g u : Nat) :
    opFull X m g (0 : Item) u = (g, nthEv X (arrivesOn m) g u) := rfl

/-- The gather item names its issue at sixteen issues per generation. -/
theorem op_gather (X : Execution) (m : Loc) (g u : Nat) (k : Fin 16) :
    opFull X m g ⟨k.val + 1, by have := k.isLt; omega⟩ u =
      (g, nthEv X (issuesTo m) g (16 * u + k.val)) := by
  simp [opFull]

section
variable {P : Params} {L : Launch}

/-- A fault-free update of the ready history is precisely a counted item of the actual issuer. -/
theorem actual_counted_of_record {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2}
    {r : Record Ref} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hp : Issuer P L X cta g)
    (hr : r ∈ X.objects (full L cta slot)) (hf : r.fault = none)
    (hu : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ countedFull X (full L cta slot) g, r.id = itemFull X (full L cta slot) g x.1 x.2 := by
  set m := full L cta slot
  rcases hu with ⟨n, tx, ha⟩ | ⟨n, ha⟩
  · obtain ⟨rfl, rfl, h, i, e, d, hid, he, hk, hc, hd, _, hst⟩ :=
      actual_ready_arrival_record hpre hX hs hr ha
    have hh := hp h i d hc hst (.inl hd)
    subst h
    let u := arrivals m ((X.tr g).take i)
    have hi : arrivesOn m e = true := by simp [arrivesOn, sourceArrive, hk, m]
    have hitem : r.id = itemFull X m g (0 : Item) u := by
      rw [hid, itemFull, op_zero]
      change Ref.thread (g, i) = Ref.thread (g, nthEv X (arrivesOn m) g u)
      unfold u arrivals
      rw [nthEv_eq he hi]
    have hun : u < (X.tr g).length + 1 := by
      have hlt : i < (X.tr g).length := PTX.len_of_get he
      have hle : u ≤ i := (List.countP_le_length).trans (List.length_take_le _ _)
      omega
    exact ⟨(0, u), item_mem hr hitem hf ha hun, hitem⟩
  · obtain ⟨hn, h, i, e, a, sp, d, k, hid, he, hk, hm, hc, hd, _, _, _, hst⟩ :=
      actual_gather_record hpre hX hs hr ha
    have hh := hp h i d hc hst (.inr ⟨k, hd⟩)
    subst h
    let p := issuesTo m
    let ordinal := ((X.tr g).take i).countP p
    let u := ordinal / 16
    let j : Fin 16 := ⟨ordinal % 16, Nat.mod_lt _ (by decide)⟩
    let key : Item := ⟨j.val + 1, by have := j.isLt; omega⟩
    have hj : key.val ≠ 0 := by simp [key]
    have hi : p e = true := by simp [p, issuesTo, hk, hm, m]
    have hx : 16 * u + j.val = ordinal := by dsimp [u, j]; omega
    have hitem : r.id = itemFull X m g key u := by
      rw [hid, itemFull, ite_eq_right hj, op_gather, hx, nthEv_eq he hi]
    have hun : u < (X.tr g).length + 1 := by
      have hi : i < (X.tr g).length := PTX.len_of_get he
      have hdiv : u ≤ ordinal := Nat.div_le_self _ _
      have hle : ordinal ≤ i := (List.countP_le_length).trans (List.length_take_le _ _)
      omega
    have hact : r.action = actionFull key := by simp [actionFull, hj, ha, hn]
    exact ⟨(key, u), item_mem hr hitem hf hact hun, hitem⟩

/-- Raw-ready alternation in the followed trace. -/
theorem ready_alt {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    :
    SelectedAlternates (objectThreadSelected g) (X.objects (full L cta slot)) 0 := by
  apply MbarRing.Poll.alternates hX (PairTmaRing.poll_clean hX
    (ready_init_first hpre hX hs ht) (objects_single_lifetime hX _))
  intro i _ _ _ _ he
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hc, d, hb, hd, hp, hst⟩ := await_ready_source hpre hX (hs g hg) ht he rfl
  have hcount := Wg2RawTrace.composed_raw_ready_count hpre
    ((hs g hg).produces (hX.thr g hg)) hst hd
  rw [hc, hb] at hcount
  change PTX.Flow.okPolls (full L cta slot) ((X.tr g).take i) = _ at hcount
  rw [hcount, hp]
  omega

private theorem ready_poll_obs {mem0 : Mem0} {X : Execution} {cta g n : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects (full L cta slot)) 0)
    (hn : n < PTX.Flow.okPolls (full L cta slot) (X.tr g)) :
    ∃ (k : Nat) (w : Record Ref) (st : State), (X.objects (full L cta slot))[k]? = some w ∧
      w.id = .thread (g, MbarRing.Poll.nth X (full L cta slot) g n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      stateBefore (X.objects (full L cta slot)) k = some st ∧ 0 < st.phase ∧
      observedAt (X.objects (full L cta slot)) k = some (st.phase - 1) ∧
      Unit.obsOf X (full L cta slot) g n = st.phase - 1 := by
  have hnI := objects_single_lifetime hX (full L cta slot)
  have hclean := PairTmaRing.poll_clean hX (actual_ready_init_first hpre hX hs) hnI
  obtain ⟨k, w, _, hk, hwid, _, hww, hwf, hsel⟩ := MbarRing.Poll.record hX hclean hn
  have hselected : objectThreadSelected g w.id = true :=
    objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
    hnI (by decide) hAlt hk hselected hww (by omega)
  refine ⟨k, w, st, hk, hwid, hww, hwf, hst, hpos, ho, ?_⟩
  unfold Unit.obsOf
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hk ho

private theorem counter_action (k : Item) : CounterUpdate (actionFull k) := by
  unfold actionFull
  split <;> trivial

/-- The 17 items are actual fault-free records and acquire polling observes their phase. -/
theorem actual_observed_full_item {mem0 : Mem0} {X : Execution} {cta g h n : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hAlt : SelectedAlternates (objectThreadSelected h) (X.objects (full L cta slot)) 0)
    (hn : n < PTX.Flow.okPolls (full L cta slot) (X.tr h))
    (hx : x ∈ countedFull X (full L cta slot) g)
    (hp : phaseFull X (full L cta slot) g x = Unit.obsOf X (full L cta slot) h n) :
    MbarObserved X (itemFull X (full L cta slot) g x.1 x.2)
      (.thread (h, MbarRing.Poll.nth X (full L cta slot) h n)) := by
  classical
  obtain ⟨_, r, hmem, hid, hf, ha⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨i, w, st, hi, hw, hww, _, _, _, hobs, hs'⟩ := ready_poll_obs hpre hX hs hAlt hn
  have hno := objects_single_lifetime hX (full L cta slot)
  have hfirst := actual_ready_init_first hpre hX hs (cta := cta) (slot := slot)
  obtain ⟨_, t, hst, _⟩ := PairTmaRing.state_of_init hX hfirst hno hk (by
    intro n
    rw [ha]
    unfold actionFull
    split <;> simp)
  have hphase : phaseAt (X.objects (full L cta slot)) k = some t.phase := by simp [phaseAt, hst]
  have hlookup := MbarRing.Poll.phaseOf_eq hX hk hphase
  unfold phaseFull at hp
  rw [← hid, hlookup, hs'] at hp
  rw [hp] at hphase
  have hct : CounterUpdate r.action := by rw [ha]; exact counter_action x.1
  have h := Consistent.observed_of_phase hX hno hk hf hct hi hww hphase hobs
  rwa [hid, hw] at h

/-- A phase observed by the dequantizer has one expectation arrival and sixteen completions. -/
theorem actual_counted_full_card {mem0 : Mem0} {X : Execution} {cta g h n : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hAlt : SelectedAlternates (objectThreadSelected h) (X.objects (full L cta slot)) 0)
    (hp : Issuer P L X cta g) (hn : n < PTX.Flow.okPolls (full L cta slot) (X.tr h)) :
    17 ≤ ((countedFull X (full L cta slot) g).filter
      (fun x => phaseFull X (full L cta slot) g x = Unit.obsOf X (full L cta slot) h n)).card := by
  classical
  let m := full L cta slot
  let log := X.objects m
  obtain ⟨i, w, st, hi, _, _, _, hst, hpos, _, ho⟩ := ready_poll_obs hpre hX hs hAlt hn
  let q := st.phase - 1
  let U := (Finset.range log.length).filter (fun p => UnitArrivalIn log q p)
  let C := (Finset.range log.length).filter (fun p => ∃ r, log[p]? = some r ∧
    r.action = .completeTx 2304 ∧ r.fault = none ∧ phaseAt log p = some q)
  have hiLt : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  have hch := X.objects_checked hX m
  have hnI := objects_single_lifetime hX m
  have hInit := actual_ready_init_first hpre hX hs (cta := cta) (slot := slot)
  have expected : ∀ p s, p ≤ log.length → stateBefore log p = some s → s.expected = 1 :=
    fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hnI h
  have arrivals : ∀ r ∈ log, r.fault = none → ∀ c tx, r.action = .arrive c tx →
      c = 1 ∧ tx = 36864 := by
    intro r hr _ c tx ha
    obtain ⟨hCount, hBytes, _⟩ := actual_ready_arrival_record hpre hX hs hr ha
    exact ⟨hCount, hBytes⟩
  have hU : U.card = 1 := hch.card_unit_arrivals_phase hnI
    (fun p r c tx hr hf ha => (arrivals r (List.mem_of_getElem? hr) hf c tx ha).1)
    (fun p s hp h => expected p s hp h) (objects_no_pending_increment hX m)
    hiLt hst (by dsimp [q]; omega)
  obtain ⟨C', hC', hc⟩ := rawReady_completion_count (q := q) hch hnI arrivals
    (fun _ hr _ _ ha => (actual_gather_record hpre hX hs hr ha).1) expected
    (objects_no_pending_increment hX m) hiLt hst (by dsimp [q]; omega)
  have hCC : C' = C := by
    ext p
    rw [hC' p]
    simp only [C, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hlt, hr⟩
      exact ⟨hlt, hr⟩
    · intro ⟨hlt, hr⟩
      exact ⟨hlt, hr⟩
  have hC : C.card = 16 := hCC ▸ hc
  have hdis : Disjoint U C := by
    rw [Finset.disjoint_left]
    intro p hpU hpC
    obtain ⟨_, r, tx, hr, ha, _, _⟩ := Finset.mem_filter.mp hpU
    obtain ⟨_, r', hr', hact, _, _⟩ := Finset.mem_filter.mp hpC
    obtain rfl := Option.some.inj (hr.symm.trans hr')
    rw [ha] at hact
    cases hact
  have hCard : (U ∪ C).card = 17 := by
    rw [Finset.card_union_of_disjoint hdis, hU, hC]
  rw [← hCard]
  apply PairTmaRing.card_le_of_rel _ _
    (fun p x => ∃ r, log[p]? = some r ∧ r.id = itemFull X m g x.1 x.2)
  · intro p hp'
    have hrec : ∃ r, log[p]? = some r ∧ r.fault = none ∧ phaseAt log p = some q ∧
        ((∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) := by
      rcases Finset.mem_union.mp hp' with hu | hc
      · obtain ⟨_, r, tx, hr, ha, hf, hp⟩ := Finset.mem_filter.mp hu
        exact ⟨r, hr, hf, hp, .inl ⟨1, tx, ha⟩⟩
      · obtain ⟨_, r, hr, ha, hf, hp⟩ := Finset.mem_filter.mp hc
        exact ⟨r, hr, hf, hp, .inr ⟨2304, ha⟩⟩
    obtain ⟨r, hr, hf, hph, hact⟩ := hrec
    obtain ⟨x, hx, hRid⟩ := actual_counted_of_record hpre hX hs hp (List.mem_of_getElem? hr) hf hact
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hRid⟩
    unfold phaseFull
    rw [← hRid, MbarRing.Poll.phaseOf_eq hX hr hph, ho]
  · intro p _ p' _ x _ ⟨r, hr, hid⟩ ⟨r', hr', hid'⟩
    exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm)


private theorem full_operation {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hx : x ∈ countedFull X (full L cta slot) g)
    :
    ∃ e, X.get (opFull X (full L cta slot) g x.1 x.2) = some e ∧
      x.2 + 1 ≤ PTX.Flow.okPolls (empty L cta slot)
        ((X.tr g).take (opFull X (full L cta slot) g x.1 x.2).2) := by
  classical
  rcases x with ⟨key, u⟩
  obtain ⟨_, r, hr, hRid, _, ha⟩ := Finset.mem_filter.mp hx
  have hkeyLt := key.isLt
  by_cases hzero : key.val = 0
  · rw [actionFull, ite_eq_left hzero] at ha
    obtain ⟨_, _, h, i, e, d, hid, he, _, hc, hd, hslot, hst⟩ :=
      actual_ready_arrival_record hpre hX hs hr ha
    have hx := Ref.thread.inj (by simpa [itemFull, hzero] using hRid.symm.trans hid)
    rw [opFull, ite_eq_left hzero] at hx
    rcases Prod.mk.inj hx with ⟨rfl, hi⟩
    have hg := Frame.lt_of_get hX he
    obtain ⟨ha, hp⟩ := TmaRawTrace.composed_publish_counts hpre
      ((hs g hg).machine.produces (hX.thr g hg)) hst hd
    rw [hc, hslot] at ha hp
    have her : X.get (g, nthEv X (arrivesOn (full L cta slot)) g u) = some e := hi ▸ he
    have hOrdinal := (nthEv_spec_of_get her).2
    rw [hi] at hOrdinal
    change PTX.Flow.arrivals (full L cta slot) ((X.tr g).take i) = u at hOrdinal
    change PTX.Flow.arrivals (full L cta slot) ((X.tr g).take i) = _ at ha
    change PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take i) = _ at hp
    refine ⟨e, ?_, ?_⟩
    · simpa [opFull, hzero] using her
    · simp only [opFull, hzero, ↓reduceIte, hi, hp]
      omega
  · rw [actionFull, ite_eq_right hzero] at ha
    obtain ⟨_, h, i, e, a, sp, d, k, hid, he, _, _, hc, hd, hslot, _, _, hst⟩ :=
      actual_gather_record hpre hX hs hr ha
    have hItem : Ref.async (opFull X (full L cta slot) g key u) (.notify .load) =
        .async (h, i) (.notify .load) := by
      simpa [itemFull, hzero] using hRid.symm.trans hid
    have hx := (Ref.async.inj hItem).1
    rw [opFull, ite_eq_right hzero] at hx
    rcases Prod.mk.inj hx with ⟨rfl, hi⟩
    have hg := Frame.lt_of_get hX he
    have tr := (hs g hg).machine.produces (hX.thr g hg)
    have hCount := TmaGatherCounts.composed_issue_count hpre tr hst hd
    have hFree := TmaRawTrace.composed_gather_reuse_count hpre tr hst hd
    rw [hc, hslot] at hCount hFree
    let pred := issuesTo (full L cta slot)
    have her : X.get (g, nthEv X pred g (16 * u + (key.val - 1))) = some e := hi ▸ he
    have hOrdinal := (nthEv_spec_of_get her).2
    rw [hi] at hOrdinal
    change ((X.tr g).take i).countP pred = _ at hCount
    change PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take i) = _ at hFree
    have hk := k.isLt
    have hUse : u = d.block / 2 := by
      omega
    refine ⟨e, ?_, ?_⟩
    · simpa [opFull, hzero, pred] using her
    · simp only [opFull, hzero, ↓reduceIte, hi, hFree]
      omega

/-- Every counted expectation or gather is guarded by the issuer's actual free poll. -/
theorem actual_guard_full_item {mem0 : Mem0} {X : Execution} {cta g n : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hx : x ∈ countedFull X (full L cta slot) g)
    (hn : n ≤ x.2) :
    Resumes kernel X (g, MbarRing.Poll.nth X (empty L cta slot) g n)
      (opFull X (full L cta slot) g x.1 x.2) := by
  obtain ⟨e, he, hGuard⟩ := full_operation hpre hX hs hx
  rcases hx' : opFull X (full L cta slot) g x.1 x.2 with ⟨g', j⟩
  have heq : g' = g := (congrArg Prod.fst hx').symm
  subst g'
  rw [hx'] at he hGuard
  change x.2 + 1 ≤ PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take j) at hGuard
  have hj : j < (X.tr g).length := PTX.len_of_get he
  exact MbarRing.Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    hj (by omega)

/-- A gather issue precedes its completion notification through its write effect. -/
theorem actual_full_item_dependency {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hx : x ∈ countedFull X (full L cta slot) g)
    :
    Relation.ReflTransGen (DepStep L kernel X)
      (.thread (opFull X (full L cta slot) g x.1 x.2), false)
      (itemFull X (full L cta slot) g x.1 x.2, false) := by
  classical
  obtain ⟨e, he, -⟩ := full_operation hpre hX hs hx
  obtain ⟨_, r, hr, hid, -, -⟩ := Finset.mem_filter.mp hx
  by_cases hk : x.1.val = 0
  · rw [itemFull, ite_eq_left hk]
  · let i := opFull X (full L cta slot) g x.1 x.2
    have hid : r.id = .async i (.notify .load) := by simpa [itemFull, hk, i] using hid
    have hpres := object_record_present hX.tma hr
    rw [hid] at hpres
    obtain ⟨o, ho, hn⟩ := id hpres
    obtain ⟨a, b, k, hwrite⟩ := tensor_write_present hX.effectValidity ho hn
    have h := Relation.TransGen.single (DepStep.issue (L := L) (K := kernel)
      (p := .write (.load a b k)) ⟨_, he⟩ hwrite
      (fun _ h => by cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h))
    have h' := (h.tail (DepStep.node hwrite)).tail (DepStep.stage
      (c := (.async i (.notify .load), false)) (.inr ⟨rfl, rfl, rfl, rfl, hwrite, hpres⟩))
    simpa [itemFull, hk, i] using h'.to_reflTransGen


/-- The corresponding raw-ring fact in a fully followed execution. -/
theorem counted_of_record {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2}
    {r : Record Ref} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hp : Issuer P L X cta g)
    (hr : r ∈ X.objects (full L cta slot)) (hf : r.fault = none)
    (hu : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ countedFull X (full L cta slot) g, r.id = itemFull X (full L cta slot) g x.1 x.2 :=
  actual_counted_of_record hpre hX (fun _ hg => Machine.code_sound hpre hg) hp hr hf hu

/-- The corresponding raw-ring fact in a fully followed execution. -/
theorem observed_full_item {mem0 : Mem0} {X : Execution} {cta g h n : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hn : n < PTX.Flow.okPolls (full L cta slot) (X.tr h))
    (hx : x ∈ countedFull X (full L cta slot) g)
    (hp : phaseFull X (full L cta slot) g x = Unit.obsOf X (full L cta slot) h n) :
    MbarObserved X (itemFull X (full L cta slot) g x.1 x.2)
      (.thread (h, MbarRing.Poll.nth X (full L cta slot) h n)) :=
  actual_observed_full_item hpre hX (fun _ hg => Machine.code_sound hpre hg)
    (ready_alt hpre hX hs ht) hn hx hp

/-- The corresponding raw-ring fact in a fully followed execution. -/
theorem guard_full_item {mem0 : Mem0} {X : Execution} {cta g n : Nat} {slot : Fin 2}
    {x : Item × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hx : x ∈ countedFull X (full L cta slot) g)
    (hn : n ≤ x.2) :
    Resumes kernel X (g, MbarRing.Poll.nth X (empty L cta slot) g n)
      (opFull X (full L cta slot) g x.1 x.2) :=
  actual_guard_full_item hpre hX (fun _ hg => Machine.code_sound hpre hg) hx hn

set_option maxRecDepth 4096 in
/-- Each counted release follows the consumer's successful ready poll for the use. -/
theorem guard_empty_item {mem0 : Mem0} {X : Execution} {cta j : Nat} {slot : Fin 2}
    {y : Fin 128 × Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hy : y ∈ Unit.S X (empty L cta slot) (consumer L cta)) (hj : j ≤ y.2) :
    Resumes kernel X
      (consumer L cta y.1, MbarRing.Poll.nth X (full L cta slot) (consumer L cta y.1) j)
      (Unit.it X (empty L cta slot) (consumer L cta) y.1 y.2) := by
  let E := free_obj hpre hX hs ht (cta := cta) (slot := slot)
  obtain ⟨_, ⟨_, _, he⟩, hu⟩ := E.S_rec hy
  let g := consumer L cta y.1
  let i := (Unit.it X (empty L cta slot) (consumer L cta) y.1 y.2).2
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hc, d, hb, hd, hst⟩ := release_source hpre hX (hs g hg) ht he rfl
  obtain ⟨ha, hp⟩ := Wg2RawTrace.composed_raw_free_counts hpre
    ((hs g hg).produces (hX.thr g hg)) hst hd
  rw [hc, hb] at ha hp
  change PTX.Flow.arrivals (empty L cta slot) ((X.tr g).take i) = d.block / 2 at ha
  change PTX.Flow.okPolls (full L cta slot) ((X.tr g).take i) = d.block / 2 + 1 at hp
  change PTX.Flow.arrivals (empty L cta slot) ((X.tr g).take i) = y.2 at hu
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hcount : j + 1 ≤ PTX.Flow.okPolls (full L cta slot) ((X.tr g).take i) := by omega
  exact MbarRing.Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    hi hcount

set_option maxRecDepth 4096 in
/-- Construct a raw slot ring from the two actual object histories and their waiters. -/
def itemsOfHistory {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} (g : Nat)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hp : Issuer P L X cta g)
    (E : Unit.History X (empty L cta slot) 128 (consumer L cta))
    (hReadyAlt : ∀ lane : Fin 128,
      SelectedAlternates (objectThreadSelected (consumer L cta lane))
        (X.objects (full L cta slot)) 0)
    (hFreeAlt : SelectedAlternates (objectThreadSelected g) (X.objects (empty L cta slot)) 1)
    (hGuard : ∀ {j : Nat} {y : Fin 128 × Nat}, y ∈ Unit.S X (empty L cta slot) (consumer L cta) →
      j ≤ y.2 → Resumes kernel X
        (consumer L cta y.1, MbarRing.Poll.nth X (full L cta slot) (consumer L cta y.1) j)
        (Unit.it X (empty L cta slot) (consumer L cta) y.1 y.2)) :
    MbarRing.Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 17) where
  owner _ := 0
  ownF _ _ := 0
  wE _ n := (g, MbarRing.Poll.nth X (empty L cta slot) g n)
  opF _ := opFull X (full L cta slot) g
  itF _ := itemFull X (full L cta slot) g
  wF b j := (consumer L cta b, MbarRing.Poll.nth X (full L cta slot) (consumer L cta b) j)
  cm := Unit.it X (empty L cta slot) (consumer L cta)
  note b _ u := .thread (Unit.it X (empty L cta slot) (consumer L cta) b u)
  SF _ := countedFull X (full L cta slot) g
  phF _ := phaseFull X (full L cta slot) g
  SE _ := Unit.S X (empty L cta slot) (consumer L cta)
  phE _ := Unit.ph X (empty L cta slot) (consumer L cta)
  oF b n := Unit.obsOf X (full L cta slot) (consumer L cta b) n
  oE _ n := Unit.obsOf X (empty L cta slot) g n
  cover _ a := ⟨0, Subsingleton.elim _ _⟩
  guardP _ _ hx _ _ hn := actual_guard_full_item hpre hX hs hx hn
  issueF _ _ hx := actual_full_item_dependency hpre hX hs hx
  guardM _ _ hy _ hj := hGuard hy hj
  issue _ _ _ := .refl
  obsF lane _ hw _ hx hph :=
    Witness.of_mbarObserved (actual_observed_full_item hpre hX hs (hReadyAlt lane)
      (MbarRing.Poll.nth_present.mp hw)
      hx hph)
  obsE _ _ hn hw _ hy hph :=
    E.observed hX (by decide) hFreeAlt hn
      (MbarRing.Poll.nth_present.mp hw) hy hph
  fullF lane _ hw :=
    actual_counted_full_card hpre hX hs (hReadyAlt lane) hp (MbarRing.Poll.nth_present.mp hw)
  fullE _ _ hn hw :=
    E.card_phase hX (by decide) hFreeAlt hn
      (MbarRing.Poll.nth_present.mp hw)
  ltF lane _ _ hlt hw := by
    have hcount := MbarRing.Poll.nth_present.mp hw
    have hno := objects_single_lifetime hX (full L cta slot)
    have hclean := PairTmaRing.poll_clean hX (actual_ready_init_first hpre hX hs) hno
    exact ⟨MbarRing.Poll.nth_present.mpr (Nat.lt_trans hlt hcount),
      MbarRing.Poll.observed_lt hX (by decide) hclean hno (hReadyAlt lane)
        (Nat.zero_le _) hlt hcount⟩
  ltE _ _ _ hn hlt hw := by
    have hcount := MbarRing.Poll.nth_present.mp hw
    exact ⟨MbarRing.Poll.nth_present.mpr (Nat.lt_trans hlt hcount),
      MbarRing.Poll.observed_lt hX (le_refl 1) (E.pclean hX) E.noInval hFreeAlt
        hn hlt hcount⟩


/-- A raw consumer lane belongs to its CTA and warpgroup two. -/
theorem actual_consumer_geometry {mem0 : Mem0} (hpre : Pre P L mem0) (cta : Nat) (lane : Fin 128) :
    ctaOf L (consumer L cta lane) = cta ∧ wgOf L (consumer L cta lane) = 2 := by
  have hl := lane.isLt
  constructor
  · simp only [ctaOf, consumer, hpre.block]
    omega
  · simp only [wgOf, tidOf_eq hpre, consumer, hpre.block]
    omega

/-- Successful raw-ready waits of a consumer alternate with its observed generations. -/
theorem consumer_ready_alternates {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 2}
    (lane : Fin 128) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    SelectedAlternates (objectThreadSelected (consumer L cta lane)) (X.objects (full L cta slot))
      0 := by
  apply MbarRing.Poll.alternates hX (PairTmaRing.poll_clean hX
    (actual_ready_init_first hpre hX hs) (objects_single_lifetime hX _))
  intro i tag p acq sc he
  obtain ⟨hc, hw⟩ := actual_consumer_geometry hpre cta lane
  have hk : (⟨tag, .wait (full L cta slot) p true acq sc⟩ : Event).kind =
      .wait (full L (ctaOf L (consumer L cta lane)) slot) p true acq sc := by rw [hc]
  simpa only [hc, Nat.add_zero] using MachineTracking.actual_raw_ready_parity hpre hX hs hw he hk

/-- The actual raw-free history contains exactly the unit releases of its consumers. -/
theorem actual_free_history {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    Unit.History X (empty L cta slot) 128 (consumer L cta) :=
  ⟨by decide, consumer_inj L cta, actual_free_sources hpre hX hs,
    actual_free_init_first hpre hX hs, objects_single_lifetime hX _⟩

/-- The TMA issuer's successful reuse waits alternate with offset one. -/
theorem tma_free_alternates {mem0 : Mem0} {X : Execution} {cta g : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hw : warpOf L g = 5) :
    SelectedAlternates (objectThreadSelected g) (X.objects (empty L cta slot)) 1 := by
  apply MbarRing.Poll.alternates hX ((actual_free_history hpre hX hs).pclean hX)
  intro i tag p acq sc he
  have hg := Frame.lt_of_get hX he
  have hFollow := MachineTracking.tracked_tma_warp hpre hX hs hw i
  obtain ⟨_, _, hc, d, hb, hd, hParity, hst⟩ :=
    reuse_source_at_followed hpre hX (hs g hg).machine hFollow he rfl
  have hCount := TmaRawTrace.composed_reuse_count hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hst hd
  rw [hc, hb] at hCount
  change PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take i) = _ at hCount
  rw [hCount, hParity]
  omega
end

set_option maxRecDepth 4096 in
/-- The raw slot is an actual ring of one issuer, sixteen gathers and 128 consumers. -/
def actual_items {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} (g : Nat)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hw : warpOf L g = 5) (hp : Issuer P L X cta g) :
    MbarRing.Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 17) := by
  let E : Unit.History X (empty L cta slot) 128 (consumer L cta) := actual_free_history hpre hX hs
  apply itemsOfHistory g hpre hX hs hp E (fun lane => consumer_ready_alternates lane hpre hX hs)
    (tma_free_alternates hpre hX hs hw)
  intro j y hy hj
  obtain ⟨_, ⟨tag, sc, he⟩, hOrdinal⟩ := E.S_rec hy
  let h := consumer L cta y.1
  let i := (Unit.it X (empty L cta slot) (consumer L cta) y.1 y.2).2
  obtain ⟨hc, hwg⟩ := actual_consumer_geometry hpre cta y.1
  have hk : (⟨tag, .arrive (empty L cta slot) 0 1 true sc⟩ : Event).kind =
      .arrive (empty L (ctaOf L h) slot) 0 1 true sc := by rw [show ctaOf L h = cta from hc]
  have hCount := MachineTracking.actual_raw_release_counts hpre hX hs hwg he hk
  rw [hc] at hCount
  change PTX.Flow.arrivals (empty L cta slot) ((X.tr h).take i) = y.2 at hOrdinal
  have hBefore : PTX.Flow.okPolls (full L cta slot) ((X.tr h).take i) = y.2 + 1 :=
    hCount.trans (congrArg (· + 1) hOrdinal)
  have hBound : j + 1 ≤ PTX.Flow.okPolls (full L cta slot) ((X.tr h).take i) :=
    hBefore.symm ▸ Nat.succ_le_succ hj
  exact MbarRing.Poll.guard (fun _ _ _ _ _ _ he => RingSpins.successful_poll hX he)
    (PTX.len_of_get he) hBound

set_option maxRecDepth 4096 in
/-- The raw slot is a concrete ring of one producer, 17 ready items and 128 releases. -/
def items {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} (g : Nat)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hp : Issuer P L X cta g) :
    MbarRing.Items.Ring L kernel Assumptions.all X 1 128 1 (fun _ => 17) :=
  itemsOfHistory (slot := slot) g hpre hX (fun _ hg => Machine.code_sound hpre hg) hp
    (free_obj hpre hX hs ht (slot := slot)).history (fun _ => ready_alt hpre hX hs ht)
    ((free_obj hpre hX hs ht (slot := slot)).alt hX g)
    (fun hy hj => guard_empty_item hpre hX hs ht hy hj)


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
