-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Bars
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Kernel.Safety.Init
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.InitPublished
public import Lemmas.Protocol.NamedBarMember
public import Lemmas.Protocol.CountNth
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Order.OrderBaseCausality
public import Core.MBarrier.InitPublication

@[expose] public section

/-! # Initialization and publication of the eleven mbarriers

The ten pipeline barriers are initialized by the init leader before its first and second
`bar.sync 0`, the state barrier by the load leader before its third. The instruction
`fence.mbarrier_init.release.cluster` that follows each block plays no part: in the model it
publishes an initialization only together with a cluster barrier, and this kernel has none.
An initialization reaches the other threads through the CTA barrier (`BarFacts.handoff0`) and
the initializing thread's own later uses through program order.

**What the thread layer exports** (`InitFacts`): which thread initializes which barrier, with
which count and after how many `bar.sync 0` (`init_ev`); that a thread initializes a barrier at
one position only (`init_once`); that the initializing thread, when it is at the `bar.sync 0`
that publishes a barrier, has initialized it (`init_done`); and for every other event that names
a barrier: it names a barrier of its own CTA, and it comes after the publishing `bar.sync 0` of
its thread or, in the initializing thread, after the initialization (`use_ev`).
`NoEvents` lists the kinds of event the program has none of, and that every successful poll is
the poll of a canonical spin loop (a fact about the code).

**What the library gives from them.**

* `InitFacts.published`: every use of a barrier is preceded, in base causality, by an
  initialization of it. The proof takes the user's own `bar.sync 0` of the publishing ordinal,
  the initializing thread's arrival of the same ordinal (`NamedBar.Sources.member_arrival_any`)
  and the hand-off of the CTA barrier.
* `InitFacts.initFirst`: every barrier's history starts with its one initialization, without
  fault (`PairTmaRing.InitFirst`, the premise of every ring structure of the library), by
  `ObjectInit.initFirst_of_published` and `ObjectInit.record_issuer`
  (`Lemmas/Protocol/InitPublished.lean`).
* `InitFacts.noMbarUninit`: no barrier is used uninitialized (`MbarUninit`, one class of
  `Unsafe`). -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

/-- **Kinds of event the program has none of**, and the shape of its poll loops. Each field is
visible in the decoded instructions alone; `Export.lean` proves the structure for the kernel
from the code scans of `Proof/Top/Static.lean`. -/
structure NoEvents (K : Kernel) (X : Execution) : Prop where
  /-- No `mbarrier.inval`. -/
  inval : ∀ i m, ¬ X.MbInval i m
  /-- No `cp.async.mbarrier.arrive`. -/
  asyncArrive : ∀ i m noinc, ¬ X.AsyncArrive i m noinc
  /-- No linear bulk copy (`cp.async.bulk` without `.tensor`) and no `cp.async`. -/
  copy : ∀ i s, ¬ X.Copy i s
  /-- No Tensor Core (`tcgen05`) event: no multiply-accumulate, no commit, no Tensor Memory
  copy. -/
  tc : X.NoTc
  /-- No linear prefetch (`cp.async.bulk.prefetch`). -/
  prefetch : ∀ i a, ¬ X.BulkPrefetch i a
  /-- No cluster launch control request. -/
  clc : ∀ i s tg, ¬ X.ClcIssue i s tg
  /-- Every successful poll is the poll of a canonical spin loop. -/
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit

/-- **Thread-layer facts about the initialization and the use of the mbarriers.** -/
structure InitFacts (L : Launch) (X : Execution) : Prop where
  /-- An initialization is the owner's, of a barrier of its CTA, with the barrier's count, after
  the barrier's number of `bar.sync 0`. -/
  init_ev : ∀ {g k pc n : Nat} {m : Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .mbInit m n⟩ →
      ∃ b : Bar, m = b.loc L (g / L.block) ∧ n = b.count ∧ g = b.owner L (g / L.block) ∧
        bar0Before X (g, k) = b.gen
  /-- A thread initializes a barrier at one position. -/
  init_once : ∀ {g k k' pc pc' n n' : Nat} {m : Loc}, X.get (g, k) = some ⟨pc, .mbInit m n⟩ →
    X.get (g, k') = some ⟨pc', .mbInit m n'⟩ → k = k'
  /-- At its publishing `bar.sync 0` the owner has initialized the barrier. -/
  init_done : ∀ {c k pc : Nat} {cnt : Option Nat} {mode : BarMode} (b : Bar), c < L.grid →
    X.get (b.owner L c, k) = some ⟨pc, .bar 0 cnt mode⟩ →
    bar0Before X (b.owner L c, k) = b.gen →
      ∃ j pcj, j < k ∧ X.get (b.owner L c, j) = some ⟨pcj, .mbInit (b.loc L c) b.count⟩
  /-- Every other event that names a barrier names one of its CTA, after the publishing
  `bar.sync 0` of its thread or, in the owner, after the initialization. -/
  use_ev : ∀ {g k : Nat} {e : Event} {m : Loc}, g < L.threads → X.get (g, k) = some e →
    MbarOf e m → (∀ n, e.kind ≠ .mbInit m n) →
      ∃ b : Bar, m = b.loc L (g / L.block) ∧
        (b.gen + 1 ≤ bar0Before X (g, k) ∨
          g = b.owner L (g / L.block) ∧
            ∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj, .mbInit m b.count⟩)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

/-- No `tcgen05.commit`. -/
theorem NoEvents.commit (h : NoEvents K X) (i : EvId) (s : TcCommit.Spec) : ¬ X.Commit i s :=
  fun ⟨pc, he⟩ => h.tc i pc _ he

/-! ### Helpers -/

/-- An event that names an mbarrier is no memory access. -/
theorem mbarOf_not_access {e : Event} {m : Loc} (h : MbarOf e m) : e.acc = none := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first | rfl | exact h.elim

theorem countP_take_mono (P : Event → Bool) (es : List Event) {a b : Nat} (h : a ≤ b) :
    (es.take a).countP P ≤ (es.take b).countP P :=
  (List.take_sublist_take_left (l := es) h).countP_le (p := P)

/-! ### The `bar.sync 0` of an ordinal -/

/-- A thread with more than `q` `bar.sync 0` before position `k` has the one with `q` earlier
ones before `k`. -/
theorem BarFacts.nth_bar0 (hB : BarFacts L X T) (hX : Consistent L K A mem0 X) {g k q : Nat}
    (hq : q + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) :
    ∃ j pc, j < k ∧ X.IsBarrier (g, j) 0 none pc ∧ bar0Before X (g, j) = q := by
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0) hq
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjk.le] at hcj
  have hget : X.get (g, j) = some ev := by
    change (X.tr g)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjk]
  obtain ⟨pc, kd⟩ := ev
  cases kd with
  | bar id cnt mode =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    obtain ⟨rfl, h⟩ := hB.shape (Frame.lt_of_get hX hget) hget
    rcases h with ⟨-, rfl⟩ | ⟨h8, -⟩
    · exact ⟨j, pc, hjk, hget, hcj⟩
    · cases h8
  | _ => simp [Execution.isBarId] at hbj

theorem Bar.owner_warp {L : Launch} {c : Nat} (hb : L.block = 192) (b : Bar) :
    b.owner L c % L.block / 32 ∈ Finset.range 6 := by
  cases b <;> simp only [Bar.owner, initLeader, loadLeader] <;>
    rw [thr_mod hb (by decide)] <;> decide

namespace InitFacts

/-- Every initialization of a barrier is one event, with the barrier's count. -/
theorem init_site (hI : InitFacts L X) (hX : Consistent L K A mem0 X) {c : Nat} {b : Bar}
    {e : EvId} {c0 : Nat} (he : X.MbInit e (b.loc L c) c0) :
    ∀ i pc n, X.get i = some ⟨pc, .mbInit (b.loc L c) n⟩ → i = e ∧ n = b.count := by
  rintro ⟨g, k⟩ pc n hi
  obtain ⟨g', k'⟩ := e
  obtain ⟨pc', he⟩ := he
  obtain ⟨b1, hm1, hn1, hg1, -⟩ := hI.init_ev (Frame.lt_of_get hX hi) hi
  obtain ⟨b2, hm2, -, hg2, -⟩ := hI.init_ev (Frame.lt_of_get hX he) he
  obtain ⟨rfl, hc1⟩ := Bar.loc_inj hm1
  obtain ⟨rfl, hc2⟩ := Bar.loc_inj hm2
  have hgg : g = g' := by rw [hg1, hg2, ← hc1, ← hc2]
  subst hgg
  exact ⟨by rw [hI.init_once hi he], hn1⟩

/-- **Every use of a barrier follows an initialization of it** in base causality. -/
theorem published (hI : InitFacts L X) (hB : BarFacts L X T) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) {g k : Nat} {e : Event} {m : Loc} (he : X.get (g, k) = some e)
    (hm : MbarOf e m) (hni : ∀ n, e.kind ≠ .mbInit m n) :
    ∃ (b : Bar) (i : EvId), m = b.loc L (g / L.block) ∧ X.MbInit i m b.count ∧
      baseCausality L X i (g, k) := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hc := cta_lt hb hg
  obtain ⟨b, hmb, h⟩ := hI.use_ev hg he hm hni
  refine ⟨b, ?_⟩
  rcases h with hgen | ⟨-, j, pcj, hjk, hj⟩
  · -- the user's `bar.sync 0` of the publishing ordinal, which it has passed
    obtain ⟨j, pc, hjk, hbar, hord⟩ := hB.nth_bar0 hX hgen
    -- the owner's arrival of the same ordinal
    obtain ⟨i, pc', md, hi, hio⟩ := (hB.sources0 hb).member_arrival_any hX (shape0 hb) hbar
      (show j + 1 < (X.tr g).length by omega) (g := b.owner L (g / L.block))
      (Bar.owner_div hb b) (Bar.owner_warp hb b) (by
        rintro ⟨jx, pcx, hx⟩
        have h9 := hB.bar0_exit (Bar.owner_lt hb hc b) hx
        have hgen2 : b.gen ≤ 2 := by cases b <;> simp [Bar.gen]
        obtain ⟨i, pci, -, hi, hio⟩ := hB.nth_bar0 hX (g := b.owner L (g / L.block))
          (k := (X.tr (b.owner L (g / L.block))).length) (q := b.gen)
          (by rw [List.take_length, h9]; omega)
        exact ⟨i, pci, .sync, hi, hio.trans hord.symm⟩)
    have hio' : bar0Before X (b.owner L (g / L.block), i) = b.gen := hio.trans hord
    obtain ⟨j', pcj, hj'i, hinit⟩ := hI.init_done b hc hi hio'
    refine ⟨(b.owner L (g / L.block), j'), hmb, ⟨pcj, hmb ▸ hinit⟩, ?_⟩
    refine hB.handoff0 hX hb _ _ _ _ ⟨Bar.owner_lt hb hc b, hg, Bar.owner_div hb b⟩ hk ?_
    have h1 := countP_take_mono (Execution.isBarId 0) (X.tr (b.owner L (g / L.block)))
      (show j' + 1 ≤ i by omega)
    unfold bar0Before at hio' hgen
    unfold bar0UpTo bar0Before
    simp only at hio' hgen ⊢
    omega
  · refine ⟨(g, j), hmb, ⟨pcj, hj⟩, .single (.inl (po_of_not_access rfl hjk hk ?_))⟩
    rw [he]
    exact mbarOf_not_access hm

/-- **Every barrier is initialized first**: its history, once it has a record, starts with its
one initialization, with the barrier's count, without fault. -/
theorem initFirst (hI : InitFacts L X) (hB : BarFacts L X T) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (c : Nat) (b : Bar) :
    PairTmaRing.InitFirst X (b.loc L c) b.count := by
  intro r hr
  obtain ⟨ev, hget, hm, -⟩ := ObjectInit.record_issuer hX hr
  rcases hiss : r.id.issuer with ⟨g, k⟩
  rw [hiss] at hget
  -- the barrier's initialization
  obtain ⟨e, he⟩ : ∃ e, X.MbInit e (b.loc L c) b.count := by
    by_cases hi : ∃ n, ev.kind = .mbInit (b.loc L c) n
    · obtain ⟨n, hn⟩ := hi
      obtain ⟨pc, kd⟩ := ev
      simp only at hn
      subst hn
      obtain ⟨b', hm', hn', -, -⟩ := hI.init_ev (Frame.lt_of_get hX hget) hget
      obtain ⟨rfl, -⟩ := Bar.loc_inj hm'
      exact ⟨(g, k), pc, hn' ▸ hget⟩
    · push Not at hi
      obtain ⟨b', i, hm', hinit, -⟩ := hI.published hB hX hb hget hm hi
      obtain ⟨rfl, -⟩ := Bar.loc_inj hm'
      exact ⟨i, hinit⟩
  refine ObjectInit.initFirst_of_published hX he (Bar.count_valid b) (hI.init_site hX he)
    (fun s hs hn => ?_) r hr
  obtain ⟨ev', hget', hm', hnot⟩ := ObjectInit.record_issuer hX hs
  rcases hiss' : s.id.issuer with ⟨g', k'⟩
  rw [hiss'] at hget'
  have hni : ∀ n, ev'.kind ≠ .mbInit (b.loc L c) n := fun n hc' =>
    (hnot ⟨n, hc'⟩).elim fun n' hn' => hn n' hn'
  obtain ⟨b', i, hmb, ⟨pci, hi⟩, hbc⟩ := hI.published hB hX hb hget' hm' hni
  have := (hI.init_site hX he i pci _ hi).1
  subst this
  exact .inl hbc

/-- **No barrier is used uninitialized** (ERR-MBAR-UNINITIALIZED). -/
theorem noMbarUninit (hI : InitFacts L X) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) : ¬ MbarUninit L X := by
  rintro ⟨⟨g, k⟩, m, hu, hni, hno⟩
  obtain ⟨e, he, hm⟩ := usesMbar_mbarOf hu
  obtain ⟨b, i, -, hinit, hbc⟩ := hI.published hB hX hb he hm (usesMbar_not_init he hni)
  exact hno ⟨i, _, hinit, .inl hbc⟩

end InitFacts

end PTX.Kernels.FlashKdaFwd.Protocol
