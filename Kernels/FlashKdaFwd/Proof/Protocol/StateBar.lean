-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Init
public import Lemmas.Protocol.TmaUnits
public import Lemmas.Protocol.TmaUnitsFault
public import Lemmas.Protocol.TmaUnitsBlock
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # The state barrier: a one-shot barrier fed by sixteen loads of one size

The load leader initializes the
barrier (count 1), arrives once expecting 65536 bytes, and issues the 16 asynchronous loads of
the FP32 initial state (4096 bytes each) that complete on it; after the next `bar.sync 0` every
thread polls the barrier with parity 0 until it succeeds, once.

The library's one-shot barrier (`MbarOneShot`) does not fit: its copies are linear bulk copies
(`cp.async.bulk`, records `.notify .copy`), and these are tensor loads (records
`.notify .load`). What fits is the full barrier of a ring without its empty barrier: the
counted items of a barrier fed by one thread's equally sized loads (`MbarRing.TmaUnits.Obj`,
`Lemmas/Protocol/TmaUnits.lean`, instantiated by TmlFa4Fwd's Q ring), with `n = 16` and
`bytes = 4096`. There is one use, so the attribution needs no engine: the phase a poll observes
holds 17 items (`TmaUnits.Obj.card_phase`) and there are only 17 (`items_use_zero`).

**What the thread layer exports** (`StateFacts`): the arrival is the load leader's, expects
65536 bytes and is its first; a load completing on the barrier is the load leader's, moves 4096
bytes and has fewer than 16 predecessors; a poll is of the thread's own CTA with parity 0, and
a successful one is the thread's first.

**What the library gives from them.**

* `stateObj`: the barrier is a `MbarRing.TmaUnits.Obj … 16 4096`.
* `faultFree`: no record of the barrier has a fault (`TmaUnits.Obj.fault_free`; both side
  conditions hold because every item is of use 0).
* `short` (for progress): with no tensor copy open, the load leader has made at most as many
  arrivals as the barrier's final phase or has issued fewer than 16 loads per phase reached
  (`TmaUnits.Obj.short`).
* `observes_load`: every thread's successful poll observed the completion of each of the 16
  loads (`WaitObserves`). This orders the loads' writes of the FP32 state buffer before
  every later access of that thread (the conversion reads, the carry loads, the output writes,
  the final-state writes) and before every later load or store the thread issues into the same
  bytes, and it is what the shared-memory lifetime rule asks of the loads. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 20000

/-- **Thread-layer facts about the state barrier.** -/
structure StateFacts (L : Launch) (X : Execution) : Prop where
  /-- An arrival on the state barrier is the load leader's first: one release arrival expecting
  65536 bytes. -/
  arrive : ∀ {g i pc tx cnt c : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, i) = some ⟨pc, .arrive (Bar.state.loc L c) tx cnt rel sc⟩ →
      g = loadLeader L c ∧ tx = 65536 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (Bar.state.loc L c) ((X.tr g).take i) = 0
  /-- A load that completes on the state barrier is the load leader's, moves 4096 bytes and has
  fewer than 16 predecessors. -/
  issue : ∀ {g i pc al c : Nat} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = Bar.state.loc L c →
      g = loadLeader L c ∧ TensorTransfer.bytes sp.descriptor = 4096 ∧
      ((X.tr g).take i).countP (issuesTo (Bar.state.loc L c)) < 16
  /-- A poll of the state barrier has parity 0; a successful one acquires and is its thread's
  first. -/
  poll : ∀ {g i pc p c : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, i) = some ⟨pc, .wait (Bar.state.loc L c) p ok acq sc⟩ →
      c = g / L.block ∧ p % 2 = 0 ∧
      (ok = true → acq = true ∧ okPolls (Bar.state.loc L c) ((X.tr g).take i) = 0)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

namespace StateFacts

section
variable (hS : StateFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hS hI hB hN hX hb

/-- **The state barrier's updates are the load leader's**: one arrival expecting `16 * 4096`
bytes and loads of 4096 bytes. -/
theorem stateObj (c : Nat) :
    MbarRing.TmaUnits.Obj X (Bar.state.loc L c) (loadLeader L c) 16 4096 := by
  refine ⟨hI.initFirst hB hX hb c .state,
    objects_noInval hX.tma.2.2.1 (fun e m => hN.inval e m) _, ?_, ?_, ?_⟩
  · intro r hr ha
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | tensor _ _ _ ha'
    | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha' | clc _ _ _ _ ha' =>
      rw [ha] at ha'; cases ha'
    | increment _ he _ => exact hN.asyncArrive _ _ _ ⟨_, he⟩
  · intro k c' tx r hr ha
    cases record_source hX.tma.2.2.1 (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | increment _ _ ha'
    | bulk _ _ _ _ ha' => rw [ha] at ha'; cases ha'
    | @arrive h j pc tx' cnt rel sc hid he ha' =>
      rw [ha] at ha'
      simp only [Action.arrive.injEq] at ha'
      obtain ⟨rfl, rfl⟩ := ha'
      obtain ⟨rfl, rfl, rfl, -⟩ := hS.arrive (Frame.lt_of_get hX he) he
      exact ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩
    | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
    | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
    | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
  · intro k b r hr ha
    cases record_source hX.tma.2.2.1 (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | increment _ _ ha'
    | arriveOn _ _ _ _ ha' | commit _ _ _ ha' => rw [ha] at ha'; cases ha'
    | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
    | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
    | @tensor i pc al sp hid he hm ha' =>
      obtain ⟨g, j⟩ := i
      rw [ha] at ha'
      simp only [Action.completeTx.injEq] at ha'
      obtain ⟨rfl, hbytes, -⟩ := hS.issue (Frame.lt_of_get hX he) he hm
      exact ⟨ha'.trans hbytes, j, pc, al, sp, hid, he, hm⟩

/-- Every counted item of the state barrier is of use 0: the leader arrives once and issues at
most 16 loads. -/
theorem items_use_zero {c : Nat} (hc : c < L.grid)
    {x : Fin (16 + 1) × Nat}
    (hx : x ∈ MbarRing.TmaUnits.S X (Bar.state.loc L c) (loadLeader L c) 16 4096) : x.2 = 0 := by
  have hy : loadLeader L c < L.threads := thr_lt hb hc (by decide)
  obtain ⟨-, h0, h1⟩ := (hS.stateObj hI hB hN hX hb c).source hx
  by_cases hk : x.1.val = 0
  · obtain ⟨⟨pc, rel, sc, he⟩, hu⟩ := h0 hk
    have h := (hS.arrive (g := loadLeader L c)
      (i := (MbarRing.TmaUnits.op X (Bar.state.loc L c) (loadLeader L c) 16 x.1 x.2).2) hy
      he).2.2.2.2
    exact hu.symm.trans h
  · obtain ⟨⟨pc, al, sp, he, hm⟩, hu⟩ := h1 hk
    have h := (hS.issue (g := loadLeader L c)
      (i := (MbarRing.TmaUnits.op X (Bar.state.loc L c) (loadLeader L c) 16 x.1 x.2).2) hy
      he hm).2.2
    have h' : 16 * x.2 + (x.1.val - 1) < 16 := hu ▸ h
    omega

/-- **No record of the state barrier has a fault.** -/
theorem faultFree {c : Nat} (hc : c < L.grid) :
    ∀ r ∈ X.objects (Bar.state.loc L c), r.fault = none := by
  have o := hS.stateObj hI hB hN hX hb c
  have hy : loadLeader L c < L.threads := thr_lt hb hc (by decide)
  refine o.fault_free hX (by decide) (by decide) ?_ (fun t _ x hx => by
    rw [hS.items_use_zero hI hB hN hX hb hc hx]
    exact Nat.zero_le _)
  -- no update of the barrier is an item of a use beyond the first
  intro k r x hk hid hact hpos
  exfalso
  rcases hact with ⟨c', tx, ha⟩ | ⟨b, ha⟩
  · obtain ⟨-, -, j, pc, rel, sc, hj, he⟩ := o.arrive hk ha
    have hx0 : x.1.val = 0 := by
      by_contra hne
      rw [hj] at hid
      simp [MbarRing.TmaUnits.it, hne] at hid
    have hj2 : j = nthEv X (arrivesOn (Bar.state.loc L c)) (loadLeader L c) x.2 := by
      rw [hj] at hid
      simp only [MbarRing.TmaUnits.it, hx0, ↓reduceIte, Ref.thread.injEq, MbarRing.TmaUnits.op,
        Prod.mk.injEq, true_and] at hid
      exact hid
    have hcnt : arrivals (Bar.state.loc L c) ((X.tr (loadLeader L c)).take j) = x.2 := by
      unfold arrivals
      rw [hj2]
      exact (nthEv_spec_of_get (hj2 ▸ he)).2
    have h0 := (hS.arrive hy he).2.2.2.2
    omega
  · obtain ⟨-, j, pc, al, sp, hj, he, hm⟩ := o.copy hk ha
    have hx0 : x.1.val ≠ 0 := by
      intro h0
      rw [hj] at hid
      simp [MbarRing.TmaUnits.it, h0] at hid
    have hj2 : j = nthEv X (issuesTo (Bar.state.loc L c)) (loadLeader L c)
        (16 * x.2 + (x.1.val - 1)) := by
      rw [hj] at hid
      simp only [MbarRing.TmaUnits.it, hx0, ↓reduceIte, Ref.async.injEq, and_true,
        MbarRing.TmaUnits.op, Prod.mk.injEq, true_and] at hid
      exact hid
    have hcnt : ((X.tr (loadLeader L c)).take j).countP (issuesTo (Bar.state.loc L c)) =
        16 * x.2 + (x.1.val - 1) := by
      rw [hj2]
      exact (nthEv_spec_of_get (hj2 ▸ he)).2
    have h0 := (hS.issue hy he hm).2.2
    omega

/-- **Who a thread blocked at the state barrier waits for** (for progress): with no tensor copy
open, the load leader has made at most as many arrivals on the barrier as its final phase, or
has issued fewer than 16 loads per phase reached. -/
theorem short {c : Nat} (hc : c < L.grid) (hno : ¬ Descent.Obl L X .tensor) {st : State}
    (hst : stateBefore (X.objects (Bar.state.loc L c))
      (X.objects (Bar.state.loc L c)).length = some st) :
    arrivals (Bar.state.loc L c) (X.tr (loadLeader L c)) ≤ st.phase ∨
      (X.tr (loadLeader L c)).countP (issuesTo (Bar.state.loc L c)) < 16 * (st.phase + 1) :=
  (hS.stateObj hI hB hN hX hb c).short hX (by decide) (hS.faultFree hI hB hN hX hb hc) hno hst
    fun x hx => by
      rw [hS.items_use_zero hI hB hN hX hb hc hx]
      exact Nat.zero_le _

/-- **Every thread's successful poll of the state barrier observed each of the 16 loads.** -/
theorem observes_load {c : Nat} (hc : c < L.grid) {h j pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (Bar.state.loc L c) p true acq sc⟩) (r : Fin 16) :
    WaitObserves X
      (.async (loadLeader L c, nthEv X (issuesTo (Bar.state.loc L c)) (loadLeader L c) r.val)
        (.notify .load)) (h, j) (Bar.state.loc L c) acq sc := by
  classical
  have o := hS.stateObj hI hB hN hX hb c
  have hpar : ∀ {k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (h, k) = some ⟨pc, .wait (Bar.state.loc L c) p true acq sc⟩ →
        p % 2 = (okPolls (Bar.state.loc L c) ((X.tr h).take k) + 0) % 2 := by
    intro k pc p acq sc hk
    obtain ⟨-, hp, hok⟩ := hS.poll (Frame.lt_of_get hX hk) hk
    rw [(hok rfl).2, hp]
  have hAlt := o.counted.alt hX hpar
  have hj0 : okPolls (Bar.state.loc L c) ((X.tr h).take j) = 0 :=
    ((hS.poll (Frame.lt_of_get hX he) he).2.2 rfl).2
  have hlt : 0 < okPolls (Bar.state.loc L c) (X.tr h) := by
    have := PairTmaRing.okPolls_lt_of_get he
    omega
  have hjn : MbarRing.Poll.nth X (Bar.state.loc L c) h 0 = j := by
    rw [← hj0]; exact MbarRing.Poll.nth_eq he
  -- the observed phase holds 17 counted items, and there are only the 17 of use 0
  have hcard := o.card_phase hX (by decide) (by decide) (δ := 0) (Nat.zero_le 1) hAlt
    (Nat.zero_le 0) hlt
  have hsub : (MbarRing.TmaUnits.S X (Bar.state.loc L c) (loadLeader L c) 16 4096).filter
      (fun x => MbarRing.Counted.ph X (Bar.state.loc L c)
        (MbarRing.TmaUnits.it X (Bar.state.loc L c) (loadLeader L c) 16) x =
          MbarRing.Unit.obsOf X (Bar.state.loc L c) h 0) ⊆
      (Finset.univ : Finset (Fin (16 + 1))) ×ˢ ({0} : Finset Nat) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr
      (hS.items_use_zero hI hB hN hX hb hc (Finset.mem_filter.mp hx).1)⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)
  have hmem : ((⟨r.val + 1, by omega⟩ : Fin (16 + 1)), 0) ∈
      (Finset.univ : Finset (Fin (16 + 1))) ×ˢ ({0} : Finset Nat) :=
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩
  rw [← heq] at hmem
  obtain ⟨hS', hph⟩ := Finset.mem_filter.mp hmem
  have hub := o.counted.ubw hX (Nat.zero_le 1) hAlt (Nat.zero_le 0) hlt hS' hph
  have hit : MbarRing.TmaUnits.it X (Bar.state.loc L c) (loadLeader L c) 16
      (⟨r.val + 1, by omega⟩ : Fin (16 + 1)) 0 =
      .async (loadLeader L c, nthEv X (issuesTo (Bar.state.loc L c)) (loadLeader L c) r.val)
        (.notify .load) := by
    simp [MbarRing.TmaUnits.it, MbarRing.TmaUnits.op]
  simp only at hub
  rw [hit, hjn] at hub
  exact ⟨⟨pc, p, he⟩, hub⟩

end

end StateFacts

end

end PTX.Kernels.FlashKdaFwd.Protocol
