-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Init
public import Kernels.FlashKdaFwd.Proof.Protocol.Fences
public import Lemmas.Protocol.UnitRingGate
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.UnitBlocker

@[expose] public section

/-! # The store pipeline: two stages, each a ring of two unit objects

The synchronization of the two output stages, with the proxy fences and the bulk-group waits
that belong to it (`Fences.lean`). Stage `o < 2` (CUTLASS `PipelineAsync<2>`) has the barrier
`storeFull o` (count 128: one arrival of each compute thread per tile, polled by the store
leader) and the barrier `storeEmpty o` (count 1: one arrival of the store leader per tile,
polled by the compute threads, whose first poll passes on the fresh barrier). This is the
library's `MbarRing.Unit.Ring` with 128 producers and one consumer; the model instance is
FlashAttn4Fwd's output ring (`Kernels/FlashAttn4Fwd/Proof/Protocol/OutputHandoff.lean`).

**What the thread layer exports** (`StoreFacts`): for each of the four barriers, who arrives on
it and who polls it, with the count of the arrival, the parity of the poll and the gate (an
arrival of a thread on one barrier of the stage follows more successful polls of the other
barrier than the thread's earlier arrivals); that no asynchronous load completes on them; that a
compute thread executes `fence.proxy.async` between a write of the output buffer and its next
arrival on `storeFull o` (`out_fence`); and that the store leader executes a `.read` bulk-group
wait covering a store between the store and its next arrival on `storeEmpty o` (`store_wait`).

**What the library gives from them.**

* `StoreFacts.unitRing`: the stage is a `MbarRing.Unit.Ring`.
* `full_handoff`, `empty_handoff` (`MbarRing.UnitHandoff`): the store leader's poll of
  `storeFull o` with `q` earlier successful ones synchronizes with every compute thread's arrival
  with `q` earlier ones; a compute thread's poll of `storeEmpty o` with `q + 1` earlier ones with
  the store leader's arrival with `q` earlier ones.
* `full_faultFree`, `empty_faultFree`: no record of the two barriers has a fault.
* `full_blocked`, `empty_blocked` (for progress): the store leader blocked at `storeFull o`
  has polled successfully as many times as the barrier's final phase, and some compute thread
  has exactly that many counted arrivals on it; a compute thread blocked at `storeEmpty o` has
  polled successfully once more than the final phase, which is the number of the store
  leader's counted arrivals (`MbarRing.Unit.Gate.blocked`).
* `publish_output`: a compute thread's write of the output buffer is visible to the store
  leader's asynchronous reads of the same tile and of later tiles (`Staging.publish_of_unit`).
* `release_output`: the source reads of a store are visible to the compute threads' writes of
  a later tile (`Staging.release_of_unit`). -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

/-- **Thread-layer facts about the store pipeline.** -/
structure StoreFacts (L : Launch) (X : Execution) : Prop where
  /-- An arrival on `storeFull o` is a compute thread's of the barrier's CTA: one release
  arrival without transaction bytes, after more successful polls of `storeEmpty o` than its
  earlier arrivals on `storeFull o`. -/
  full_arrive : ∀ {g i pc tx cnt c : Nat} {o : Fin 2} {rel : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .arrive ((Bar.storeFull o).loc L c) tx cnt rel sc⟩ →
      g % L.block < 128 ∧ c = g / L.block ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeFull o).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.storeEmpty o).loc L c) ((X.tr g).take i)
  /-- A poll of `storeFull o` is the store leader's, with the parity of its earlier successful
  polls; a successful one acquires. -/
  full_poll : ∀ {g i pc p c : Nat} {o : Fin 2} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, i) = some ⟨pc, .wait ((Bar.storeFull o).loc L c) p ok acq sc⟩ →
      g = storeLeader L c ∧
      p % 2 = okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true)
  /-- An arrival on `storeEmpty o` is the store leader's: one release arrival without
  transaction bytes, after more successful polls of `storeFull o` than its earlier arrivals on
  `storeEmpty o`. -/
  empty_arrive : ∀ {g i pc tx cnt c : Nat} {o : Fin 2} {rel : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .arrive ((Bar.storeEmpty o).loc L c) tx cnt rel sc⟩ →
      g = storeLeader L c ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeEmpty o).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take i)
  /-- A poll of `storeEmpty o` is a compute thread's of the barrier's CTA, with the parity of
  its earlier successful polls plus one; a successful one acquires. -/
  empty_poll : ∀ {g i pc p c : Nat} {o : Fin 2} {ok acq : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .wait ((Bar.storeEmpty o).loc L c) p ok acq sc⟩ →
      g % L.block < 128 ∧ c = g / L.block ∧
      p % 2 = (okPolls ((Bar.storeEmpty o).loc L c) ((X.tr g).take i) + 1) % 2 ∧
      (ok = true → acq = true)
  /-- No asynchronous load completes on a barrier of the store pipeline. -/
  no_tensor : ∀ {i : EvId} {pc a c : Nat} {o : Fin 2} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ →
      sp.mbar ≠ (Bar.storeFull o).loc L c ∧ sp.mbar ≠ (Bar.storeEmpty o).loc L c
  /-- Between a compute thread's access of the output buffer of stage `o` and its next arrival
  on `storeFull o` the thread executes a `fence.proxy.async.shared::cta`. -/
  out_fence : ∀ {g i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {o : Fin 2}
    {rel : Bool} {sc : MbarScope}, g < L.threads → X.Access (g, i) a w → a.Covers l →
    InOutput L (g / L.block) o.val l → i < e →
    X.get (g, e) = some ⟨pce, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩ →
      ∃ f pcf, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩
  /-- Between a store of the store leader that reads the output buffer of stage `o` and its
  next arrival on `storeEmpty o` the leader executes a `.read` bulk-group wait that covers the
  store. -/
  store_wait : ∀ {c i e pc addr pce tx cnt x y z : Nat} {s : TensorStore.Spec} {l : Loc}
    {o : Fin 2} {rel : Bool} {sc : MbarScope},
    X.get (storeLeader L c, i) = some ⟨pc, .tensorStore addr s⟩ →
    TensorStore.readLoc s x y z = some l → InOutput L c o.val l → i < e →
    X.get (storeLeader L c, e) =
      some ⟨pce, .arrive ((Bar.storeEmpty o).loc L c) tx cnt rel sc⟩ →
      ∃ w, i < w ∧ w < e ∧ BulkWaitsFor X .read (storeLeader L c, i) (storeLeader L c, w)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

namespace StoreFacts

section
variable (hS : StoreFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hS hI hB hN hX hb

/-- **Stage `o` of the store pipeline of CTA `c` is a ring of two unit objects.** -/
theorem unitRing {c : Nat} (hc : c < L.grid) (o : Fin 2) :
    MbarRing.Unit.Ring L K A X ((Bar.storeFull o).loc L c) ((Bar.storeEmpty o).loc L c) 128 1
      (computeThread L c) (fun _ => storeLeader L c) where
  F :=
    { pos := by decide
      inj := computeThread_inj L c
      src := fun r hr => by
        cases record_source hX.tma.2.2.1 hr with
        | init _ _ ha => exact .init ha
        | inval _ he _ => exact (hN.inval _ _ ⟨_, he⟩).elim
        | @arrive g j pc tx cnt rel sc hid he ha =>
          obtain ⟨hw, hc', rfl, rfl, rfl, -⟩ := hS.full_arrive (Frame.lt_of_get hX he) he
          exact .arrive hid (computeThread_of hb hw hc') he ha
        | wait hid he ha => exact .poll hid he ha
        | tensor _ he hm _ => exact ((hS.no_tensor (c := c) (o := o) he).1 hm).elim
        | increment _ he _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
        | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
        | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
        | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
        | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
      init := hI.initFirst hB hX hb c (.storeFull o)
      noInval := objects_noInval hX.tma.2.2.1 (fun e m => hN.inval e m) _
      parity := fun he => by
        rw [Nat.add_zero]
        exact (hS.full_poll (Frame.lt_of_get hX he) he).2.1
      δ_le := Nat.zero_le 1 }
  E :=
    { pos := by decide
      inj := fun a b _ => Subsingleton.elim a b
      src := fun r hr => by
        cases record_source hX.tma.2.2.1 hr with
        | init _ _ ha => exact .init ha
        | inval _ he _ => exact (hN.inval _ _ ⟨_, he⟩).elim
        | @arrive g j pc tx cnt rel sc hid he ha =>
          obtain ⟨hg, rfl, rfl, rfl, -⟩ := hS.empty_arrive (Frame.lt_of_get hX he) he
          exact .arrive hid ⟨0, hg⟩ he ha
        | wait hid he ha => exact .poll hid he ha
        | tensor _ he hm _ => exact ((hS.no_tensor (c := c) (o := o) he).2 hm).elim
        | increment _ he _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
        | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
        | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
        | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
        | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
      init := hI.initFirst hB hX hb c (.storeEmpty o)
      noInval := objects_noInval hX.tma.2.2.1 (fun e m => hN.inval e m) _
      parity := fun he => (hS.empty_poll (Frame.lt_of_get hX he) he).2.2.1
      δ_le := le_refl 1 }
  gateP he := (hS.full_arrive (Frame.lt_of_get hX he) he).2.2.2.2.2
  gateC he := (hS.empty_arrive (Frame.lt_of_get hX he) he).2.2.2.2
  spins := hN.spins
  acqF he := (hS.full_poll (Frame.lt_of_get hX he) he).2.2 rfl
  acqE he := (hS.empty_poll (Frame.lt_of_get hX he) he).2.2.2 rfl
  cta a _ := sameCta_thr hb hc (by have := a.isLt; omega) (by decide)

/-- **The full hand-off**: the store leader's poll of `storeFull o` with `q` earlier successful
ones synchronizes with every compute thread's arrival with `q` earlier ones. -/
theorem full_handoff {c : Nat} (hc : c < L.grid) (o : Fin 2) :
    MbarRing.UnitHandoff L X ((Bar.storeFull o).loc L c) (fun g => ∃ a, g = computeThread L c a)
      (fun h => ∃ _ : Fin 1, h = storeLeader L c) 0 :=
  (hS.unitRing hI hB hN hX hb hc o).full_handoff hX

/-- **The empty hand-off**: a compute thread's poll of `storeEmpty o` with `q + 1` earlier
successful ones synchronizes with the store leader's arrival with `q` earlier ones. -/
theorem empty_handoff {c : Nat} (hc : c < L.grid) (o : Fin 2) :
    MbarRing.UnitHandoff L X ((Bar.storeEmpty o).loc L c)
      (fun g => ∃ _ : Fin 1, g = storeLeader L c) (fun h => ∃ a, h = computeThread L c a) 1 :=
  (hS.unitRing hI hB hN hX hb hc o).empty_handoff hX

/-- **No record of `storeFull o` has a fault.** -/
theorem full_faultFree {c : Nat} (hc : c < L.grid) (o : Fin 2) :
    ∀ r ∈ X.objects ((Bar.storeFull o).loc L c), r.fault = none := by
  have R := hS.unitRing hI hB hN hX hb hc o
  have hg : MbarRing.Unit.Gated L K A X ((Bar.storeFull o).loc L c) 128 (computeThread L c) 0 :=
    MbarRing.Unit.Gate.gated (R.fullGate hX)
  exact R.F.fault_free hX @hg

/-- **No record of `storeEmpty o` has a fault.** -/
theorem empty_faultFree {c : Nat} (hc : c < L.grid) (o : Fin 2) :
    ∀ r ∈ X.objects ((Bar.storeEmpty o).loc L c), r.fault = none := by
  have R := hS.unitRing hI hB hN hX hb hc o
  have hg : MbarRing.Unit.Gated L K A X ((Bar.storeEmpty o).loc L c) 1
      (fun _ => storeLeader L c) 1 :=
    fun {a _ _ _} he hpos => MbarRing.Unit.Gate.gated (R.emptyGate hX) (a := a) he hpos
  exact R.E.fault_free hX @hg

/-- **Who the store leader blocked at `storeFull o` waits for** (for progress). -/
theorem full_blocked {c : Nat} (hc : c < L.grid) (o : Fin 2) {before : State}
    (hst : stateBefore (X.objects ((Bar.storeFull o).loc L c))
      (X.objects ((Bar.storeFull o).loc L c)).length = some before)
    (hpar : before.phase % 2 =
      okPolls ((Bar.storeFull o).loc L c) (X.tr (storeLeader L c)) % 2) :
    before.phase = okPolls ((Bar.storeFull o).loc L c) (X.tr (storeLeader L c)) ∧
      ∃ a, (X.objects ((Bar.storeFull o).loc L c)).countP
        (MbarRing.Unit.unitsOf (computeThread L c a)) = before.phase := by
  have R := hS.unitRing hI hB hN hX hb hc o
  have h := (R.fullGate hX).blocked hX ⟨0, rfl⟩ hst (by rw [Nat.add_zero]; exact hpar)
  rwa [Nat.add_zero] at h

/-- **Who a compute thread blocked at `storeEmpty o` waits for** (for progress). -/
theorem empty_blocked {c : Nat} (hc : c < L.grid) (o : Fin 2) (ga : Fin 128) {before : State}
    (hst : stateBefore (X.objects ((Bar.storeEmpty o).loc L c))
      (X.objects ((Bar.storeEmpty o).loc L c)).length = some before)
    (hpar : before.phase % 2 =
      (okPolls ((Bar.storeEmpty o).loc L c) (X.tr (computeThread L c ga)) + 1) % 2) :
    before.phase + 1 = okPolls ((Bar.storeEmpty o).loc L c) (X.tr (computeThread L c ga)) ∧
      (X.objects ((Bar.storeEmpty o).loc L c)).countP
        (MbarRing.Unit.unitsOf (storeLeader L c)) = before.phase := by
  have R := hS.unitRing hI hB hN hX hb hc o
  obtain ⟨h1, -, h2⟩ := (R.emptyGate hX).blocked hX ⟨ga, rfl⟩ hst hpar
  exact ⟨h1, h2⟩

/-- **Publication of the output buffer** (proxy fence 2914). A compute thread's access of the
output buffer of stage `o` with `j` earlier arrivals on `storeFull o` is visible to every
asynchronous operation the store leader issues after more than `j` successful polls of
`storeFull o`, at every byte of the buffer the operation covers. -/
theorem publish_output {c : Nat} (hc : c < L.grid) (o : Fin 2) {i k j : Nat} {a : Acc}
    {w : Bool} {p : Part} {l : Loc} (ga : Fin 128) (hacc : X.Access (computeThread L c ga, i) a w)
    (hal : a.Covers l) (hl : InOutput L c o.val l)
    (hj : arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c ga)).take i) ≤ j)
    (hk : k < (X.tr (storeLeader L c)).length)
    (hpolls : j + 1 ≤ okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k))
    (hcov : AsyncCovers X (storeLeader L c, k) p l) :
    modelCausality L X l (.thread (computeThread L c ga, i)) (.async (storeLeader L c, k) p) := by
  have hdiv := computeThread_div (L := L) (c := c) hb ga
  refine Staging.publish_of_unit (hS.full_handoff hI hB hN hX hb hc o) ⟨ga, rfl⟩ ⟨0, rfl⟩
    (sameCta_thr hb hc (by have := ga.isLt; omega) (by decide)) hacc hj
    (fun e pce tx cnt rel sc hie he => ?_) hk hpolls hl.1 (by rw [hdiv]; exact hl.2.1) hcov
  refine hS.out_fence (computeThread_lt hb hc ga) hacc hal (o := o) (by rw [hdiv]; exact hl) hie
    (by rw [hdiv]; exact he)

/-- **Release of the output buffer** (`cp.async.bulk.wait_group.read` at 3093). The source
reads of a store the store leader issues with `j` earlier arrivals on `storeEmpty o` are visible
to a compute thread's access after more than `j + 1` successful polls of `storeEmpty o`. -/
theorem release_output {c : Nat} (hc : c < L.grid) (o : Fin 2) {k i j pc addr x y z : Nat}
    {sp : TensorStore.Spec} {l : Loc} (ga : Fin 128)
    (hi : X.get (storeLeader L c, k) = some ⟨pc, .tensorStore addr sp⟩)
    (hrl : TensorStore.readLoc sp x y z = some l) (hl : InOutput L c o.val l)
    (hj : arrivals ((Bar.storeEmpty o).loc L c) ((X.tr (storeLeader L c)).take k) ≤ j)
    (hlen : i < (X.tr (computeThread L c ga)).length)
    (hpolls : j + 1 + 1 ≤
      okPolls ((Bar.storeEmpty o).loc L c) ((X.tr (computeThread L c ga)).take i))
    (hcov : AsyncCovers X (storeLeader L c, k) (.read (.store x y z)) l) :
    modelCausality L X l (.async (storeLeader L c, k) (.read (.store x y z)))
      (.thread (computeThread L c ga, i)) :=
  Staging.release_of_unit hX (hS.empty_handoff hI hB hN hX hb hc o) ⟨0, rfl⟩ ⟨ga, rfl⟩ hi hj
    (fun _ _ _ _ _ _ hke he => hS.store_wait hi hrl hl hke he) hlen hpolls hcov

end

end StoreFacts

end PTX.Kernels.FlashKdaFwd.Protocol
