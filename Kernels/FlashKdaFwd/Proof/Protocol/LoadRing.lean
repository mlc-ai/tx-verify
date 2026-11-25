-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Init
public import Kernels.FlashKdaFwd.Proof.Protocol.Fences
public import Lemmas.Protocol.TmaSizedRing

@[expose] public section

/-! # The load pipeline: three stages, each a ring of kinds

The synchronization of the three input stages, with the proxy fences that belong to it
(`Fences.lean`). Stage `s < 3` (CUTLASS `PipelineTmaAsync<3>`) has the barrier `loadFull s`
(count 1) and the barrier `loadEmpty s` (count 128). Per tile the load leader polls
`loadEmpty s` (its first poll passes on the fresh barrier), arrives on `loadFull s` expecting
17984 bytes, and issues 70 asynchronous loads ("TMA" copies) that complete on `loadFull s`;
each of the 128 compute threads polls `loadFull s`, reads the input buffer, and arrives on
`loadEmpty s`. After its loop the load leader polls each `loadEmpty s` once more (the "tail").

**The library declaration** is `MbarRing.TmaSized.Stage` (`Lemmas/Protocol/TmaSizedRing.lean`):
a stage of a one-CTA TMA pipeline whose copies have several sizes. It was written for this
kernel, because the 70 loads of a tile have three sizes (68 of 256 bytes; the 17th, `beta`, of
64; the 66th, `g_total`, of 512; sum 17984) and the library's `MbarRing.TmaUnits` counts copies
of one size. `TmaSized` counts in units of 64 bytes: a tile has 281 units, `loadUnit u` is the
position (0 to 69) of the load that unit `u` belongs to, and the full barrier has `281 + 1`
kinds of item per use. The three facts about `loadUnit` that the library asks are checked by
evaluation (`loadUnit_lt`, `loadUnit_surj`, `loadBytes_eq`). The order "expect-tx arrival
before the loads" needs nothing: the stage's gates only ask that both follow the poll of the
empty barrier.

**What the thread layer exports** (`LoadFacts`): who arrives on, polls and issues to the six
barriers, with counts, bytes, parities and gates; and the proxy fence after the reads.

**What the library gives from them** (all proved below, no further premise):

* `fullSized`, `emptyObj`, `stage`: the two barriers of a stage are a `TmaSized.Obj` and a
  `Unit.Obj`, and the stage is a `TmaSized.Stage`; `kring` is its ring of kinds
  (`MbarRing.KRing … 1 128 (281 + 1)`).
* `full_observes_copy`: a compute thread's poll of `loadFull s` with `u` earlier successful
  ones observed the completion of each of the 70 loads of use `u` (`WaitObserves`); this is
  what makes the loaded bytes visible to the thread's reads and what the shared-memory
  lifetime rule asks for.
* `empty_handoff` (`MbarRing.UnitHandoff`, offset 1): the load leader's poll of `loadEmpty s`
  with `q + 1` earlier successful ones (a poll of the loop or of the tail) synchronizes with
  every compute thread's arrival with `q` earlier ones.
* `full_faultFree`, `empty_faultFree`: no record of the six barriers has a fault.
* `publish_input`: a compute thread's read of the input buffer is visible to the loads of every
  later use of the stage (`Staging.publish_of_unit`, proxy fence 2914).
* `full_blocked` (for progress): a compute thread whose next poll of `loadFull s` fails waits
  for the load leader's arrival of that use or for a load of that use not yet issued.
* `empty_blocked` (for progress): the load leader blocked at a poll of `loadEmpty s`, in its
  loop or in its tail, has polled successfully once more than the barrier's final phase, and
  some compute thread has exactly that phase's number of counted arrivals on the barrier. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 20000

/-! ### The 70 loads of a tile in units of 64 bytes -/

/-- The position, among the 70 loads of a tile, of the load that unit `u` belongs to: 16 loads
of `v` (4 units each), `beta` (1 unit), 48 loads of the three row arrays (4 units each),
`g_total` (8 units), 2 loads of `INV` and 2 of `Mqk` (4 units each). -/
def loadUnit (u : Fin 281) : Nat :=
  if u.val < 64 then u.val / 4 else if u.val = 64 then 16
  else if u.val < 257 then 17 + (u.val - 65) / 4
  else if u.val < 265 then 65 else 66 + (u.val - 265) / 4

/-- The bytes the load at position `i` of a tile moves. -/
def loadBytes (i : Nat) : Nat := if i = 16 then 64 else if i = 65 then 512 else 256

/-- Every unit belongs to one of the 70 loads. -/
theorem loadUnit_lt : ∀ u, loadUnit u < 70 := by decide +kernel

/-- Every load has a unit. -/
theorem loadUnit_surj : ∀ i : Fin 70, ∃ u, loadUnit u = i.val := by decide +kernel

/-- A load moves 64 bytes per unit. -/
theorem loadBytes_eq :
    ∀ i : Fin 70, loadBytes i.val = 64 * MbarRing.TmaSized.wt loadUnit i.val := by
  decide +kernel

/-- **Thread-layer facts about the load pipeline.** -/
structure LoadFacts (L : Launch) (X : Execution) : Prop where
  /-- An arrival on `loadFull s` is the load leader's: one release arrival expecting 17984
  bytes, after more successful polls of `loadEmpty s` than its earlier arrivals. -/
  full_arrive : ∀ {g i pc tx cnt c : Nat} {s : Fin 3} {rel : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .arrive ((Bar.loadFull s).loc L c) tx cnt rel sc⟩ →
      g = loadLeader L c ∧ tx = 17984 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadFull s).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.loadEmpty s).loc L c) ((X.tr g).take i)
  /-- A load that completes on `loadFull s` is the load leader's; the load with `q` earlier
  ones on the barrier is the load at position `q % 70` of use `q / 70`: it moves
  `loadBytes (q % 70)` bytes and follows `q / 70 + 1` successful polls of `loadEmpty s` and
  `q / 70 + 1` arrivals on `loadFull s` (the expect-tx arrival of a tile precedes its loads). -/
  full_issue : ∀ {g i pc al c : Nat} {s : Fin 3} {sp : TensorCopy.Spec}, g < L.threads →
    X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = (Bar.loadFull s).loc L c →
      g = loadLeader L c ∧
      TensorTransfer.bytes sp.descriptor =
        loadBytes (((X.tr g).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) % 70) ∧
      ((X.tr g).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70 + 1 ≤
        okPolls ((Bar.loadEmpty s).loc L c) ((X.tr g).take i) ∧
      ((X.tr g).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) / 70 + 1 ≤
        arrivals ((Bar.loadFull s).loc L c) ((X.tr g).take i)
  /-- A poll of `loadFull s` is a compute thread's of the barrier's CTA, with the parity of its
  earlier successful polls; a successful one acquires. -/
  full_poll : ∀ {g i pc p c : Nat} {s : Fin 3} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, i) = some ⟨pc, .wait ((Bar.loadFull s).loc L c) p ok acq sc⟩ →
      g % L.block < 128 ∧ c = g / L.block ∧
      p % 2 = okPolls ((Bar.loadFull s).loc L c) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true)
  /-- An arrival on `loadEmpty s` is a compute thread's of the barrier's CTA: one release
  arrival without transaction bytes, after more successful polls of `loadFull s` than its
  earlier arrivals on `loadEmpty s`. -/
  empty_arrive : ∀ {g i pc tx cnt c : Nat} {s : Fin 3} {rel : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .arrive ((Bar.loadEmpty s).loc L c) tx cnt rel sc⟩ →
      g % L.block < 128 ∧ c = g / L.block ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadEmpty s).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.loadFull s).loc L c) ((X.tr g).take i)
  /-- A poll of `loadEmpty s` is the load leader's (in its loop or in its tail), with the parity
  of its earlier successful polls plus one; a successful one acquires. -/
  empty_poll : ∀ {g i pc p c : Nat} {s : Fin 3} {ok acq : Bool} {sc : MbarScope},
    g < L.threads →
    X.get (g, i) = some ⟨pc, .wait ((Bar.loadEmpty s).loc L c) p ok acq sc⟩ →
      g = loadLeader L c ∧
      p % 2 = (okPolls ((Bar.loadEmpty s).loc L c) ((X.tr g).take i) + 1) % 2 ∧
      (ok = true → acq = true)
  /-- No asynchronous load completes on `loadEmpty s`. -/
  no_tensor_empty : ∀ {i : EvId} {pc a c : Nat} {s : Fin 3} {sp : TensorCopy.Spec},
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ (Bar.loadEmpty s).loc L c
  /-- Between a compute thread's access of the input buffer of stage `s` and its next arrival
  on `loadEmpty s` the thread executes a `fence.proxy.async.shared::cta`. -/
  in_fence : ∀ {g i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {s : Fin 3}
    {rel : Bool} {sc : MbarScope}, g < L.threads → X.Access (g, i) a w → a.Covers l →
    InInput L (g / L.block) s.val l → i < e →
    X.get (g, e) = some ⟨pce, .arrive ((Bar.loadEmpty s).loc L (g / L.block)) tx cnt rel sc⟩ →
      ∃ f pcf, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

namespace LoadFacts

section
variable (hLd : LoadFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
  (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include hLd hI hB hN hX hb

/-- **The empty barrier of stage `s` is a unit object** of the 128 compute threads, polled with
offset 1. -/
theorem emptyObj (c : Nat) (s : Fin 3) :
    MbarRing.Unit.Obj X ((Bar.loadEmpty s).loc L c) 128 (computeThread L c) 1 where
  pos := by decide
  inj := computeThread_inj L c
  src := fun r hr => by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (hN.inval _ _ ⟨_, he⟩).elim
    | @arrive g j pc tx cnt rel sc hid he ha =>
      obtain ⟨hw, hc', rfl, rfl, rfl, -⟩ := hLd.empty_arrive (Frame.lt_of_get hX he) he
      exact .arrive hid (computeThread_of hb hw hc') he ha
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact (hLd.no_tensor_empty (c := c) (s := s) he hm).elim
    | increment _ he _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
    | arriveOn _ he _ _ _ => exact (hN.asyncArrive _ _ _ ⟨_, he⟩).elim
    | bulk _ he _ _ _ => exact (hN.copy _ _ ⟨_, he⟩).elim
    | commit _ he _ _ => exact (hN.commit _ _ ⟨_, he⟩).elim
    | clc _ he _ _ _ => exact (hN.clc _ _ _ ⟨_, he⟩).elim
  init := hI.initFirst hB hX hb c (.loadEmpty s)
  noInval := objects_noInval hX.tma.2.2.1 (fun e m => hN.inval e m) _
  parity := fun he => (hLd.empty_poll (Frame.lt_of_get hX he) he).2.1
  δ_le := le_refl 1

/-- **The full barrier of stage `s` is fed by the load leader**: per use one arrival expecting
`64 * 281` bytes and 70 loads, the load at position `i` moving `64 * wt loadUnit i` bytes. -/
theorem fullSized (c : Nat) (s : Fin 3) :
    MbarRing.TmaSized.Obj X ((Bar.loadFull s).loc L c) (loadLeader L c) 70 64 loadUnit := by
  refine ⟨hI.initFirst hB hX hb c (.loadFull s),
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
      obtain ⟨rfl, rfl, rfl, -⟩ := hLd.full_arrive (Frame.lt_of_get hX he) he
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
      obtain ⟨rfl, hbytes, -⟩ := hLd.full_issue (Frame.lt_of_get hX he) he hm
      refine ⟨j, pc, al, sp, hid, he, hm, ?_⟩
      rw [ha', hbytes]
      exact loadBytes_eq ⟨_ % 70, Nat.mod_lt _ (by decide)⟩

/-- **Stage `s` of the load pipeline of CTA `c` is a stage of a one-CTA TMA pipeline.** -/
theorem stage {c : Nat} (hc : c < L.grid) (s : Fin 3) :
    MbarRing.TmaSized.Stage L K X ((Bar.loadFull s).loc L c) ((Bar.loadEmpty s).loc L c)
      (loadLeader L c) 70 64 loadUnit 128 (computeThread L c) where
  full := hLd.fullSized hI hB hN hX hb c s
  empty := hLd.emptyObj hI hB hN hX hb c s
  unit_pos := by decide
  n_pos := by decide
  spins := hN.spins
  parF := fun _ _ _ _ _ _ he =>
    (Nat.add_zero _).symm ▸ (hLd.full_poll (Frame.lt_of_get hX he) he).2.2.1
  gateA := fun he => (hLd.full_arrive (Frame.lt_of_get hX he) he).2.2.2.2
  gateI := fun he hm => (hLd.full_issue (Frame.lt_of_get hX he) he hm).2.2.1
  gateC := fun he => (hLd.empty_arrive (Frame.lt_of_get hX he) he).2.2.2.2.2
  acqE := fun he => (hLd.empty_poll (Frame.lt_of_get hX he) he).2.2 rfl
  cta := fun b => sameCta_thr hb hc (by have := b.isLt; omega) (by decide)

/-- **Stage `s` of the load pipeline of CTA `c` as a ring of kinds.** -/
def kring {c : Nat} (hc : c < L.grid) (s : Fin 3) : MbarRing.KRing L K X 1 128 (281 + 1) :=
  (hLd.stage hI hB hN hX hb hc s).ring hX

/-- **A compute thread's poll of `loadFull s` observed every load of its use.** The poll with
`u` earlier successful ones observed the completion of the load with `70 u + r` earlier ones on
the barrier, for each `r < 70`. -/
theorem full_observes_copy {c : Nat} (hc : c < L.grid) (s : Fin 3) (b : Fin 128)
    {j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (computeThread L c b, j) =
      some ⟨pc, .wait ((Bar.loadFull s).loc L c) p true acq sc⟩)
    (hu : okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c b)).take j) = u)
    (r : Fin 70) :
    WaitObserves X
      (.async (loadLeader L c,
        nthEv X (issuesTo ((Bar.loadFull s).loc L c)) (loadLeader L c) (70 * u + r.val))
        (.notify .load))
      (computeThread L c b, j) ((Bar.loadFull s).loc L c) acq sc := by
  obtain ⟨v, hv⟩ := loadUnit_surj r
  have h := (hLd.stage hI hB hN hX hb hc s).copy_observed hX b he hu v
  rwa [hv] at h

/-- **The empty hand-off**: the load leader's poll of `loadEmpty s` with `q + 1` earlier
successful ones synchronizes with every compute thread's arrival with `q` earlier ones. -/
theorem empty_handoff {c : Nat} (hc : c < L.grid) (s : Fin 3) :
    MbarRing.UnitHandoff L X ((Bar.loadEmpty s).loc L c)
      (fun g => ∃ a, g = computeThread L c a) (fun h => h = loadLeader L c) 1 :=
  (hLd.stage hI hB hN hX hb hc s).empty_handoff hX

/-- **No record of `loadEmpty s` has a fault.** -/
theorem empty_faultFree {c : Nat} (hc : c < L.grid) (s : Fin 3) :
    ∀ r ∈ X.objects ((Bar.loadEmpty s).loc L c), r.fault = none :=
  (hLd.stage hI hB hN hX hb hc s).empty_faultFree hX

/-- **No record of `loadFull s` has a fault.** -/
theorem full_faultFree {c : Nat} (hc : c < L.grid) (s : Fin 3) :
    ∀ r ∈ X.objects ((Bar.loadFull s).loc L c), r.fault = none :=
  (hLd.stage hI hB hN hX hb hc s).full_faultFree hX 0 (by decide) (by decide)

/-- **A compute thread blocked at `loadFull s` waits for the load leader** (for progress). When
the final phase of `loadFull s` has the parity of compute thread `b`'s successful polls, so
that its next poll fails, and no load of the execution is unfinished, the phase is the number of
those polls, and the load leader has made at most that many arrivals on the barrier or has
issued fewer than 70 loads of that use. -/
theorem full_blocked {c : Nat} (hc : c < L.grid) (s : Fin 3)
    (hno : ¬ Descent.Obl L X .tensor) (b : Fin 128) {st : State}
    (hst : stateBefore (X.objects ((Bar.loadFull s).loc L c))
      (X.objects ((Bar.loadFull s).loc L c)).length = some st)
    (hpar : st.phase % 2 =
      okPolls ((Bar.loadFull s).loc L c) (X.tr (computeThread L c b)) % 2) :
    st.phase = okPolls ((Bar.loadFull s).loc L c) (X.tr (computeThread L c b)) ∧
      (arrivals ((Bar.loadFull s).loc L c) (X.tr (loadLeader L c)) ≤ st.phase ∨
        (X.tr (loadLeader L c)).countP (issuesTo ((Bar.loadFull s).loc L c)) <
          70 * (st.phase + 1)) :=
  (hLd.stage hI hB hN hX hb hc s).full_blocked hX loadUnit_lt
    (hLd.full_faultFree hI hB hN hX hb hc s) hno b hst hpar

/-- **Who the load leader blocked at `loadEmpty s` waits for** (for progress): when the final
phase of `loadEmpty s` has the parity that the leader's next poll (of its loop or of its tail)
does not find, the leader has polled successfully once more than that phase, and some compute
thread has exactly that phase's number of counted arrivals on the barrier. -/
theorem empty_blocked {c : Nat} (hc : c < L.grid) (s : Fin 3) {before : State}
    (hst : stateBefore (X.objects ((Bar.loadEmpty s).loc L c))
      (X.objects ((Bar.loadEmpty s).loc L c)).length = some before)
    (hpar : before.phase % 2 =
      (okPolls ((Bar.loadEmpty s).loc L c) (X.tr (loadLeader L c)) + 1) % 2) :
    before.phase + 1 = okPolls ((Bar.loadEmpty s).loc L c) (X.tr (loadLeader L c)) ∧
      ∃ b, (X.objects ((Bar.loadEmpty s).loc L c)).countP
        (MbarRing.Unit.unitsOf (computeThread L c b)) = before.phase :=
  (hLd.stage hI hB hN hX hb hc s).empty_blocked hX hst hpar

/-- **Publication of the input buffer** (proxy fence 2914). A compute thread's access of the
input buffer of stage `s` with `j` earlier arrivals on `loadEmpty s` is visible to every
asynchronous operation the load leader issues after more than `j + 1` successful polls of
`loadEmpty s`, i.e. to the loads of the later uses of the stage. -/
theorem publish_input {c : Nat} (hc : c < L.grid) (s : Fin 3)
    {i k j : Nat} {a : Acc} {w : Bool} {p : Part} {l : Loc} (ga : Fin 128)
    (hacc : X.Access (computeThread L c ga, i) a w) (hal : a.Covers l)
    (hl : InInput L c s.val l)
    (hj : arrivals ((Bar.loadEmpty s).loc L c) ((X.tr (computeThread L c ga)).take i) ≤ j)
    (hk : k < (X.tr (loadLeader L c)).length)
    (hpolls : j + 1 + 1 ≤
      okPolls ((Bar.loadEmpty s).loc L c) ((X.tr (loadLeader L c)).take k))
    (hcov : AsyncCovers X (loadLeader L c, k) p l) :
    modelCausality L X l (.thread (computeThread L c ga, i)) (.async (loadLeader L c, k) p) := by
  have hdiv := computeThread_div (L := L) (c := c) hb ga
  refine Staging.publish_of_unit (hLd.empty_handoff hI hB hN hX hb hc s) ⟨ga, rfl⟩ rfl
    (sameCta_thr hb hc (by have := ga.isLt; omega) (by decide)) hacc hj
    (fun e pce tx cnt rel sc hie he => ?_) hk hpolls hl.1 (by rw [hdiv]; exact hl.2.1) hcov
  refine hLd.in_fence (computeThread_lt hb hc ga) hacc hal (s := s) (by rw [hdiv]; exact hl) hie
    (by rw [hdiv]; exact he)

end

end LoadFacts

end

end PTX.Kernels.FlashKdaFwd.Protocol
