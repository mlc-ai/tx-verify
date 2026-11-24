-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObjectSource
public import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

/-! # A kernel's mbarrier table and its initialization

A proof tool. A kernel's mbarriers form a table (`BarTable`): each barrier of the table lies at
a fixed shared offset of every CTA (`BarTable.loc`), distinct barriers at distinct offsets
(`BarTable.loc_inj`), and is initialized with a valid arrival count. The kernel names who
initializes each barrier by an initializer map `init : B → Nat → EvId` (barrier `b` of CTA
`cta` is initialized by event `init b cta`): the map's events are the only initializations of
the barrier, with its count (`BarTable.InitSites`).

An object whose initializations are all one event `e`, with count `c` (`init_source_of_site`),
and whose every other record is issued by an event that `e` happens before, has `e`'s
initialization, once it exists, as its first record, which succeeds (`first_record_of_site`, by
`init_record_success_of_unique_init`). The table forms (`BarTable.init_source`,
`BarTable.first_record`) apply this to `init b cta`. Two records of an object with one reference
are one (`Consistent.record_eq`), and a poll record names its poll event
(`Consistent.poll_record`). -/

namespace PTX

open AsyncCopy MBarrier

noncomputable section

/-- A kernel's table of mbarriers: a barrier `b` of the table (`Valid b`) lies at shared offset
`off b` of every CTA and is initialized with arrival count `count b`. -/
structure BarTable (B : Type) where
  Valid : B → Prop
  off : B → Nat
  count : B → Nat
  /-- Distinct barriers of the table lie at distinct offsets. -/
  off_inj : ∀ {b b' : B}, Valid b → Valid b' → off b = off b' → b = b'
  /-- Every count is a valid arrival count. -/
  count_valid : ∀ {b : B}, Valid b → validCount (count b)

namespace BarTable

variable {B : Type} (T : BarTable B)

/-- Barrier `b` of CTA `cta`. -/
def loc (L : Launch) (cta : Nat) (b : B) : Loc := ⟨.shared, cta, L.sharedBase + T.off b⟩

variable {T}

/-- A barrier location names its barrier and CTA. -/
theorem loc_inj {L : Launch} {b b' : B} {c c' : Nat} (h : T.Valid b) (h' : T.Valid b')
    (he : T.loc L c b = T.loc L c' b') : b = b' ∧ c = c' := by
  simp only [loc, Loc.mk.injEq, true_and] at he
  exact ⟨T.off_inj h h' (by omega), he.1⟩

variable (T)

/-- **The initializer map.** Every initialization of barrier `b` of CTA `cta` is the event
`init b cta`, with the barrier's count. -/
def InitSites (L : Launch) (X : Execution) (init : B → Nat → EvId) : Prop :=
  ∀ (b : B) cta i pc n, T.Valid b → X.get i = some ⟨pc, .mbInit (T.loc L cta b) n⟩ →
    i = init b cta ∧ n = T.count b

end BarTable

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- An initialization record of an object whose initializations are all event `e` with count
`c` is `e`'s, with count `c`. -/
theorem BarTable.init_source_of_site (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId} {c : Nat}
    (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit m n⟩ → i = e ∧ n = c)
    {s : Record Ref} (hs : s ∈ X.objects m) {n : Nat} (ha : s.action = .init n) :
    s.id = .thread e ∧ n = c ∧ X.MbInit e m n := by
  cases record_source hX.tma.2.2.1 hs with
  | @init g j pc c' hid he ha' =>
    rw [ha] at ha'
    cases ha'
    obtain ⟨rfl, rfl⟩ := hsite _ _ _ he
    exact ⟨hid, rfl, pc, he⟩
  | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | commit _ _ _ ha'
  | clc _ _ _ _ ha' | increment _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' =>
    rw [ha] at ha'; cases ha'

/-- **An object initialized once, before its other records, is initialized first, without
fault.** Event `e` initializes object `m` with count `c`, every initialization of `m` is `e`'s,
and every other record is issued by an event that `e` happens before. -/
theorem BarTable.first_record_of_site (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId}
    {c : Nat} (hinit : X.MbInit e m c) (hcount : validCount c)
    (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit m n⟩ → i = e ∧ n = c)
    (hpub : ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) → baseCausality L X e s.id.issuer) :
    ∃ r0, (X.objects m)[0]? = some r0 ∧ r0.id = .thread e ∧ r0.action = .init c ∧
      r0.fault = none := by
  obtain ⟨r0, h0, hid, ha, hf, -⟩ := init_record_success_of_unique_init hX hinit hcount
    (fun _ s _ hs ha => (init_source_of_site hX hsite (List.mem_of_getElem? hs) ha).1)
    (fun _ s hs hnon => object_not_before_of_baseCausality hX ⟨c, hinit⟩
        (hpub s (List.mem_of_getElem? hs) hnon))
  exact ⟨r0, h0, hid, ha, hf⟩

/-- Two records of an object with the same reference are the same record. -/
theorem Consistent.record_eq (hX : Consistent L K A mem0 X) {m : Loc} {r q : Record Ref}
    (hr : r ∈ X.objects m) (hq : q ∈ X.objects m) (hid : r.id = q.id) : r = q :=
  List.inj_on_of_nodup_map (hX.tma.2.2.1 m).1.1 hr hq hid

/-- A thread's poll record on an object names its poll event. -/
theorem Consistent.poll_record (hX : Consistent L K A mem0 X) {m : Loc} {r : Record Ref}
    (hr : r ∈ X.objects m) {g j p : Nat} {ok : Bool} (hid : r.id = .thread (g, j))
    (ha : r.action = .pollParity p ok) :
    ∃ pc acq sc, X.get (g, j) = some ⟨pc, .wait m p ok acq sc⟩ := by
  cases record_source hX.tma.2.2.1 hr with
  | wait hid' he ha' =>
    rw [hid] at hid'
    cases hid'
    rw [ha] at ha'
    cases ha'
    exact ⟨_, _, _, he⟩
  | inval _ _ ha' | init _ _ ha' | arrive _ _ ha' | tensor _ _ _ ha' | commit _ _ _ ha'
  | increment _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | clc _ _ _ _ ha' =>
    rw [ha] at ha'; cases ha'

namespace BarTable

variable {B : Type} {T : BarTable B} {init : B → Nat → EvId}

/-- An initialization record of a table barrier is its initializer's, with the barrier's
count. -/
theorem init_source (hX : Consistent L K A mem0 X) (hsite : T.InitSites L X init) {b : B}
    {cta : Nat} (hb : T.Valid b) {s : Record Ref} (hs : s ∈ X.objects (T.loc L cta b)) {n : Nat}
    (ha : s.action = .init n) :
    s.id = .thread (init b cta) ∧ n = T.count b ∧ X.MbInit (init b cta) (T.loc L cta b) n :=
  init_source_of_site hX (fun _ _ _ he => hsite b cta _ _ _ hb he) hs ha

/-- **The first record of a table barrier with a record is its initializer's successful
initialization**, once the initializer happens before the issue of every other record. -/
theorem first_record (hX : Consistent L K A mem0 X) (hsite : T.InitSites L X init) {b : B}
    {cta : Nat} (hb : T.Valid b)
    (hpub : ∀ s ∈ X.objects (T.loc L cta b), (∀ n, s.action ≠ .init n) →
      X.MbInit (init b cta) (T.loc L cta b) (T.count b) ∧ PTX.baseCausality L X
          (init b cta) s.id.issuer )
    {r : Record Ref} (hr : r ∈ X.objects (T.loc L cta b)) :
    ∃ r0, (X.objects (T.loc L cta b))[0]? = some r0 ∧ r0.id = .thread (init b cta) ∧
      r0.action = .init (T.count b) ∧ r0.fault = none := by
  have hsite' := fun i pc n (he : X.get i = some ⟨pc, .mbInit (T.loc L cta b) n⟩) =>
    hsite b cta i pc n hb he
  have hinit : X.MbInit (init b cta) (T.loc L cta b) (T.count b) := by
    by_cases hri : ∃ n, r.action = .init n
    · obtain ⟨n, hn⟩ := hri
      obtain ⟨-, rfl, hget⟩ := init_source_of_site hX hsite' hr hn
      exact hget
    · exact (hpub r hr fun n h => hri ⟨n, h⟩).1
  exact first_record_of_site hX hinit (T.count_valid hb) hsite'
    fun s hs hnon => (hpub s hs hnon).2

end BarTable

end
end PTX
