-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.MbarInit
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Flow.ElectActor
public import Lemmas.Protocol.PollPhase

@[expose] public section

/-! # The records of the ring objects

Facts every ring protocol uses about the records of the ring objects. A thread's event is
fired from a state its machine follows; a polling thread runs a role on that role's warp.
Every ring object is initialized by its CTA's thread 0, once, with the object's count: the
barrier table's initializer map (`init_sites`, `Bar.init`); every other record of the object is
issued by a role event of the object's cluster, which that initialization happens before. So the
initialization is the object's first record and succeeds (`first_record`, by
`BarTable.first_record`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event's index is within its thread's trace. -/
theorem idx_le {g k : Nat} {e : Event} (he : X.get (g, k) = some e) : k ≤ (X.tr g).length :=
  (List.getElem?_eq_some_iff.mp he).1.le

/-- The state a thread's wait fires from, in a tracked execution. -/
theorem wait_role (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g k : Nat}
    {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e) {m : Loc} {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    ∃ r, Frame.stateAt (code L) X g k = some (some (.inr r)) ∧ roleWarp (g % L.block / 32) r := by
  obtain ⟨τ, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by rintro pc f rfl; cases hk)
  cases τ with
  | inl q => exact (ht.prologue_no_wait hg he hσ _ _ _ _ _ hk).elim
  | inr r => exact ⟨r, hσ, ht.role_warp hg (List.getElem?_eq_some_iff.mp he).1.le hσ⟩

/-- Two threads of one warp of a CTA, in roles with the same election site, that use
mbarriers are one: only the warp's elected lane goes on. -/
theorem elected_unique (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g h j k pc : Nat} {e f : Event} {r r' : Prologue.Role} (hcta : g / L.block = h / L.block)
    (hw : g % L.block / 32 = h % L.block / 32) (he : X.get (g, j) = some e)
    (hf : X.get (h, k) = some f) (hσ : Frame.stateAt (code L) X g j = some (some (.inr r)))
    (hσ' : Frame.stateAt (code L) X h k = some (some (.inr r'))) (hpc : r.electPc = some pc)
    (hpc' : r'.electPc = some pc) (hke : ObjectKind e.kind) (hkf : ObjectKind f.kind) :
    g = h := by
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  obtain ⟨j1, i1, l1, -, hE1, hl1⟩ := ht.elected hg he hσ hpc hke
  obtain ⟨j2, i2, l2, -, hE2, hl2⟩ := ht.elected hh hf hσ' hpc' hkf
  exact selected_elect_thread_unique hX.elect hE1 hE2 ⟨⟨hg, hh, hcta⟩, hw⟩ hl1 hl2

/-- Two threads of one MMA warp of a CTA that poll are one. -/
theorem mma_unique (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g h j k : Nat}
    {e f : Event} (hcta : g / L.block = h / L.block)
    (hw : g % L.block / 32 = h % L.block / 32) (hwg : g % L.block / 32 = 8 ∨ g % L.block / 32 = 9)
    (he : X.get (g, j) = some e) (hf : X.get (h, k) = some f) {m m' : Loc} {p p' : Nat}
    {ok ok' acq acq' : Bool} {sc sc' : MbarScope} (hke : e.kind = .wait m p ok acq sc)
    (hkf : f.kind = .wait m' p' ok' acq' sc') : g = h := by
  have mma : ∀ {x i : Nat} {ev : Event} {mb : Loc} {q : Nat} {o a' : Bool} {c : MbarScope},
      x < L.threads → (x % L.block / 32 = 8 ∨ x % L.block / 32 = 9) →
      X.get (x, i) = some ev → ev.kind = .wait mb q o a' c →
      ∃ mm, Frame.stateAt (code L) X x i = some (some (.inr (.mma mm))) := by
    intro x i ev mb q o a' c hx hw' hev hk
    obtain ⟨r, hσ, hr⟩ := wait_role hX ht hx hev hk
    cases r with
    | mma mm => exact ⟨mm, hσ⟩
    | loader l => simp only [roleWarp] at hr; omega
    | sched sd => simp only [roleWarp] at hr; omega
    | cons c => simp only [roleWarp] at hr; omega
  obtain ⟨m1, h1⟩ := mma (Frame.lt_of_get hX he) hwg he hke
  obtain ⟨m2, h2⟩ := mma (Frame.lt_of_get hX hf) (hw ▸ hwg) hf hkf
  exact elected_unique hX ht hcta hw he hf h1 h2 rfl rfl (by rw [hke]; trivial)
    (by rw [hkf]; trivial)

/-- No thread issues `cp.async.mbarrier.arrive`: the instruction at no site of the code is one. -/
theorem no_asyncArrive (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g k pc : Nat} {m : Loc} {noinc : Bool}
    (he : X.get (g, k) = some ⟨pc, .asyncArrive m noinc⟩) : False := by
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site ht.sound hX he hσ
  have hk := site_kindOp d hc
  cases hob : objectOp ins.op
  · exact notObject_of_op hob hf trivial
  rcases eventTmpl_opTmpl (A := Prod) (L := L) (g := g) (t := t) ins.op with ⟨f, hub⟩ | hev
  · rw [hub] at hf
    simp [Fires] at hf
  generalize eventTmpl Prod L g t ins.op = tm at hf hev
  generalize nextKind d = nk at hk
  cases hop : ins.op <;> rw [hop] at hob hk hev <;>
    simp only [objectOp, Bool.false_eq_true] at hob <;>
    simp only [OpEv] at hev
  all_goals first
    | (cases nk <;> simp [kindOp] at hk; done)
    | (obtain ⟨_, _, _, rfl⟩ := hev; simp [Fires] at hf)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := hev; simp [Fires] at hf)
    | (obtain ⟨_, _, _, rfl, -⟩ := hev; simp [Fires] at hf)

/-- No mbarrier record is a pending-count increment: only `cp.async.mbarrier.arrive` without
`.noinc` records one, and no thread issues it. -/
theorem no_increment (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {m : Loc}
    {r : Record Ref} (hr : r ∈ X.objects m) (ha : r.action = .increment) : False := by
  cases record_source hX.tma.2.2.1 hr with
  | increment _ he _ => exact no_asyncArrive hX ht he
  | init _ _ ha' | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | tensor _ _ _ ha'
  | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha' | clc _ _ _ _ ha' =>
    rw [ha] at ha'; cases ha'

/-- No mbarrier history counts a pending-count increment (`no_increment`). -/
theorem incrementsBefore_zero (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (m : Loc) : incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun _ hr ha => no_increment hX ht hr ha

/-- Each kind of use of a ring barrier is by a role. -/
theorem Bar.role_of {L : Launch} {g : Nat} {d : ThreadD} {b : Bar}
    (h : b.pollBy L g d ∨ b.arriveBy L g d ∨ b.commitBy d ∨ b.copyBy d) : ∃ r, d = .inr r := by
  obtain ⟨rg, s, f⟩ := b
  cases rg <;> cases f <;> simp only [Bar.pollBy, Bar.arriveBy, Bar.commitBy, Bar.copyBy] at h <;>
    aesop

/-- A cancellation request completing on ring barrier `b` in CTA `cta` is one that the
barrier's table allows, completing on `b` in the requester's CTA and its cluster's targets. -/
theorem clc_source (ht : ThreadFacts L X) {g j : Nat} {e : Event} {d : ThreadD}
    (hg : g < L.threads) (he : X.get (g, j) = some e)
    (hσ : Frame.stateAt (code L) X g j = some (some d))
    {sp : Clc.Spec} {tg : List Nat} (hk : e.kind = .clcIssue sp tg) {b : Bar} {cta c : Nat}
    (hm : b.loc L cta = { sp.mbar with cta := c }) (hb : b.Valid) (htg : c ∈ tg) :
    b.clcBy L g d ∧ sp.mbar = b.loc L (g / L.block) ∧ cta = c ∧ c / 2 = g / L.block / 2 := by
  obtain ⟨b', hb', hby, hmb, -, hcl⟩ := (ht.ring_event hg he hσ).clc _ _ hk
  have h' : ({ sp.mbar with cta := c } : Loc) = b'.loc L c := by rw [hmb]; rfl
  obtain ⟨rfl, hcc⟩ := Bar.loc_inj hb hb' (hm.trans h')
  exact ⟨hby, hmb, hcc, hcl c htg⟩

/-- The issuing event of a record of a ring barrier that is not its initialization is a role
event of the barrier's cluster. -/
theorem issuer_role (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {b : Bar}
    {cta : Nat} (hb : b.Valid) {r : Record Ref} (hr : r ∈ X.objects (b.loc L cta))
    (hnoninit : ∀ n, r.action ≠ .init n) :
    ∃ g j ev role, r.id.issuer = (g, j) ∧ g < L.threads ∧ X.get (g, j) = some ev ∧
      Frame.stateAt (code L) X g j = some (some (.inr role)) ∧ cta / 2 = g / L.block / 2 := by
  have role : ∀ {g j : Nat} {ev : Event} {d : ThreadD}, g < L.threads → X.get (g, j) = some ev →
      Frame.stateAt (code L) X g j = some (some d) →
      (b.pollBy L g d ∨ b.arriveBy L g d ∨ b.commitBy d ∨ b.copyBy d) → cta / 2 = g / L.block / 2 →
      ∃ g' j' ev role, (g, j) = (g', j') ∧ g' < L.threads ∧ X.get (g', j') = some ev ∧
        Frame.stateAt (code L) X g' j' = some (some (.inr role)) ∧ cta / 2 = g' / L.block / 2 := by
    intro g j ev d hg he hσ hby hc
    obtain ⟨r, rfl⟩ := Bar.role_of hby
    exact ⟨g, j, ev, r, rfl, hg, he, hσ, hc⟩
  cases record_source hX.tma.2.2.1 hr with
  | inval _ he _ => exact (no_inval hX ht ⟨_, he⟩).elim
  | init hid he ha => exact absurd ha (hnoninit _)
  | increment _ he _ => exact (no_asyncArrive hX ht he).elim
  | @arriveOn i _ _ _ _ he _ _ _ => exact (no_asyncArrive hX ht (g := i.1) (k := i.2) he).elim
  | @arrive g j pc tx c rel sc hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, rfl, -, -⟩ := (ht.ring_event hg he hσ).arrive _ _ _ _ _ _ rfl hb
    rw [hid]
    exact role hg he hσ (.inr (.inl hby)) (by simp only [Bar.arriveCta]; split <;> omega)
  | @wait g j pc p ok acq sc hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, rfl⟩ := (ht.ring_event hg he hσ).wait _ _ _ _ _ _ rfl hb
    rw [hid]
    exact role hg he hσ (.inl hby) rfl
  | @tensor i pc a sp hid he hm ha =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, rfl, -⟩ := (ht.ring_event hg he hσ).tensor _ _ _ _ rfl hm hb
    rw [hid]
    exact role hg he hσ (.inr (.inr (.inr hby))) (by omega)
  | @bulk i pc src hid he =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact absurd rfl ((ht.ring_event hg he hσ).copy src)
  | @commit i pc sp rank hid he htg ha =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hev, hrank, rfl, -⟩ := (ht.ring_event hg he hσ).commit _ _ _ _ rfl htg hb
    rw [hid]
    exact role hg he hσ (.inr (.inr (.inl hby))) (by omega)
  | @clc i pc sp tg c hid he hm htg hca =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, -, rfl, hcl⟩ := clc_source ht hg he hσ rfl hm hb htg
    obtain ⟨sd, rfl⟩ : ∃ sd, d = .inr (.sched sd) := by
      obtain ⟨rg, s, f⟩ := b
      cases rg <;> cases f <;> simp only [Bar.clcBy] at hby
      exact hby.1
    rw [hid]
    exact ⟨g, j, _, _, rfl, hg, he, hσ, hcl⟩

/-- CTA thread 0 initializes every ring barrier, at the event its offset gives, with its count
(`RingEvent.init`): the initializer map of the barrier table. -/
theorem init_sites (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    Bar.table.InitSites L X (Bar.init L) := by
  rintro b cta ⟨g, j⟩ pc n hb he
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨h0, hcta, hj, hc⟩ := (ht.ring_event hg he hσ).init _ _ _ rfl hb
  have hg0 : g = cta * L.block := by
    rw [hcta]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h0)).symm
  subst hg0 hj
  exact ⟨rfl, hc⟩

/-- An initialization record of a ring barrier is its CTA thread 0's initialization, with the
barrier's count. -/
theorem init_source (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {b : Bar}
    {cta : Nat} (hb : b.Valid) {s : Record Ref} (hs : s ∈ X.objects (b.loc L cta)) {n : Nat}
    (ha : s.action = .init n) :
    s.id = .thread (cta * L.block, b.initIndex) ∧ n = b.count ∧
      ∃ pc, X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) n⟩ :=
  BarTable.init_source (T := Bar.table) hX (init_sites hX ht) hb hs ha

/-- The first record of a ring barrier that has any record is its CTA thread 0's successful
initialization: the initialization is published to the issuer of every other record
(`ThreadFacts.ring_initialized`). -/
theorem first_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} {cta : Nat} (hb : b.Valid) {r : Record Ref}
    (hr : r ∈ X.objects (b.loc L cta)) :
    ∃ r0, (X.objects (b.loc L cta))[0]? = some r0 ∧
      r0.id = .thread (cta * L.block, b.initIndex) ∧
      r0.action = .init b.count ∧ r0.fault = none := by
  have hcl := hpre.cluster
  refine BarTable.first_record (T := Bar.table) hX (init_sites hX ht) hb (fun s hs hnon => ?_) hr
  obtain ⟨g, j, ev, role, hiss, hg, he, hσ, hc⟩ := issuer_role hX ht hb hs hnon
  have hcta : cta < L.grid := by
    have := cta_lt hpre hg
    have := hpre.grid
    have := hpre.block
    omega
  obtain ⟨pc, hget, hp⟩ := ht.ring_initialized hg he hσ hb hcta
    (by rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre]; exact hc)
  exact ⟨⟨pc, hget⟩, hiss ▸ hp⟩

/-- How a record of ring barrier `b` in CTA `cta` arises: CTA thread 0's initialization, a
poll, an arrival, a copy completion or a cancellation response of a thread that the barrier's
table allows, or the notification of an allowed thread's commit. -/
inductive BarSource (L : Launch) (X : Execution) (b : Bar) (cta : Nat) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n) (hn : n = b.count)
      (hid : r.id = .thread (cta * L.block, b.initIndex))
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} {d : ThreadD}
      (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait (b.loc L cta) p ok acq sc⟩)
      (ha : r.action = .pollParity p ok) (hσ : Frame.stateAt (code L) X g j = some (some d))
      (hby : b.pollBy L g d) (hcta : cta = g / L.block)
  | arrive {g j pc : Nat} {rel : Bool} {sc : MbarScope} {d : ThreadD}
      (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .arrive (b.loc L cta) b.arriveTx 1 rel sc⟩)
      (ha : r.action = .arrive 1 b.arriveTx) (hσ : Frame.stateAt (code L) X g j = some (some d))
      (hby : b.arriveBy L g d) (hcta : cta = b.arriveCta L g)
  | copy {g j pc a : Nat} {sp : TensorCopy.Spec} {d : ThreadD}
      (hid : r.id = .async (g, j) (.notify .load))
      (he : X.get (g, j) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = b.loc L cta)
      (ha : r.action = .completeTx b.completeBytes)
      (hσ : Frame.stateAt (code L) X g j = some (some d))
      (hby : b.copyBy d) (hcta : cta = 2 * (g / L.block / 2))
  | notify {g j pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16} {d : ThreadD}
      (hid : r.id = .async (g, j) (.tcNotify rank))
      (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
      (ht : TcCommit.target sp rank = some (b.loc L cta)) (ha : r.action = .arrive 1 0)
      (hσ : Frame.stateAt (code L) X g j = some (some d)) (hby : b.commitBy d)
      (hlead : g / L.block % 2 = 0)
      (hrank : rank.val < 2) (hcta : cta = g / L.block + rank.val)
      (hmb : sp.mbar = b.loc L (g / L.block))
  | clc {g j pc c : Nat} {sp : Clc.Spec} {tg : List Nat} {d : ThreadD}
      (hid : r.id = .async (g, j) (.notify (.cta c)))
      (he : X.get (g, j) = some ⟨pc, .clcIssue sp tg⟩) (htg : c ∈ tg)
      (ha : r.action = .completeTx b.completeBytes)
      (hσ : Frame.stateAt (code L) X g j = some (some d))
      (hby : b.clcBy L g d) (hmb : sp.mbar = b.loc L (g / L.block)) (hcta : cta = c)
      (hcl : c / 2 = g / L.block / 2)

/-- Every record of a ring barrier arises as `BarSource` says. -/
theorem bar_source (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {b : Bar}
    {cta : Nat} (hb : b.Valid) {r : Record Ref} (hr : r ∈ X.objects (b.loc L cta)) :
    BarSource L X b cta r := by
  cases record_source hX.tma.2.2.1 hr with
  | inval _ he _ => exact (no_inval hX ht ⟨_, he⟩).elim
  | increment _ he _ => exact (no_asyncArrive hX ht he).elim
  | @arriveOn i _ _ _ _ he _ _ _ => exact (no_asyncArrive hX ht (g := i.1) (k := i.2) he).elim
  | @init g j pc n hid he ha =>
    obtain ⟨hid', hn, -⟩ := init_source hX ht hb hr ha
    exact .init ha hn hid'
  | @wait g j pc p ok acq sc hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hcta⟩ := (ht.ring_event hg he hσ).wait _ _ _ _ _ _ rfl hb
    exact .poll hid he ha hσ hby hcta
  | @arrive g j pc tx c rel sc hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hcta, rfl, rfl⟩ := (ht.ring_event hg he hσ).arrive _ _ _ _ _ _ rfl hb
    exact .arrive hid he ha hσ hby hcta
  | @tensor i pc a sp hid he hm ha =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hcta, hbytes⟩ := (ht.ring_event hg he hσ).tensor _ _ _ _ rfl hm hb
    exact .copy hid he hm (by rw [ha, hbytes]) hσ hby hcta
  | @bulk i pc src hid he =>
    obtain ⟨g, j⟩ := i
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact absurd rfl ((ht.ring_event (Frame.lt_of_get hX he) he hσ).copy src)
  | @commit i pc sp rank hid he htg ha =>
    obtain ⟨g, j⟩ := i
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hlead, hrank, hcta, hmb⟩ := (ht.ring_event hg he hσ).commit _ _ _ _ rfl htg hb
    exact .notify hid he htg ha hσ hby hlead hrank hcta hmb
  | @clc i pc sp tg c hid he hm htg hca =>
    obtain ⟨g, j⟩ := i
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    obtain ⟨hby, hmb, hcta, hcl⟩ := clc_source ht (Frame.lt_of_get hX he) he hσ rfl hm hb htg
    have hbytes : b.completeBytes = 16 := by
      obtain ⟨rg, s, f⟩ := b
      cases rg <;> cases f <;> simp only [Bar.clcBy] at hby
      rfl
    exact .clc hid he htg (by rw [hca, hbytes]) hσ hby hmb hcta hcl

end
end PTX.Kernels.Fp16Gemm8192.Proof
