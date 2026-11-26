-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaSizedFault
public import Lemmas.Protocol.TmaSizedBlock
public import Lemmas.Protocol.KindRingGate
public import Lemmas.Protocol.UnitRing
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.UnitBlocker
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # A stage of a one-CTA TMA pipeline with copies of several sizes

A proof tool: the ring of one stage of a pipeline in the style of CUTLASS `PipelineTmaAsync`,
for one thread block. The stage has a *full* barrier `F` (arrival count 1) and an *empty* barrier
`E` (arrival count `nc`). Per use, one producer thread `y` polls `E`, arrives on `F` expecting
the use's bytes and issues the use's `n` tensor copies, which complete on `F` and may have
different sizes (`TmaSized.Obj`); each of the `nc` consumer threads `cons b` polls `F`, uses the
copied bytes and arrives on `E` (`MbarRing.Unit.Obj`, polled with offset 1: the producer's first
poll passes on the fresh barrier). The arrival may come before or after the copies of its use;
the tail polls a producer makes after its last use are ordinary polls of `E`.

`Stage` lists what the thread layer supplies: the two object descriptions, the parity of the
consumers' polls of `F`, the three gates (the producer's arrival and copies of use `u` follow
`u + 1` successful polls of `E`; a consumer's arrival of use `t` follows `t + 1` successful polls
of `F`), that the producer's successful polls of `E` acquire, that the threads are of one CTA,
and that every successful poll heads a canonical spin loop.

Results (`H : Stage …`):

* `Stage.ring`: the stage is a ring of kinds (`MbarRing.KRing … 1 nc (W + 1)`).
* `Stage.full_observes`, `Stage.copy_observed`: a consumer's successful poll of `F` with `u`
  earlier ones observed every item of use `u`, in particular the completion of each copy of
  use `u`.
* `Stage.empty_handoff`: the producer's successful poll of `E` with `q + 1` earlier ones
  synchronizes with every consumer's arrival with `q` earlier ones (`MbarRing.UnitHandoff`).
* `Stage.empty_faultFree`, `Stage.full_faultFree`: no record of either barrier has a fault.
  For `F` this is `TmaSized.Obj.fault_free`, whose two side conditions come from the ring
  (`Obj.fault_free_of_ring`, the argument of TmlFa4Fwd's `tma_fault` for `TmaUnits`).
* `Stage.emptyGate`, `Stage.empty_blocked` (for progress): the empty barrier is a gated unit
  object (`MbarRing.Unit.Gate`); when its final phase has the parity that the producer's next
  poll (of its loop or of its tail) does not find, the producer has polled successfully once
  more than that phase, and some consumer has exactly that phase's number of counted arrivals:
  it has not made the arrival the producer waits for.
* `Stage.full_blocked` (for progress): when the full barrier's final phase has the parity of a
  consumer's successful polls, so that the consumer's next poll fails, the final phase is the
  number of those polls and the producer is short of that use's arrival or of one of its
  copies (`TmaSized.Obj.short`). -/

namespace PTX.MbarRing.TmaSized

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {F E : Loc} {y n W U nc : Nat} {cp : Fin W → Nat} {cons : Fin nc → Nat}

/-- **The full barrier of a ring of kinds is fault-free**, when its items are those of a
`TmaSized.Obj` and the feeding thread's arrivals and copies of use `u` follow `u + 1` successful
polls of the empty barrier. -/
theorem Obj.fault_free_of_ring (hX : Consistent L K A mem0 X) (o : Obj X F y n U cp)
    (hU : 0 < U) (hW : 0 < W) (hn : 0 < n) (hfit : 2 * (U * W) ≤ limit)
    (R : KRing L K X 1 nc (W + 1)) (b0 : Fin nc) (hF : R.F = F) (hE : R.E = E)
    (hP : R.prod 0 = y) (hS : R.SF = S X F y n U cp)
    (gateA : ∀ {j pc tx c : Nat} {rel : Bool} {sc : MbarScope},
      X.get (y, j) = some ⟨pc, .arrive F tx c rel sc⟩ →
        arrivals F ((X.tr y).take j) + 1 ≤ okPolls E ((X.tr y).take j))
    (gateI : ∀ {j pc al : Nat} {sp : TensorCopy.Spec},
      X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = F →
        ((X.tr y).take j).countP (issuesTo F) / n + 1 ≤ okPolls E ((X.tr y).take j)) :
    ∀ r ∈ X.objects F, r.fault = none := by
  -- an event after `t + 1` polls of the empty barrier, `1 ≤ t`, whose path reaches the record
  have key : ∀ {k i t : Nat} {r : Record Ref}, (X.objects F)[k]? = some r →
      ((∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) →
      i < (X.tr y).length → 1 ≤ t → t + 1 ≤ okPolls E ((X.tr y).take i) →
      Relation.ReflTransGen (DepStep L K X) (.thread (y, i), false) (r.id, false) →
      ∃ kw w sw, kw < k ∧ (X.objects F)[kw]? = some w ∧ w.reply.waited = some true ∧
        stateBefore (X.objects F) kw = some sw ∧ t ≤ sw.phase := by
    intro k i t r hk hact hi ht hpoll hpath
    have hg' := R.gateF hX (a := 0) (i := i) (u := t - 1) (by rw [hP]; exact hi)
      (by rw [hE, hP, Nat.sub_add_cancel ht]; exact hpoll) b0
    rw [hP, hF] at hg'
    obtain ⟨pc, par, acq, sc, hw, hcnt⟩ := poll_of_path hg'
    obtain ⟨kw, w, sw, hkw, hwid, ⟨p', hwa⟩, hww, hsw, hge⟩ := poll_phase_ge_for_thread hX
      (Nat.zero_le 1) o.noInval (PairTmaRing.poll_clean hX o.init o.noInval)
      (fun he => by have := R.parF b0 (hF ▸ he); rw [hF] at this; exact this) hw
    refine ⟨kw, w, sw, ?_, hkw, hww, hsw, by omega⟩
    exact Unit.Gate.poll_before hX (hg'.trans_left hpath) hk rfl hkw hwid (by
      rcases hact with ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h, hwa] <;> simp)
  refine o.fault_free hX hU hW hfit ?_ ?_
  · intro k r x hk hid hact hpos
    rcases id hact with ⟨c, tx, ha⟩ | ⟨b, ha⟩
    · obtain ⟨-, rfl, j, pc, rel, sc, hj, he⟩ := o.arrive hk ha
      have hx0 : x.1 = 0 := by
        by_contra hne
        obtain ⟨u, hu⟩ := Fin.exists_succ_eq.mpr hne
        rw [hj, ← hu, it_succ] at hid
        cases hid
      have hj2 : j = nthEv X (arrivesOn F) y x.2 := by
        rw [hj, hx0, it_zero] at hid
        exact (Prod.mk.inj (Ref.thread.inj hid)).2
      have hc : arrivals F ((X.tr y).take j) = x.2 := by
        unfold arrivals
        rw [hj2]
        exact (nthEv_spec_of_get (hj2 ▸ he)).2
      have hb := gateA he
      rw [hc] at hb
      exact key hk hact (len_of_get he) hpos hb (by rw [hj])
    · obtain ⟨j, pc, al, sp, hj, he, hm, -⟩ := o.copy hk ha
      have hx0 : x.1 ≠ 0 := by
        intro h0
        rw [hj, h0, it_zero] at hid
        cases hid
      obtain ⟨u, hu⟩ := Fin.exists_succ_eq.mpr hx0
      have hj2 : j = nthEv X (issuesTo F) y (n * x.2 + cp u) := by
        rw [hj, ← hu, it_succ] at hid
        injection hid with h1
        exact (Prod.mk.inj h1).2
      have hc : ((X.tr y).take j).countP (issuesTo F) = n * x.2 + cp u := by
        rw [hj2]
        exact (nthEv_spec_of_get (hj2 ▸ he)).2
      have hb := gateI he hm
      rw [hc, Nat.mul_add_div hn] at hb
      have hb' : x.2 + 1 ≤ okPolls E ((X.tr y).take j) :=
        le_trans (Nat.add_le_add_right (Nat.le_add_right _ _) 1) hb
      refine key hk hact (len_of_get he) hpos hb' ?_
      have hpr := object_record_present hX.tma (List.mem_of_getElem? hk)
      rw [hj] at hpr ⊢
      obtain ⟨ob, hob, hn'⟩ := id hpr
      obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity hob hn'
      exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := K)
        (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
          (c := (.async (y, j) (.notify .load), false))
          (.inr ⟨rfl, rfl, rfl, rfl, hwp, hpr⟩))).to_reflTransGen
  · intro t hnot x hx
    by_contra hlt
    have hr := R.reachF hX (x := x) (by rw [hS]; exact hx) b0 (j := t) (by omega)
    have hu : t < okPolls R.F (X.tr (R.cons b0)) := Poll.nth_present.mp (present_of_path hr)
    have := (R.full_observes hX hu 0).1
    rw [hS] at this
    exact hnot this

/-- **What the thread layer supplies for one stage** (module docstring). -/
structure Stage (L : Launch) (K : Kernel) (X : Execution) (F E : Loc) (y n U : Nat)
    (cp : Fin W → Nat) (nc : Nat) (cons : Fin nc → Nat) : Prop where
  /-- The full barrier's updates are the producer's arrivals and copies. -/
  full : Obj X F y n U cp
  /-- The empty barrier's updates are the consumers' unit arrivals; it is polled with offset 1. -/
  empty : Unit.Obj X E nc cons 1
  unit_pos : 0 < U
  n_pos : 0 < n
  /-- Every successful poll is the poll of a canonical spin (DEP-CANONICAL-SPIN). -/
  spins : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
    ∃ exit, K.CanonicalSpin pc exit
  /-- A consumer's successful poll of `F` has the parity of its earlier successful polls. -/
  parF : ∀ (b : Fin nc) {k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (cons b, k) = some ⟨pc, .wait F p true acq sc⟩ →
      p % 2 = (okPolls F ((X.tr (cons b)).take k) + 0) % 2
  /-- The producer's arrival of use `u` follows `u + 1` successful polls of `E`. -/
  gateA : ∀ {j pc tx c : Nat} {rel : Bool} {sc : MbarScope},
    X.get (y, j) = some ⟨pc, .arrive F tx c rel sc⟩ →
      arrivals F ((X.tr y).take j) + 1 ≤ okPolls E ((X.tr y).take j)
  /-- The producer's copy with `q` earlier ones follows `q / n + 1` successful polls of `E`. -/
  gateI : ∀ {j pc al : Nat} {sp : TensorCopy.Spec},
    X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = F →
      ((X.tr y).take j).countP (issuesTo F) / n + 1 ≤ okPolls E ((X.tr y).take j)
  /-- A consumer's arrival of use `t` follows `t + 1` successful polls of `F`. -/
  gateC : ∀ {b : Fin nc} {i pc : Nat} {sc : MbarScope},
    X.get (cons b, i) = some ⟨pc, .arrive E 0 1 true sc⟩ →
      arrivals E ((X.tr (cons b)).take i) + 1 ≤ okPolls F ((X.tr (cons b)).take i)
  /-- The producer's successful polls of `E` acquire. -/
  acqE : ∀ {j pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (y, j) = some ⟨pc, .wait E p true acq sc⟩ → acq = true
  /-- The consumers and the producer are threads of one CTA. -/
  cta : ∀ b, SameCta L (cons b) y

namespace Stage

/-- The consumers' arrivals on the empty barrier as counted units. -/
theorem empty_counted (H : Stage L K X F E y n U cp nc cons) :
    Counted X E (Unit.S X E cons) (fun b t => .thread (Unit.it X E cons b t)) where
  record := fun x hx => by
    obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := H.empty.S_rec hx
    exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
  init := ⟨nc, H.empty.init⟩
  noInval := H.empty.noInval

/-- An item of use `u` of the full barrier is issued after `u + 1` successful polls of `E`. -/
theorem polF (H : Stage L K X F E y n U cp nc cons) :
    ∀ x ∈ S X F y n U cp, ∃ i, op X F y n cp x.1 x.2 = (y, i) ∧ i < (X.tr y).length ∧
      x.2 + 1 ≤ okPolls E ((X.tr y).take i) := by
  intro x hx
  obtain ⟨-, h0, h1⟩ := H.full.source hx
  refine ⟨(op X F y n cp x.1 x.2).2, rfl, ?_⟩
  by_cases hz : x.1 = 0
  · obtain ⟨⟨pc, rel, sc, he⟩, hu⟩ := h0 hz
    have hg := H.gateA (j := (op X F y n cp x.1 x.2).2) he
    exact ⟨len_of_get he, by omega⟩
  · obtain ⟨⟨pc, al, sp, he, hm⟩, hu⟩ := h1 hz
    have hg := H.gateI (j := (op X F y n cp x.1 x.2).2) he hm
    rw [hu, Nat.mul_add_div H.n_pos] at hg
    exact ⟨len_of_get he, le_trans (Nat.add_le_add_right (Nat.le_add_right _ _) 1) hg⟩

/-- A consumer's arrival of use `t` on the empty barrier follows `t + 1` successful polls of
`F`. -/
theorem polE (H : Stage L K X F E y n U cp nc cons) :
    ∀ z ∈ Unit.S X E cons, ∃ i, Unit.it X E cons z.1 z.2 = (cons z.1, i) ∧
      i < (X.tr (cons z.1)).length ∧ z.2 + 1 ≤ okPolls F ((X.tr (cons z.1)).take i) := by
  intro z hz
  obtain ⟨-, ⟨pc, sc, he⟩, hu⟩ := H.empty.S_rec hz
  refine ⟨_, rfl, len_of_get he, ?_⟩
  have hg := H.gateC he
  have hu' : arrivals E ((X.tr (cons z.1)).take (nthEv X (arrivesOn E) (cons z.1) z.2)) = z.2 :=
    hu
  omega

/-- **The stage as a ring of kinds.** -/
def ring (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X) :
    KRing L K X 1 nc (W + 1) where
  F := F
  E := E
  prod := fun _ => y
  cons := cons
  ownF := fun _ => 0
  opF := op X F y n cp
  itF := it X F y n cp
  cm := fun b t => Unit.it X E cons b t
  note := fun b t => .thread (Unit.it X E cons b t)
  SF := S X F y n U cp
  SE := Unit.S X E cons
  cover := fun _ => ⟨0, Subsingleton.elim _ _⟩
  cF := H.full.counted
  cE := H.empty_counted
  spins := H.spins
  parF := fun b _ _ _ _ _ he => H.parF b he
  parE := fun _ _ _ _ _ _ he => H.empty.parity he
  fullF := fun b _ hj => H.full.card_phase hX H.unit_pos (δ := 0) (Nat.zero_le 1)
    (H.full.counted.alt hX fun he => H.parF b he) (Nat.zero_le _) hj
  fullE := fun _ _ hn hj => H.empty.card_phase hX hn hj
  polF := H.polF
  polE := H.polE
  issueF := fun _ hx => H.full.issue hX hx
  issueE := fun _ _ => .refl

/-- **A consumer's poll of the full barrier observed every item of its use.** -/
theorem full_observes (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X)
    (b : Fin nc) {j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (cons b, j) = some ⟨pc, .wait F p true acq sc⟩)
    (hu : okPolls F ((X.tr (cons b)).take j) = u) (k : Fin (W + 1)) :
    (k, u) ∈ S X F y n U cp ∧ WaitObserves X (it X F y n cp k u) (cons b, j) F acq sc := by
  have hlt : u < okPolls F (X.tr (cons b)) := by
    rw [← hu]; exact PairTmaRing.okPolls_lt_of_get he
  obtain ⟨hS, hub⟩ := (H.ring hX).full_observes hX (b := b) hlt k
  have hjn : MbarRing.Poll.nth X F (cons b) u = j := by
    rw [← hu]; exact MbarRing.Poll.nth_eq he
  have hub' : UpdateBeforeWait (X.objects F) (it X F y n cp k u)
      (.thread (cons b, MbarRing.Poll.nth X F (cons b) u)) := hub
  rw [hjn] at hub'
  exact ⟨hS, ⟨pc, p, he⟩, hub'⟩

/-- **A consumer's poll of the full barrier observed every copy of its use**: the poll with `u`
earlier successful ones observed the completion of the copy with `n u + i` earlier ones, for
each position `i` that has a unit. -/
theorem copy_observed (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X)
    (b : Fin nc) {j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (cons b, j) = some ⟨pc, .wait F p true acq sc⟩)
    (hu : okPolls F ((X.tr (cons b)).take j) = u) (v : Fin W) :
    WaitObserves X (.async (y, nthEv X (issuesTo F) y (n * u + cp v)) (.notify .load))
      (cons b, j) F acq sc := by
  have h := (H.full_observes hX b he hu v.succ).2
  rwa [it_succ] at h

/-- **The empty hand-off**: the producer's successful poll of the empty barrier with `q + 1`
earlier ones synchronizes with every consumer's arrival with `q` earlier ones. -/
theorem empty_handoff (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X) :
    MbarRing.UnitHandoff L X E (fun g => ∃ b, g = cons b) (fun h => h = y) 1 := by
  intro h j pc p acq sc q hh he hq g ⟨b, hgb⟩
  have hh' : y = h := hh.symm
  subst hh' hgb
  have hacq := H.acqE he
  subst hacq
  have hjn : MbarRing.Poll.nth X E y (q + 1) = j := by
    rw [← hq]; exact MbarRing.Poll.nth_eq he
  have hn : q + 1 < okPolls E (X.tr y) := by
    rw [← hq]; exact PairTmaRing.okPolls_lt_of_get he
  obtain ⟨hS, hu⟩ := (H.ring hX).empty_observes hX (a := 0) (u := q) hn b
  have hu' : UpdateBeforeWait (X.objects E) (.thread (Unit.it X E cons b q))
      (.thread (y, MbarRing.Poll.nth X E y (q + 1))) := hu
  rw [hjn] at hu'
  have hS' : (b, q) ∈ Unit.S X E cons := hS
  exact ⟨_, Unit.Ring.syncs H.empty hS' he hu' (H.cta b)⟩

/-- **No record of the empty barrier has a fault.** -/
theorem empty_faultFree (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X) :
    ∀ r ∈ X.objects E, r.fault = none := by
  refine H.empty.fault_free hX (Unit.gated_of_paths (K := K) (A := A)
    fun {a i pc sc} he hpos => ⟨y, ?_⟩)
  have hg := H.gateC he
  exact (H.ring hX).gateE hX (b := a) (i := i)
    (t := arrivals E ((X.tr (cons a)).take i) - 1 + 1) (len_of_get he)
    (by rw [Nat.sub_add_cancel hpos]; exact hg) (by omega) 0

/-- **No record of the full barrier has a fault.** -/
theorem full_faultFree (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X)
    (b0 : Fin nc) (hW : 0 < W) (hfit : 2 * (U * W) ≤ limit) :
    ∀ r ∈ X.objects F, r.fault = none :=
  H.full.fault_free_of_ring hX H.unit_pos hW H.n_pos hfit (H.ring hX) b0 rfl rfl rfl rfl
    H.gateA H.gateI

/-- **The empty barrier is gated by the producer's polls**: a consumer's arrival of use `t` is
guarded by its poll of the full barrier for use `t`, which observed the producer's arrival of
use `t`, which the producer's poll of the empty barrier with `t` earlier ones guards. -/
theorem emptyGate (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X) :
    Unit.Gate L K A X E nc cons 1 (fun h => h = y) (fun _ h => h = y) where
  toObj := H.empty
  cover _ hh := ⟨⟨0, H.empty.pos⟩, hh⟩
  partner _ := ⟨y, rfl⟩
  gate := by
    intro b h i pc sc hh he _
    have hh' : y = h := hh.symm
    subst hh'
    set t := arrivals E ((X.tr (cons b)).take i) with ht
    have hgc := H.gateC he
    have hn : t < okPolls F (X.tr (cons b)) := by
      have := MbarRing.Poll.okPolls_mono F (X.tr (cons b))
        (show i ≤ (X.tr (cons b)).length from (len_of_get he).le)
      rw [List.take_length] at this
      omega
    obtain ⟨hx, hobs⟩ := ((H.ring hX).ring hX).observes_full hX.depAcyclic (b := b) (j := t)
      (Poll.nth_present.mpr hn) (0 : Fin (W + 1))
    have g2 : Resumes K X (cons b, MbarRing.Poll.nth X F (cons b) t) (cons b, i) :=
      MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
    obtain ⟨i', hop, hi', hp⟩ := H.polF ((0 : Fin (W + 1)), t) hx
    obtain ⟨j, pcw, p, acq, scw, -, hw, hjq⟩ := MbarRing.Poll.exists_nth (X := X) (m := E)
      (g := y) (k := i') (n := t) (by omega)
    have g1 : Resumes K X (y, MbarRing.Poll.nth X E y t) (y, i') :=
      MbarRing.Poll.guard (m := E) (g := y) (n := t) H.spins hi' (by omega)
    have hnth : MbarRing.Poll.nth X E y t = j := by
      rw [← hjq, MbarRing.Poll.nth_eq hw]
    rw [hnth] at g1
    have hobs' : Witness L X (.thread (y, i'))
        (cons b, MbarRing.Poll.nth X F (cons b) t) := by
      have h0 : it X F y n cp 0 t = .thread (y, i') := by
        have hop' : op X F y n cp 0 t = (y, i') := hop
        simp [it, hop']
      rw [← h0]
      exact hobs
    refine ⟨j, pcw, p, acq, scw, hw, by omega, ?_⟩
    exact ((Relation.TransGen.single (DepStep.of_resumes L g1)).tail
      (DepStep.of_witness L hobs')).tail (DepStep.of_resumes L g2)
  acq := by
    intro h j pc p acq sc hh he
    have hh' : y = h := hh.symm
    subst hh'
    exact H.acqE he
  cta b h := by
    rintro rfl
    exact H.cta b

/-- **The producer blocked at the empty barrier waits for a consumer.** When the final phase of
the empty barrier has the parity that the producer's next poll does not find, the producer has
polled successfully once more than that phase, and some consumer has exactly that phase's
number of counted arrivals. -/
theorem empty_blocked (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X)
    {before : State}
    (hst : stateBefore (X.objects E) (X.objects E).length = some before)
    (hpar : before.phase % 2 = (okPolls E (X.tr y) + 1) % 2) :
    before.phase + 1 = okPolls E (X.tr y) ∧
      ∃ b, (X.objects E).countP (Unit.unitsOf (cons b)) = before.phase :=
  (H.emptyGate hX).blocked hX rfl hst hpar

/-- **A consumer blocked at the full barrier waits for the producer.** When the final phase of
the full barrier has the parity of consumer `b`'s successful polls, the phase is the number of
those polls, and the producer has made at most that many arrivals or has not issued all the
copies of that use. -/
theorem full_blocked (H : Stage L K X F E y n U cp nc cons) (hX : Consistent L K A mem0 X)
    (hcp : ∀ u, cp u < n) (hff : ∀ r ∈ X.objects F, r.fault = none)
    (hno : ¬ Descent.Obl L X .tensor) (b : Fin nc) {st : State}
    (hst : stateBefore (X.objects F) (X.objects F).length = some st)
    (hpar : st.phase % 2 = okPolls F (X.tr (cons b)) % 2) :
    st.phase = okPolls F (X.tr (cons b)) ∧
      (arrivals F (X.tr y) ≤ st.phase ∨
        (X.tr y).countP (issuesTo F) < n * (st.phase + 1)) := by
  have hle : st.phase ≤ okPolls F (X.tr (cons b)) + 1 :=
    (H.ring hX).F_phase_le hX (κ := {0}) (by simp)
      (by rw [Finset.card_singleton]; exact H.full.init) H.full.incr
      (fun hr _ ha => (H.full.arrive hr ha).1)
      (fun hr hf ha => by
        obtain ⟨t, hS, hid⟩ := H.full.arrive_item hr hf ha
        exact ⟨(0, t), hS, Finset.mem_singleton_self _, hid⟩) b hst
  have hph : st.phase = okPolls F (X.tr (cons b)) := (H.ring hX).F_phase hX b hst hle hpar
  refine ⟨hph, H.full.short hX H.n_pos H.unit_pos hcp hff hno hst fun x hx => ?_⟩
  rw [hph]
  exact (H.ring hX).F_use hX (x := x) hx b

end Stage

end
end PTX.MbarRing.TmaSized
