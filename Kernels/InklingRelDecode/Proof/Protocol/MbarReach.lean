-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.MbarRoute

@[expose] public section

/-!
# The reuse paths of the S/P/O handshake

`Notify.Reach` of `s_ready b` and `o_done` for every softmax thread, and `Unit.Reach` of `p_ready b`
for every MMA lane (the premises of `SO.s_observes`, `SOOdone.o_observes`, `SO.p_handoff`), proved
together by well-founded induction along the dependency order (`DepStep`, DEP-ORDER) over the
issues of the thread events and their commit notifications, as FA4's `TmemReach` does for its
four objects (`reach_all`): at each node, the paths that end there (`Reach3`), knowing them at
every node that precedes it.

* **`s_ready`** (`stepS`): the notification of the commit with `t` earlier ones follows each
  softmax thread's poll for a use `j < t`: the poll precedes thread 0's arrival on `p_ready` of
  use `j` through the meeting at `bar.sync 0, 128` (`Route.soft_bar`, `Bar128Witness`), the
  committing lane's poll of `p_ready` for use `j` observes that arrival (`contentP`, the
  induction hypothesis), and the poll precedes the commit.
* **`o_done`** (`stepO`): the same with block `j + 1`: the softmax thread's `o_done` poll of
  iteration `j + 1` precedes the arrival of block `j + 1` on `p_ready ((j + 1) % 2)`, the lane's
  poll of it precedes the commit of block `t ≥ j + 1`.
* **`p_ready`** (`stepP`): thread 0's arrival of use `u` follows each lane's poll for a use
  `j < u`: the lane's poll precedes the commit of `s_ready b` of use `u` (a lane other than the
  committing one through the election, `Route.lane_commit`), whose notification the thread's
  own `s_ready` poll for use `u` observes (`contentS`, the induction hypothesis) before the
  arrival.

The statements are for every recorded notification and every arrival event, not only the counted
ones (as FA4's `TmemReachGates`), so they also give the gates of the objects (`sGated`, `oGated`,
`pGated`), from which no record of these barriers faults (`MbarGate`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (Facts CommitBar sObj oObj pObj)

noncomputable section

/-- **The premises of one CTA's handshake**: the execution, the record sources (`SO.Facts`), the
parity of the `o_done` polls, and the thread-layer order facts (`Route`). -/
structure Ctx (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution)
    (c cm p0 : Nat) (Soft Mma : Nat → Prop) : Prop where
  cons : Consistent L K A mem0 X
  facts : Facts L X c cm p0
  route : Route L K X c cm p0 Soft Mma
  bar : Bar128Witness L X
  /-- A successful poll of `o_done` has the parity of the thread's earlier ones
  (`SOOdone.o_parity_of_runs`). -/
  opar : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait (oDone L c) p true acq sc⟩ →
      p % 2 = (okPolls (oDone L c) ((X.tr g).take k) + 0) % 2

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {c cm p0 : Nat} {Soft Mma : Nat → Prop}

/-- The paths of `p_ready` that end at node `n`: thread 0's arrival of use `u` follows each MMA
lane's poll for a use `j < u`. -/
def RPn (L : Launch) (K : Kernel) (X : Execution) (c p0 : Nat) (Mma : Nat → Prop)
    (n : Ref × Bool) : Prop :=
  ∀ b, b < 2 → ∀ {i pc : Nat} {sc : MbarScope},
    X.get (p0, i) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩ →
    n = (.thread (p0, i), false) → ∀ h, Mma h →
      ∀ j < arrivals (pReady L c b) ((X.tr p0).take i), Relation.TransGen (DepStep L K X)
        (.thread (h, MbarRing.Poll.nth X (pReady L c b) h j), true) n

/-- The paths of `s_ready` that end at node `n`. -/
def RSn (L : Launch) (K : Kernel) (X : Execution) (c : Nat) (Soft : Nat → Prop)
    (n : Ref × Bool) : Prop :=
  ∀ b, b < 2 → ∀ h, Soft h → ∀ (y : EvId) (rank : Fin 16),
    (∃ r ∈ X.objects (sReady L c b), r.id = .async y (.tcNotify rank)) →
    n = (.async y (.tcNotify rank), false) →
    ∀ j < ((X.tr y.1).take y.2).countP (commitsTo (sReady L c b)),
      Relation.TransGen (DepStep L K X)
        (.thread (h, MbarRing.Poll.nth X (sReady L c b) h j), true) n

/-- The paths of `o_done` that end at node `n`. -/
def ROn (L : Launch) (K : Kernel) (X : Execution) (c : Nat) (Soft : Nat → Prop)
    (n : Ref × Bool) : Prop :=
  ∀ h, Soft h → ∀ (y : EvId) (rank : Fin 16),
    (∃ r ∈ X.objects (oDone L c), r.id = .async y (.tcNotify rank)) →
    n = (.async y (.tcNotify rank), false) →
    ∀ j < ((X.tr y.1).take y.2).countP (commitsTo (oDone L c)),
      Relation.TransGen (DepStep L K X)
        (.thread (h, MbarRing.Poll.nth X (oDone L c) h j), true) n

/-- The paths of the three objects that end at node `n`. -/
def Reach3 (L : Launch) (K : Kernel) (X : Execution) (c p0 : Nat) (Soft Mma : Nat → Prop)
    (n : Ref × Bool) : Prop :=
  RPn L K X c p0 Mma n ∧ RSn L K X c Soft n ∧ ROn L K X c Soft n

/-- The induction hypothesis at node `n`. -/
def IH (L : Launch) (K : Kernel) (X : Execution) (c p0 : Nat) (Soft Mma : Nat → Prop)
    (n : Ref × Bool) : Prop :=
  ∀ p ∈ nodes L X, Relation.TransGen (DepStep L K X) p n → Reach3 L K X c p0 Soft Mma p

/-- **A softmax thread reaches thread 0's arrival.** Thread 0's arrival event `ia` on `p_ready b`,
of use `u`, is preceded in the dependency order by an event `a` of each softmax thread `h` (its
`bar.sync 0, 128` of the same ordinal), before which `h` made the polls of `s_ready b` and
`o_done` that `Route.soft_bar` counts. -/
theorem soft_rendezvous (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b ia pc : Nat}
    {sc : MbarScope} {h : Nat} (hb : b < 2) (hsoft : Soft h)
    (hga : X.get (p0, ia) = some ⟨pc, .arrive (pReady L c b) 0 1 true sc⟩) :
    ∃ a, a < (X.tr h).length ∧
      Relation.TransGen (DepStep L K X) (.thread (h, a), false) (.thread (p0, ia), false) ∧
      arrivals (pReady L c b) ((X.tr p0).take ia) + 1 ≤
        okPolls (sReady L c b) ((X.tr h).take a) ∧
      (1 ≤ 2 * arrivals (pReady L c b) ((X.tr p0).take ia) + b →
        2 * arrivals (pReady L c b) ((X.tr p0).take ia) + b ≤
          okPolls (oDone L c) ((X.tr h).take a)) := by
  obtain ⟨y', a', pc1, pc2, hy'lt, hy', ha', hord, hs, ho⟩ := H.route.soft_bar hb hga hsoft
  obtain ⟨hhlt, hhc, hh128⟩ := H.route.soft_thread hsoft
  obtain ⟨hplt, hpc, hp128⟩ := H.route.soft_thread H.route.p0_soft
  have hlen : ia < (X.tr p0).length := len_of_get hga
  have hw := H.bar hhlt hplt (hhc.trans hpc.symm) hh128 hp128 ha' hy' (by omega) hord
  exact ⟨a', len_of_get ha', rendezvous_path (K := K) hy' hw (k := ia) hy'lt hlen, hs, ho⟩

set_option maxRecDepth 20000 in
/-- **The `p_ready` step**: thread 0's arrival follows each MMA lane's earlier polls. -/
theorem stepP (H : Ctx L K A mem0 X c cm p0 Soft Mma) {n : Ref × Bool}
    (ih : IH L K X c p0 Soft Mma n) : RPn L K X c p0 Mma n := by
  intro b hb i pc sc hget hn h hh j hj
  subst hn
  have hX := H.cons
  have hlen : i < (X.tr p0).length := len_of_get hget
  have hpolls := H.route.arrive_polls hb hget
  have hpath0 : Relation.TransGen (DepStep L K X)
      (.thread (p0, MbarRing.Poll.nth X (sReady L c b) p0
        (arrivals (pReady L c b) ((X.tr p0).take i))), true) (.thread (p0, i), false) :=
    .single (poll_guard H.route.spin hlen hpolls)
  obtain ⟨t, hS, ht, hobs⟩ :=
    (MbarRing.Notify.Obj.obs hX (sObj hX H.facts hb) p0).content_of_reach
    hX.depStepAcyclic (J := arrivals (pReady L c b) ((X.tr p0).take i))
    (n := (.thread (p0, i), false))
    (MbarRing.Poll.nth_present.mpr (poll_lt hlen.le hpolls))
    (fun j' hj' => MbarRing.Poll.enables_earlier H.route.spin hj'
      (poll_lt hlen.le hpolls) hpath0)
    (fun x hx hxn j' hj' => by
      obtain ⟨⟨k, r, hk, hid, hf, -⟩, pc', sp, hget', hm, ht', hcnt⟩ :=
        (sObj hX H.facts hb).S_rec hx
      exact (ih _ (notify_mem hX _ hget') hxn).2.1 b hb p0 H.route.p0_soft _ _
        ⟨r, List.mem_of_getElem? hk, hid⟩ rfl j' (by rw [hcnt]; exact hj')) 0
  have hu : t = arrivals (pReady L c b) ((X.tr p0).take i) := ht
  obtain ⟨⟨k, r, hk, hid, hf, -⟩, pcc, sp, hgetc, hm, htg, hcnt⟩ :=
    (sObj hX H.facts hb).S_rec hS
  obtain ⟨-, -, -, -, hrank⟩ := notify_rec hX (List.mem_of_getElem? hk) hid
  set iy := MbarRing.Notify.cm X cm (sReady L c b) t with hiy
  have hgetc' : X.get (cm, iy) = some ⟨pcc, .tc (.commit sp)⟩ := hgetc
  have hcnt' : ((X.tr cm).take iy).countP (commitsTo (sReady L c b)) = t := hcnt
  have hlane : Relation.TransGen (DepStep L K X)
      (.thread (h, MbarRing.Poll.nth X (pReady L c b) h j), true) (.thread (cm, iy), false) := by
    by_cases hhc : h = cm
    · subst hhc
      refine .single (poll_guard H.route.spin (len_of_get hgetc') ?_)
      have := H.route.qk_polls hb hgetc' hm
      omega
    · exact (H.route.lane_commit hh hhc hb hgetc' hm (by omega)).2
  exact ((hlane.tail (commit_notify hgetc' hrank)).tail (DepStep.of_witness L hobs)).tail
    (poll_guard H.route.spin hlen hpolls)


set_option maxRecDepth 20000 in
/-- **The `s_ready` step**: the notification of a commit follows each softmax thread's polls for
the earlier uses. -/
theorem stepS (H : Ctx L K A mem0 X c cm p0 Soft Mma) {n : Ref × Bool}
    (ih : IH L K X c p0 Soft Mma n) : RSn L K X c Soft n := by
  intro b hb h hsoft y rank ⟨r, hr, hid⟩ hn j hj
  subst hn
  have hX := H.cons
  obtain ⟨pc, sp, hy, ht, hrank⟩ := notify_rec hX hr hid
  obtain ⟨g', iy⟩ := y
  obtain ⟨hyc, hm⟩ := H.facts.commit_only hy ht (CommitBar.sReady hb)
  simp only at hyc
  subst g'
  have hj' : j < ((X.tr cm).take iy).countP (commitsTo (sReady L c b)) := hj
  have hqk := H.route.qk_polls hb hy hm
  have hpy : j + 1 ≤ okPolls (pReady L c b) ((X.tr cm).take iy) := by omega
  have hlen : iy < (X.tr cm).length := len_of_get hy
  have hpath : Relation.TransGen (DepStep L K X)
      (.thread (cm, MbarRing.Poll.nth X (pReady L c b) cm j), true)
      (.async (cm, iy) (.tcNotify rank), false) :=
    (Relation.TransGen.single (poll_guard H.route.spin hlen hpy)).tail (commit_notify hy hrank)
  obtain ⟨t, hS, ht', hobs⟩ :=
    (MbarRing.Unit.Obj.obs hX (pObj hX H.facts hb) cm).content_of_reach hX.depStepAcyclic
    (J := j) (n := (.async (cm, iy) (.tcNotify rank), false))
    (MbarRing.Poll.nth_present.mpr (poll_lt hlen.le hpy))
    (fun j'' hj'' => MbarRing.Poll.enables_earlier H.route.spin hj''
      (poll_lt hlen.le hpy) hpath)
    (fun x hx hxn j'' hj'' => by
      obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj hX H.facts hb).S_rec hx
      exact (ih _ (thread_mem hX hga) hxn).1 b hb hga rfl cm H.route.cm_mma j''
        (lt_of_lt_of_eq hj'' harr.symm)) 0
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj hX H.facts hb).S_rec hS
  have hga' : X.get (p0, Flow.nthEv X (arrivesOn (pReady L c b)) p0 t) =
      some ⟨pca, .arrive (pReady L c b) 0 1 true sca⟩ := hga
  have harr' : arrivals (pReady L c b)
      ((X.tr p0).take (Flow.nthEv X (arrivesOn (pReady L c b)) p0 t)) = t := harr
  obtain ⟨a, hal, hrend, hs, -⟩ := soft_rendezvous H hb hsoft hga'
  rw [harr'] at hs
  have hu : t = j := ht'
  subst hu
  exact .head (poll_guard H.route.spin hal (by omega))
    (hrend.trans (.head (DepStep.of_witness L hobs) hpath))

set_option maxRecDepth 20000 in
/-- **The `o_done` step**: the notification of a commit follows each softmax thread's polls for
the earlier uses. -/
theorem stepO (H : Ctx L K A mem0 X c cm p0 Soft Mma) {n : Ref × Bool}
    (ih : IH L K X c p0 Soft Mma n) : ROn L K X c Soft n := by
  intro h hsoft y rank ⟨r, hr, hid⟩ hn j hj
  subst hn
  have hX := H.cons
  obtain ⟨pc, sp, hy, ht, hrank⟩ := notify_rec hX hr hid
  obtain ⟨g', iy⟩ := y
  obtain ⟨hyc, hm⟩ := H.facts.commit_only hy ht CommitBar.oDone
  simp only at hyc
  subst g'
  have hj' : j < ((X.tr cm).take iy).countP (commitsTo (oDone L c)) := hj
  obtain ⟨u, bb, hbb, hjub, hu, hbbe⟩ : ∃ u bb, bb < 2 ∧ 2 * u + bb = j + 1 ∧
      u = (j + 1) / 2 ∧ bb = (j + 1) % 2 :=
    ⟨(j + 1) / 2, (j + 1) % 2, by omega, by omega, rfl, rfl⟩
  have hpy : u + 1 ≤ okPolls (pReady L c bb) ((X.tr cm).take iy) := by
    rw [hu, hbbe]
    exact H.route.pv_polls hy hm (j + 1) (by omega)
  have hlen : iy < (X.tr cm).length := len_of_get hy
  have hpath : Relation.TransGen (DepStep L K X)
      (.thread (cm, MbarRing.Poll.nth X (pReady L c bb) cm u), true)
      (.async (cm, iy) (.tcNotify rank), false) :=
    (Relation.TransGen.single (poll_guard H.route.spin hlen hpy)).tail (commit_notify hy hrank)
  obtain ⟨t, hS, ht', hobs⟩ :=
    (MbarRing.Unit.Obj.obs hX (pObj hX H.facts hbb) cm).content_of_reach hX.depStepAcyclic
    (J := u) (n := (.async (cm, iy) (.tcNotify rank), false))
    (MbarRing.Poll.nth_present.mpr (poll_lt hlen.le hpy))
    (fun j'' hj'' => MbarRing.Poll.enables_earlier H.route.spin hj''
      (poll_lt hlen.le hpy) hpath)
    (fun x hx hxn j'' hj'' => by
      obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj hX H.facts hbb).S_rec hx
      exact (ih _ (thread_mem hX hga) hxn).1 bb hbb hga rfl cm H.route.cm_mma j''
        (lt_of_lt_of_eq hj'' harr.symm)) 0
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj hX H.facts hbb).S_rec hS
  have hga' : X.get (p0, Flow.nthEv X (arrivesOn (pReady L c bb)) p0 t) =
      some ⟨pca, .arrive (pReady L c bb) 0 1 true sca⟩ := hga
  have harr' : arrivals (pReady L c bb)
      ((X.tr p0).take (Flow.nthEv X (arrivesOn (pReady L c bb)) p0 t)) = t := harr
  obtain ⟨a, hal, hrend, -, ho⟩ := soft_rendezvous H hbb hsoft hga'
  rw [harr'] at ho
  have hu' : t = u := ht'
  subst hu'
  have ho' := ho (by omega)
  exact .head (poll_guard H.route.spin hal (by omega))
    (hrend.trans (.head (DepStep.of_witness L hobs) hpath))

/-- **The reuse paths of the three objects at every node.** -/
theorem reach_all (H : Ctx L K A mem0 X c cm p0 Soft Mma) :
    ∀ n ∈ nodes L X, Reach3 L K X c p0 Soft Mma n :=
  induction_of_acyclic H.cons.depStepAcyclic (nodes L X) _
    (fun _ _ ih => ⟨stepP H ih, stepS H ih, stepO H ih⟩)


/-! ### The exports -/

/-- **`Notify.Reach` of `s_ready b`** for every softmax thread: the premise of `SO.s_observes` and
`SO.s_doneBefore`. -/
theorem sReach (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b h : Nat} (hb : b < 2) (hh : Soft h) :
    MbarRing.Notify.Reach L K A X (sReady L c b) cm (sReady L c b) 0 h :=
  MbarRing.Notify.Reach.of_records (sObj H.cons H.facts hb) fun i rank hrec j hj => by
    obtain ⟨r, hr, hid, -⟩ := hrec
    obtain ⟨pc, sp, hy, -⟩ := notify_rec H.cons hr hid
    exact (reach_all H _ (notify_mem H.cons rank hy)).2.1 b hb h hh (cm, i) rank ⟨r, hr, hid⟩
      rfl j hj

/-- **`Notify.Reach` of `o_done`** for every softmax thread: the premise of `SOOdone.o_observes`
and `SOOdone.o_doneBefore`. -/
theorem oReach (H : Ctx L K A mem0 X c cm p0 Soft Mma) {h : Nat} (hh : Soft h) :
    MbarRing.Notify.Reach L K A X (oDone L c) cm (oDone L c) 0 h :=
  MbarRing.Notify.Reach.of_records (SO.oObj H.cons H.facts H.opar) fun i rank hrec j hj => by
    obtain ⟨r, hr, hid, -⟩ := hrec
    obtain ⟨pc, sp, hy, -⟩ := notify_rec H.cons hr hid
    exact (reach_all H _ (notify_mem H.cons rank hy)).2.2 h hh (cm, i) rank ⟨r, hr, hid⟩
      rfl j hj

/-- **`Unit.Reach` of `p_ready b`** for every MMA lane: the premise of `SO.p_handoff`. -/
theorem pReach (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b h : Nat} (hb : b < 2) (hh : Mma h) :
    MbarRing.Unit.Reach L K A X (pReady L c b) 1 (fun _ => p0) 0 h := by
  intro x hx j hj
  obtain ⟨-, ⟨pca, sca, hga⟩, harr⟩ := (pObj H.cons H.facts hb).S_rec hx
  exact (reach_all H _ (thread_mem H.cons hga)).1 b hb hga rfl h hh j
    (lt_of_lt_of_eq hj harr.symm)

/-- **The gate of `s_ready b`**: the notification of each recorded commit with `t ≥ 1` earlier
ones follows a poll with `t - 1` earlier successful ones. -/
theorem sGated (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b : Nat} (hb : b < 2) :
    MbarRing.Notify.Gated L K A X (sReady L c b) cm (sReady L c b) 0 :=
  MbarRing.Notify.gated_of_paths (A := A) fun {i pc sp rank} hy hm ht hrec hpos =>
    ⟨p0, by
      obtain ⟨r, hr, hid⟩ := hrec
      exact (reach_all H _ (notify_mem H.cons rank hy)).2.1 b hb p0 H.route.p0_soft (cm, i) rank
        ⟨r, hr, hid⟩ rfl _ (Nat.sub_lt hpos Nat.one_pos)⟩

/-- **The gate of `o_done`.** -/
theorem oGated (H : Ctx L K A mem0 X c cm p0 Soft Mma) :
    MbarRing.Notify.Gated L K A X (oDone L c) cm (oDone L c) 0 :=
  MbarRing.Notify.gated_of_paths (A := A) fun {i pc sp rank} hy hm ht hrec hpos =>
    ⟨p0, by
      obtain ⟨r, hr, hid⟩ := hrec
      exact (reach_all H _ (notify_mem H.cons rank hy)).2.2 p0 H.route.p0_soft (cm, i) rank
        ⟨r, hr, hid⟩ rfl _ (Nat.sub_lt hpos Nat.one_pos)⟩

/-- **The gate of `p_ready b`**: thread 0's arrival of use `u ≥ 1` follows the committing lane's
poll with `u - 1` earlier successful ones. -/
theorem pGated (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b : Nat} (hb : b < 2) :
    MbarRing.Unit.Gated L K A X (pReady L c b) 1 (fun _ => p0) 0 :=
  @MbarRing.Unit.gated_of_paths L K A X (pReady L c b) 1 0 (fun _ => p0)
    (fun {_ _ _ _} hga hpos => ⟨cm,
      (reach_all H _ (thread_mem H.cons hga)).1 b hb hga rfl cm H.route.cm_mma _
        (Nat.sub_lt hpos Nat.one_pos)⟩)


/-- **No record of `s_ready b` faults.** -/
theorem s_faultFree (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b : Nat} (hb : b < 2) :
    ∀ r ∈ X.objects (sReady L c b), r.fault = none :=
  MbarRing.Notify.Obj.fault_free H.cons (sObj H.cons H.facts hb) (sGated H hb)

/-- **No record of `o_done` faults** (the barrier the unmodified kernel violated
§9.7.15.16.5.1 on: with the dense polls its arrivals follow the previous phase's polls). -/
theorem o_faultFree (H : Ctx L K A mem0 X c cm p0 Soft Mma) :
    ∀ r ∈ X.objects (oDone L c), r.fault = none :=
  MbarRing.Notify.Obj.fault_free H.cons (SO.oObj H.cons H.facts H.opar) (oGated H)

/-- **No record of `p_ready b` faults.** -/
theorem p_faultFree (H : Ctx L K A mem0 X c cm p0 Soft Mma) {b : Nat} (hb : b < 2) :
    ∀ r ∈ X.objects (pReady L c b), r.fault = none :=
  MbarRing.Unit.Obj.fault_free H.cons (pObj H.cons H.facts hb)
    (fun {a _ _ _} hga hpos => pGated H hb (a := a) hga hpos)

/-- **No record of `o_final` faults**, given that the MMA lane commits to it once (the first
commit has no earlier one, so its notification has no gate to follow). -/
theorem f_faultFree (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0)
    (hone : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (oFinal L c)) = 0) :
    ∀ r ∈ X.objects (oFinal L c), r.fault = none :=
  MbarRing.Notify.Obj.fault_free hX (SO.fObj hX F)
    (MbarRing.Notify.gated_of_paths (A := A) fun {i pc sp rank} hy hm ht hrec hpos => by
      have := hone hy hm
      omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Mbar
