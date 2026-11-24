-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Lemmas.Flow.ArriveCount
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # The loader's thread facts: where its events come from

An event of a thread of warp 14 that is not of the prologue's kinds fires from a loader state,
with the loader's run invariant (`Loader.Counts`) over the thread's earlier events
(`Loader.origin`). The event has its site's shape (`Loader.site_event`): only the poll sites
fire polls (`poll_site`), only the arrival sites arrivals (`arrive_site`), each with the barrier,
parity, bytes and count of the shape.

Every tensor copy of the kernel is the loader's: no other role has a site at a tensor-load
instruction (`kernel_tensor_pcs`), so a copy fires from a loader state at a copy site, of the
copy `CopyIs` of that site's use and item (`copy_origin`, from the shape and the copy counts,
`copy_fact`). Every election of the thread returned its lane (`Counts.elect` at the
copy site and the warp's election dichotomy, `Static.elect_dichotomy_take`), so the copies
before it on its barrier number `CopyId.before`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader

/-! ### The positions of the polls, arrivals and copies -/

/-- The loader's ten tensor loads (the code's other `tensorCopy` sites are the store warp's
tensor stores). -/
abbrev tensorPcs : List Nat := [Flow.tensorCopy_0, Flow.tensorCopy_1, Flow.tensorCopy_2,
  Flow.tensorCopy_3, Flow.tensorCopy_4, Flow.tensorCopy_5, Flow.tensorCopy_6, Flow.tensorCopy_7,
  Flow.tensorCopy_8, Flow.tensorCopy_9]

theorem kernel_tensor_pcs : OpPcsFast kernel.code tensorOp tensorPcs = true := by
  decide +kernel

/-- A tensor copy fires at a tensor-load instruction. -/
theorem tensorOp_of {A : List Assumption} {g : Nat} {t : TState} {op : Op} {pc : Nat}
    {e : Event} {o : Option TState} {a : Nat} {sp : TensorCopy.Spec}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hk : e.kind = .tensorIssue a sp) :
    tensorOp op = true := by
  by_contra hne
  exact fires_notTensor (eventTmpl_notTensor (by simpa using hne)) hf a sp hk

/-! ### The sites of the loader's events -/

theorem site_copy (s : Site) (h : s.pc ∈ tensorPcs) : ∃ u j, s = .copy u j := by
  cases s
  case copy u j => exact ⟨u, j, rfl⟩
  all_goals (exfalso; revert h; site_decide)

theorem site_ret (s : Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s
  case exit => rfl
  all_goals (exfalso; revert h; site_decide)

/-- No site of another role, nor of the prologue, is a tensor load. -/
theorem prologue_not_tensor (s : Prologue.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

theorem idle_not_tensor (s : Idle.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

theorem store_not_tensor (s : Store.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

theorem corr_not_tensor (s : Correction.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

theorem softmax_not_tensor (s : Softmax.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

theorem mma_not_tensor (s : Mma.Site) : s.pc ∉ tensorPcs := by
  cases s <;> site_decide

/-! ### The copy of a copy site -/

/-- At a copy site, the event is the copy of the site's use, of the state's item and trip. -/
theorem copy_fact_at (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {d : D} {u : UseK}
    {j : Fin 2} {pre : List Event} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hs : d.site = .copy u j) (hJ : Counts L g d pre) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    CopyFactOf L g pre e ⟨u, j, d.i, d.t⟩ :=
  copy_fact hJ.toLedger hi (site_event hpre hg h hi hc hf) hs

/-! ### The loader's polls -/

/-- The barrier a poll site polls, from the use `B` of the ring registers and the Q parity
count `Q`: the KV slot of the site's use, or the Q stage. -/
def waitBar (s : Site) (B : Nat) : FBar :=
  match s with
  | .wait .q0 => .qEmpty 0
  | .wait .q1 | .drainQ => .qEmpty 1
  | .wait .v0 | .wait .v => .kvEmpty ⟨(B + 1) % 6, Nat.mod_lt _ (by decide)⟩
  | .drain k => .kvEmpty ⟨(B + k.val) % 6, Nat.mod_lt _ (by decide)⟩
  | _ => .kvEmpty ⟨B % 6, Nat.mod_lt _ (by decide)⟩

/-- The parity a poll site polls with. -/
def waitPar (s : Site) (B Q : Nat) : Nat :=
  match s with
  | .wait .q0 | .wait .q1 | .drainQ => Q % 2
  | .wait .v0 | .wait .v => ((B + 1) / 6 + 1) % 2
  | .drain k => ((B + k.val) / 6 + 1) % 2
  | _ => (B / 6 + 1) % 2

/-- The drain's polls are of cluster-scope sites. -/
theorem drain_cluster (k : Fin 6) : (Site.drain k).pc ∈ Assumptions.clusterMbarSites := by
  revert k; decide

/-- **A loader poll** is of an empty barrier of its CTA, with the parity of the thread's earlier
successful polls of it plus the barrier's poll offset; barrier and parity are those of the site
and the state's ring use (`waitBar`, `waitPar`). -/
theorem wait_fact (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {d : D} {pre : List Event}
    {e : Event} {t : TState} {ins : Instr} {o : Option TState} (hJ : Counts L g d pre)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) {m : Loc} {p : Nat}
    {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    ∃ b : FBar, b.isEmpty ∧ m = b.loc L (ctaOf L g) ∧
      p % 2 = (okPolls m pre + b.pollOffset) % 2 ∧ e.pc ∈ Assumptions.clusterMbarSites ∧
      b = waitBar d.site (kvB L g d) ∧ p % 2 = waitPar d.site (kvB L g d) (qB L g d) := by
  have hev := site_event hpre hg h hi hc hf
  have hpc := fires_pc hf
  have hR := hJ.ring
  have hkp := hJ.kvPoll
  have hqp' := hJ.qPoll
  obtain ⟨epc, ek⟩ := e
  simp only at hk hpc
  subst hk hpc
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  have hs6 : s < 6 := hi.s
  have hsn := snext_lt hs6
  have hA := sAfter_lt hs6
  cases site <;> (try cases ‹UseK›) <;>
    simp only [Ev, PollIs, ArriveIs, reduceCtorEq, exists_false, false_and] at hev
  all_goals obtain ⟨ok', acq', sc', hk'⟩ := hev
  all_goals simp only [Kind.wait.injEq] at hk'
  all_goals obtain ⟨rfl, rfl, -⟩ := hk'
  all_goals simp only [kvB, qB] at hR
  all_goals have hN := ring_after hR.1 hR.2.1
  all_goals first
    | refine ⟨.kvEmpty ⟨s, hs6⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨.kvEmpty ⟨snext s, hsn⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨.qEmpty 0, rfl, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨.qEmpty 1, rfl, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨.kvEmpty ⟨sAfter _ s, hA _⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (dsimp only; decide)
    | exact drain_cluster _
    | (have hN1 := hN 1; have hN2 := hN 2; have hN3 := hN 3; have hN4 := hN 4; have hN5 := hN 5
       have hNx := ring_next hR.1 hR.2.1
       try have hNk := hN (Fin.val ‹Fin 6›)
       try first
         | erw [hkp ⟨s, hs6⟩]
         | erw [hkp ⟨snext s, hsn⟩]
         | erw [hqp' 0]
         | erw [hqp' 1]
         | erw [hkp ⟨sAfter _ s, hA _⟩]
       all_goals simp only [waitBar, waitPar, kvPolled, qPolled, slotCount, FBar.pollOffset, kvB,
         qB, FBar.kvEmpty.injEq, Fin.ext_iff, Fin.isValue] at hN1 ⊢
       all_goals (try split_ifs at hN1 ⊢)
       all_goals omega)

/-! ### The loader's arrivals -/

/-- Only the arrival sites fire arrivals. -/
theorem arrive_site {g : Nat} {d : D} {e : Event} (hev : Ev L g d e) {m : Loc} {tx c : Nat}
    {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx c rel sc) :
    (∃ u, d.site = .arrive u) ∨ d.site = .arriveTail := by
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  cases site <;> (try cases ‹UseK›) <;>
    simp only [Ev, PollIs, ArriveIs, reduceCtorEq, exists_false, false_and] at hev
  all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr rfl

/-- **A loader arrival** is the leader CTA's, on a full barrier of its CTA, of one unit
expecting the use's bytes, after the last election returned the lane; along a trace whose
elections all returned the lane, it follows more polls of the partner empty barrier than its
earlier arrivals on the full barrier. -/
theorem arrive_fact (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {d : D}
    {pre : List Event} {e : Event} {t : TState} {ins : Instr} {o : Option TState}
    (hJ : Counts L g d pre) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) {m : Loc} {tx cnt : Nat}
    {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx cnt rel sc) :
    ∃ b : FBar, b.isFull ∧ m = b.loc L (ctaOf L g) ∧ tx = b.useBytes ∧ cnt = 1 ∧
      ctaOf L g % 2 = 0 ∧ ¬ ElectNonLead L g pre ∧
      (ElectLead L g pre → arrivals m pre + 1 ≤ okPolls (b.partner.loc L (ctaOf L g)) pre) := by
  have hev := site_event hpre hg h hi hc hf
  have hw := arrive_site hev hk
  have hel : ¬ ElectNonLead L g pre := hJ.elect (by
    rcases hw with ⟨u, hu⟩ | hu
    · exact .inl ⟨u, hu⟩
    · exact .inr (.inr hu))
  have hr0 : Work.rank L g = 0 := hi.lead (by rcases hw with ⟨u, hu⟩ | hu <;> rw [hu] <;> rfl)
  have hA : ∀ m', arrivesOn m' e = decide (m = m') := fun _ =>
    arrivesOn_arrive (show e = ⟨e.pc, .arrive m tx cnt rel sc⟩ by rw [← hk])
  have hne : ∀ mask inst ld, e.kind ≠ .elect mask inst ld := by intro _ _ _ h; rw [hk] at h; cases h
  -- the state after the arrival, and its counts
  obtain ⟨d', hn, hkv, hq⟩ : ∃ d', next L g d e = some (some d') ∧
      kvArrived L g d' ≤ kvPolled L g d ∧ ∀ st, qArrived L g d' st ≤ qPolled L g d st := by
    obtain ⟨site, i, tt, s, ph, qp⟩ := d
    simp only at hw
    rcases hw with ⟨u, rfl⟩ | rfl
    · refine ⟨⟨.elC u 0, i, tt, s, ph, qp⟩, by simp only [next, hk], ?_, fun st => ?_⟩ <;>
        cases u <;> simp [kvArrived, kvPolled, qArrived, qPolled]
    · exact ⟨⟨.exit, i, tt, s, ph, qp⟩, by simp only [next, hk], by simp [kvArrived, kvPolled],
        fun st => by simp [qArrived, qPolled]⟩
  have hJ' := counts_step hpre hg hJ hi h hc hf hn
  -- the arrival's count
  have hcnt : cnt = 1 := by
    obtain ⟨epc, ek⟩ := e
    obtain ⟨site, i, tt, s, ph, qp⟩ := d
    simp only at hw hk
    subst hk
    rcases hw with ⟨u, rfl⟩ | rfl <;> (try cases u) <;> simp only [Ev, ArriveIs] at hev <;>
      obtain ⟨rel', sc', hk'⟩ := hev <;> simp only [Kind.arrive.injEq] at hk' <;> exact hk'.2.2.1
  have hlead : ElectLead L g pre → ElectLead L g (pre ++ [e]) :=
    fun hl => (electLead_snoc_of_ne hne).mpr hl
  rcases hJ'.arrTx e (List.mem_append_right _ (List.mem_singleton_self e)) m tx cnt rel sc hk
    with ⟨rfl, s, rfl⟩ | ⟨rfl, st, rfl⟩
  · refine ⟨.kvFull s, rfl, rfl, (FBar.useBytes_kv s).symm, hcnt, hr0, hel, fun hl => ?_⟩
    have h1 := hJ.kvArr hl s
    have h2 := hJ'.kvArr (hlead hl) s
    have h3 := hJ.kvPoll s
    rw [arrivals_snoc, hA, decide_eq_true rfl] at h2
    simp only [FBar.partner]
    rw [h1, h3]
    have := hkv
    simp only [hr0, ↓reduceIte, slotCount] at h1 h2 ⊢
    omega
  · refine ⟨.qFull st, rfl, rfl, (FBar.useBytes_q st).symm, hcnt, hr0, hel, fun hl => ?_⟩
    have h1 := hJ.qArr hl st
    have h2 := hJ'.qArr (hlead hl) st
    have h3 := hJ.qPoll st
    rw [arrivals_snoc, hA, decide_eq_true rfl] at h2
    simp only [FBar.partner]
    rw [h1, h3]
    have := hq st
    simp only [hr0, ↓reduceIte] at h1 h2 ⊢
    omega

/-! ### The origin of the loader's events -/

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (Proof.code L) X)
include hpre hX ht

/-- **An event of the loader's warp** that is not of the prologue's kinds fires from a loader
state, with the loader's counts over the thread's earlier events. -/
theorem origin {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hnp : ¬ Prologue.ProKind e.kind) (hw : warpOf L g = 14) :
    ∃ d t ins o, Frame.stateAt (Proof.code L) X g k = some (some (.inr (.loader d))) ∧
      Counts L g d ((X.tr g).take k) ∧ At t d.site.pc (facts L g d) ∧ Inv L g d ∧
      kernel.code[d.site.pc]? = some ins ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he hub
  have hg := Frame.lt_of_get hX he
  rcases d with p | r
  · exact absurd (pro_event hpre hX he hσ fun f hf' => hub e.pc f (by rw [← hf'])).proKind hnp
  · have hw' := role_warp_run hpre hg
      (Frame.trace (C := Proof.code L) (fun _ hg => sound hpre hg) hX hg) k r hσ
    cases r with
    | loader l =>
      exact ⟨l, t, ins, o, hσ, hJ, ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩, hi,
        hc, hf⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hw'; omega

/-- **Every tensor copy is the loader's**: it fires from a loader state at a copy site, of the
copy of the site's use, and the copies before it on its barrier number `CopyId.before`. -/
theorem copy_origin {g k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ d : D, warpOf L g = 14 ∧
      Frame.stateAt (Proof.code L) X g k = some (some (.inr (.loader d))) ∧
      Counts L g d ((X.tr g).take k) ∧ Inv L g d ∧ LeadAt L X g k ∧ ∃ u j, d.site = .copy u j ∧
        CopyIs L g ⟨u, j, d.i, d.t⟩ a sp ∧
        ((X.tr g).take k).countP (issuesTo sp.mbar) = CopyId.before L ⟨u, j, d.i, d.t⟩ := by
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hg := Frame.lt_of_get hX he
  have hpc := OpPcsFast.mem kernel_tensor_pcs hc (tensorOp_of hf rfl)
  rcases d with p | r
  · exact absurd hpc (prologue_not_tensor p.site)
  cases r with
  | idle s => exact absurd hpc (idle_not_tensor s.site)
  | store s => exact absurd hpc (store_not_tensor s.site)
  | softmax s => exact absurd hpc (softmax_not_tensor s.site)
  | corr c => exact absurd hpc (corr_not_tensor c.site)
  | mma m => exact absurd hpc (mma_not_tensor m.site)
  | loader l =>
    have hw' := role_warp_run hpre hg
      (Frame.trace (C := Proof.code L) (fun _ hg => sound hpre hg) hX hg) k (.loader l) hσ
    obtain ⟨u, j, hs⟩ := site_copy l.site hpc
    have hcf := copy_fact_at hpre hg hs hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf a sp rfl
    have hn := hJ.elect (.inr (.inl ⟨u, j, hs⟩))
    have hl : ElectLead L g ((X.tr g).take k) :=
      (Static.elect_dichotomy_take hX g k).resolve_right hn
    exact ⟨l, hw', hσ, hJ, hi, Static.leadAt_of_not_nonLead hX hn, u, j, hs, hcf.1, hcf.2 hl⟩

omit hpre hX ht in
/-- A full-mask election that returned the lane before event `k`: not every election before it
returned another lane. -/
theorem not_nonLead_of_leadAt {g k : Nat} (h : LeadAt L X g k) :
    ¬ ElectNonLead L g ((X.tr g).take k) := by
  obtain ⟨j, hj, pc, inst, hE⟩ := h
  have hE' : (X.tr g)[j]? = some ⟨pc, .elect 4294967295 inst (laneOf L g)⟩ := hE
  have hmem : (⟨pc, .elect 4294967295 inst (laneOf L g)⟩ : Event) ∈ (X.tr g).take k :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hE')
  exact fun hn => hn _ hmem _ _ _ rfl rfl

/-- **The loader's exit**: at its exit state, with the exit the thread's last event. -/
theorem exit_state {g k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) (hw : warpOf L g = 14) :
    ∃ d : D, d.site = .exit ∧ Counts L g d ((X.tr g).take k) ∧
      X.tr g = (X.tr g).take k ++ [⟨pc, .exit⟩] := by
  obtain ⟨d, t, ins, o, -, hJ, -, -, hc, hf⟩ :=
    origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  have hret : retOp ins.op = true := retOp_of_fires hf rfl
  have hs := site_ret d.site (OpPcsFast.mem kernel_ret_pcs hc hret)
  have hg := Frame.lt_of_get hX he
  have hlen := Execution.exit_last hX hg he
  refine ⟨d, hs, hJ, ?_⟩
  conv_lhs => rw [← List.take_of_length_le (show (X.tr g).length ≤ k + 1 by omega)]
  rw [List.take_add_one]
  have he' : (X.tr g)[k]? = some ⟨pc, .exit⟩ := he
  rw [he']
  rfl

end Loader

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`RingFacts.poll`, the loader's part**: a poll of a ring barrier by a thread of warp 14 is
of an empty barrier of its CTA, with the parity of its earlier successful polls plus the poll
offset, acquiring at cluster scope. -/
theorem RingFacts_poll_loader : ∀ {g k pc p c : Nat} {b : FBar} {ok acq : Bool}
    {sc : MbarScope}, g < L.threads → warpOf L g = 14 →
    X.get (g, k) = some ⟨pc, .wait (b.loc L c) p ok acq sc⟩ → b.ring →
      c = ctaOf L g ∧ (b.isFull → warpOf L g = 12 ∧ ctaOf L g % 2 = 0) ∧
      (b.isEmpty → warpOf L g = 14) ∧
      p % 2 = (okPolls (b.loc L c) ((X.tr g).take k) + b.pollOffset) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  intro g k pc p c b ok acq sc _ hw he _
  obtain ⟨d, t, ins, o, -, hJ, h, hi, hc, hf⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  obtain ⟨b', hemp, hm, hp, hpc, -⟩ :=
    Loader.wait_fact hpre (Frame.lt_of_get hX he) hJ hi h hc hf rfl
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  obtain ⟨hacq, hsc⟩ := Static.wait_attr hX he
  refine ⟨rfl, fun hfull => ?_, fun _ => hw, hp, fun _ => ⟨hacq, hsc hpc⟩⟩
  cases b <;> simp [FBar.isEmpty, FBar.isFull] at hemp hfull

/-- **`RingFacts.arrive`, the loader's part**: an arrival of a thread of warp 14 on a ring
barrier is the leader CTA's elected lane's, on a full barrier of its CTA, of one unit expecting
the use's bytes, after more polls of the partner empty barrier than earlier arrivals. -/
theorem RingFacts_arrive_loader : ∀ {g k pc tx cnt c : Nat} {b : FBar} {rel : Bool}
    {sc : MbarScope}, g < L.threads → warpOf L g = 14 →
    X.get (g, k) = some ⟨pc, .arrive (b.loc L c) tx cnt rel sc⟩ → b.ring →
      b.isFull ∧ c = ctaOf L g ∧ ctaOf L g % 2 = 0 ∧ warpOf L g = 14 ∧ LeadAt L X g k ∧
      tx = b.useBytes ∧ cnt = 1 ∧
      arrivals (b.loc L c) ((X.tr g).take k) + 1 ≤
        okPolls (b.partner.loc L c) ((X.tr g).take k) := by
  intro g k pc tx cnt c b rel sc hg hw he _
  obtain ⟨d, t, ins, o, -, hJ, h, hi, hc, hf⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  obtain ⟨b', hfull, hm, htx, hcnt, hcta, hel, hle⟩ :=
    Loader.arrive_fact hpre hg hJ hi h hc hf rfl
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  exact ⟨hfull, rfl, hcta, hw, Static.leadAt_of_not_nonLead hX hel, htx, hcnt,
    hle ((Static.elect_dichotomy_take hX g k).resolve_right hel)⟩

/-- **`RingFacts.drain`**: at its exit an elected loader lane has polled every ring empty
barrier but Q stage 0's once more than its uses of the partner full barrier. -/
theorem RingFacts_drain : ∀ {g k pc : Nat} {b : FBar}, g < L.threads →
    X.get (g, k) = some ⟨pc, .exit⟩ → warpOf L g = 14 → LeadAt L X g k → b.isFull →
    b ≠ .qFull 0 →
      (X.tr g).countP (issuesTo (b.loc L (pairBase L g))) + b.copies =
        b.copies * okPolls (b.partner.loc L (ctaOf L g)) (X.tr g) := by
  intro g k pc b _ he hw hlead hb hb0
  obtain ⟨d, hs, hJ, htr⟩ := Loader.exit_state hpre hX ht he hw
  have hl := (Static.elect_dichotomy_take hX g k).resolve_right
    (Loader.not_nonLead_of_leadAt hlead)
  rw [htr, List.countP_append, okPolls_snoc]
  simp only [issuesTo, okPoll, List.countP_singleton]
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hb
  case qFull st =>
    have hst : st = 1 := by
      rcases Store.fin2_cases st with rfl | rfl
      · exact absurd rfl hb0
      · rfl
    subst hst
    have h1 := hJ.qIss hl 1
    have h2 := hJ.qPoll 1
    simp only [Loader.qIssued, Loader.qPolled] at h1 h2
    simp only [pairBase, FBar.partner, FBar.copies, h1, h2]
    simp [sourceWaitSuccess]
    omega
  case kvFull s' =>
    have h1 := hJ.kvIss hl s'
    have h2 := hJ.kvPoll s'
    simp only [Loader.kvIssued, Loader.kvDone, Loader.kvPart, Loader.kvPolled,
      Loader.slotCount, reduceCtorEq, or_self, ↓reduceIte, ite_self, Nat.add_zero] at h1 h2
    simp only [pairBase, FBar.partner, FBar.copies, h1, h2]
    simp [sourceWaitSuccess]
    split_ifs <;> omega

/-- **`ExitFacts.loader_q`**: at its exit an elected loader lane has polled its CTA's
`qEmpty 1` once more than its `qEmpty 0`. -/
theorem ExitFacts_loader_q : ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 14 →
    LeadAt L X g k → X.get (g, k) = some ⟨pc, .exit⟩ →
      okPolls (FBar.loc L (ctaOf L g) (.qEmpty 1)) (X.tr g) =
        okPolls (FBar.loc L (ctaOf L g) (.qEmpty 0)) (X.tr g) + 1 := by
  intro g k pc _ hw _ he
  obtain ⟨d, hs, hJ, htr⟩ := Loader.exit_state hpre hX ht he hw
  rw [htr, okPolls_snoc, okPolls_snoc, hJ.qPoll 1, hJ.qPoll 0]
  simp [okPoll, sourceWaitSuccess, Loader.qPolled, hs]

/-- **The loader's part of `Cross.SyncNamed`**: an arrival or a poll of a thread of warp 14
names a ring barrier of its CTA. -/
theorem Cross.SyncNamed_loader : ∀ {g k pc : Nat} {m : Loc} {kd : Kind}, g < L.threads →
    warpOf L g = 14 → X.get (g, k) = some ⟨pc, kd⟩ →
    ((∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨
      (∃ p ok acq sc, kd = .wait m p ok acq sc)) →
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧ ∀ i st, b ≠ .spare i st := by
  intro g k pc m kd hg hw he hk
  rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
  · obtain ⟨d, t, ins, o, -, hJ, h, hi, hc, hf⟩ :=
      Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
    obtain ⟨b, hb, hm, -⟩ := Loader.arrive_fact hpre hg hJ hi h hc hf rfl
    refine ⟨b, _, hm, rfl, fun i st h => ?_⟩
    subst h
    simp [FBar.isFull] at hb
  · obtain ⟨d, t, ins, o, -, hJ, h, hi, hc, hf⟩ :=
      Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
    obtain ⟨b, hb, hm, -⟩ := Loader.wait_fact hpre (Frame.lt_of_get hX he) hJ hi h hc hf rfl
    refine ⟨b, _, hm, rfl, fun i st h => ?_⟩
    subst h
    simp [FBar.isEmpty] at hb

/-- **The loader's part of `Cross.PeerBar2High`**: a thread of warp 14 makes no use of the other
CTA: its arrivals name barriers of its own CTA, and it makes no commit. -/
theorem Cross.PeerBar2High_loader : ∀ {g k : Nat} {ev : Event}, g < L.threads →
    warpOf L g = 14 → X.get (g, k) = some ev → ¬ PeerEvent L g ev := by
  intro g k ev hg hw he hp
  rcases hp with ⟨m, tx, cnt, rel, sc, hk, hne, -⟩ | ⟨sp, hk⟩
  · obtain ⟨pc, kd⟩ := ev
    simp only at hk
    subst hk
    obtain ⟨d, t, ins, o, -, hJ, h, hi, hc, hf⟩ :=
      Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
    obtain ⟨b, -, rfl, -⟩ := Loader.arrive_fact hpre hg hJ hi h hc hf rfl
    exact hne rfl
  · obtain ⟨pc, kd⟩ := ev
    simp only at hk
    subst hk
    obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
      Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
    have hop : commitOp ins.op = true := by
      by_contra hne
      exact fires_notCommit (eventTmpl_notCommit (commitOp_ne (by simpa using hne))) hf sp rfl
    exact (Loader.site_not d.site).1 (OpPcsFast.mem kernel_commit_pcs hc hop)


end
end PTX.Kernels.FlashAttn4Fwd.Proof
