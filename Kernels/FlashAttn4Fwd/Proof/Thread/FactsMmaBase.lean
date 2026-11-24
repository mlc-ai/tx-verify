-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Lemmas.Flow.Final
public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The MMA warp's events, from its machine

The tools of the MMA warp's thread facts:

* an event of a thread of warp 12 that is not of the prologue's kinds fires from a state of the
  MMA role, with the role's run invariant `Mma.Counts` over the thread's earlier events, its
  state invariant, the register facts of its site and the site's instruction (`mma_state`; with
  a successor state when the event does not end the thread, `mma_state_cont`);
* a thread whose elections all use the full mask (every election of the kernel does) led every
  election of its trace or none (`mma_lead`), and a thread at a site of the elected lane led
  them all (`lead_of_site`);
* the arrival and the polls of a site (`arrive_ev`, `wait_ev`), and the `bar.sync 2` of each
  ordinal below the site's count (`bar2_nth`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A role state of a thread of warp 12 is an MMA state. -/
theorem mma_of_warp (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    {r : Role} (hg : g < L.threads) (hw : warpOf L g = 12)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) : ∃ d, r = .mma d := by
  have h := role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k
    r hσ
  rw [hw] at h
  cases r <;> simp only [Role.kind, RoleKind.Warp] at h <;> first | omega | exact ⟨_, rfl⟩

/-- **The MMA state of an event of warp 12** that is not of the prologue's kinds. -/
theorem mma_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hw : warpOf L g = 12) (hp : ¬ Prologue.ProKind e.kind) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ (d : Mma.D) (t : TState) (ins : Instr) (o : Option TState),
      Frame.stateAt (code L) X g k = some (some (.inr (.mma d))) ∧
      Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ t.pc = d.site.pc ∧
      t.sub = d.site.sub ∧ Holds t.regs (Mma.facts L g d) ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he
      (fun pc f h => hub f (by rw [h]))
  rcases d with p | r
  · exact absurd (pro_event hpre hX he hσ hub).proKind hp
  · obtain ⟨m, rfl⟩ := mma_of_warp hpre hX hg hw hσ
    exact ⟨m, t, ins, o, hσ, hJ, hi.1, hat.1, hat.2.1, hat.2.2.2.2, hc, hf⟩

/-- **The MMA state of a continuing event of warp 12.** -/
theorem mma_state_cont (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hw : warpOf L g = 12) (hp : ¬ Prologue.ProKind e.kind) (hend : ¬ Ends e) :
    ∃ (d : Mma.D) (t : TState) (ins : Instr) (u : TState),
      Frame.stateAt (code L) X g k = some (some (.inr (.mma d))) ∧
      Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ t.pc = d.site.pc ∧
      t.sub = d.site.sub ∧ Holds t.regs (Mma.facts L g d) ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := by
  obtain ⟨d, t, ins, o, hσ, hJ, hi, hpc, hs, h, hc, hf⟩ :=
    mma_state hpre hX ht he hw hp fun f hk => hend (.inl ⟨f, hk⟩)
  cases o with
  | none => exact absurd (fires_none_ends hf) hend
  | some u => exact ⟨d, t, ins, u, hσ, hJ, hi, hpc, hs, h, hc, hf⟩

/-- Every election of a thread uses the full mask. -/
theorem elect_mask_full (hX : Consistent L kernel asms mem0 X) (g : Nat) :
    ElectMask 4294967295 (X.tr g) := fun e he mask inst ld hk => by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  exact elect_full hX (e := (g, j)) (pc := e.pc) (show (X.tr g)[j]? = _ by rw [hj, ← hk])

/-- A thread led every election of its trace or none. -/
theorem mma_lead (hX : Consistent L kernel asms mem0 X) (g : Nat) :
    ElectLead L g (X.tr g) ∨ ElectNonLead L g (X.tr g) :=
  electLead_or_nonLead hX.elect (elect_mask_full hX g)

/-- A thread at a site of the elected lane led every election of its trace. -/
theorem lead_of_site (hX : Consistent L kernel asms mem0 X) {g k : Nat} {d : Mma.D}
    (hJ : Mma.Counts L g d ((X.tr g).take k)) (hl : d.site.lead = true) :
    ElectLead L g (X.tr g) := by
  rcases mma_lead hX g with h | h
  · exact h
  · exact absurd hl (by rw [(hJ.nonLead (h.take k)).1]; decide)

/-- An event of a prefix of the thread's trace is an event of the execution before its end. -/
theorem mem_take_get {g k : Nat} {x : Event} (hx : x ∈ (X.tr g).take k) :
    ∃ j < k, X.get (g, j) = some x :=
  get_of_mem_take hx

/-- An event at a position below `k` is in the prefix of length `k`. -/
theorem mem_take_of_get {g j k : Nat} {e : Event} (he : X.get (g, j) = some e) (hj : j < k) :
    e ∈ (X.tr g).take k :=
  List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_take_of_lt hj]; exact he⟩

/-- **The `bar.sync 2` of each ordinal below the site's count** comes before the state. -/
theorem bar2_nth {g k n : Nat} {d : Mma.D} (hJ : Mma.Counts L g d ((X.tr g).take k))
    (hn : n < Mma.bar2A d.site) : ∃ b < k, Bar2Sync X g b n := by
  have hc := hJ.bar2
  obtain ⟨j, e, hj, he, hp, hcnt⟩ := exists_nthEv (X := X) (p := Execution.isBarId 2) (g := g)
    (k := k) (n := n) (by omega)
  refine ⟨j, hj, e.pc, ?_, hcnt⟩
  rw [he, ← hJ.bar2Sync e (mem_take_of_get he hj) hp]

/-- The parity of a site's poll. -/
def Mma.pollPar (L : Launch) (d : Mma.D) : Nat :=
  match d.site with
  | .qWait _ => d.i % 2
  | .kvWait k => Mma.kvPar L d.i (Mma.kvU k d.t)
  | .pWait _ | .p2Wait _ _ => Mma.pPar L d.i d.t
  | _ => 0

/-- **A poll of an MMA site** is of the site's poll barrier of the thread's CTA, with the site's
parity. -/
theorem wait_ev {g : Nat} {d : Mma.D} {e : Event} {m : Loc} {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (hev : Mma.Ev L g d e) (hk : e.kind = .wait m p ok acq sc) :
    ∃ B, Mma.pollBar L d = some B ∧ m = Mma.bar L g B ∧ p = Mma.pollPar L d := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Mma.Ev] at hev <;> simp only [Mma.pollBar, Mma.pollPar]
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok', acq', sc', h⟩ := hev
    rw [hk] at h
    obtain ⟨rfl, rfl, -⟩ := Kind.wait.inj h
    exact ⟨_, rfl, rfl, rfl⟩
  case arrivePeer =>
    obtain ⟨rel, sc', h⟩ := hev
    rw [hk] at h
    cases h
  case commit c =>
    rw [hk] at hev
    cases hev
  case mma b j => exact absurd (by rw [hk]; trivial) (Mma.notObject_of_mma hev)
  all_goals exact absurd (by rw [hk]; trivial) hev.1

/-- **An arrival of an MMA site** is the hand-off: one arrival on the peer's handshake
barrier. -/
theorem arrive_ev {g : Nat} {d : Mma.D} {e : Event} {m : Loc} {tx c : Nat} {rel : Bool}
    {sc : MbarScope} (hev : Mma.Ev L g d e) (hk : e.kind = .arrive m tx c rel sc) :
    d.site = .arrivePeer ∧ m = FBar.loc L (Mma.peer L g) .dealloc ∧ tx = 0 ∧ c = 1 := by
  obtain ⟨site, i, t, base, pro⟩ := d
  cases site <;> simp only [Mma.Ev] at hev
  case arrivePeer =>
    obtain ⟨rel', sc', h⟩ := hev
    rw [hk] at h
    obtain ⟨rfl, rfl, rfl, -⟩ := Kind.arrive.inj h
    exact ⟨rfl, rfl, rfl, rfl⟩
  case qWait k | kvWait k | pWait k | p2Wait k _ | waitDealloc =>
    obtain ⟨ok', acq', sc', h⟩ := hev
    rw [hk] at h
    cases h
  case commit c =>
    rw [hk] at hev
    cases hev
  case mma b j => exact absurd (by rw [hk]; trivial) (Mma.notObject_of_mma hev)
  all_goals exact absurd (by rw [hk]; trivial) hev.1

/-- The peer of the hand-off is the other CTA of the pair. -/
theorem peer_eq (hpre : Pre P L mem0) (g : Nat) : Mma.peer L g = pairCta (ctaOf L g) := by
  simp only [Mma.peer, clusterOf, ctaOf, Mma.rank,
    Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, pairCta]

/-- The last event of a prefix is the event before its end. -/
theorem getLast_take {g k : Nat} {x : Event} (h : ((X.tr g).take k).getLast? = some x)
    (hk : k ≤ (X.tr g).length) : ∃ j, k = j + 1 ∧ X.get (g, j) = some x := by
  cases k with
  | zero => simp at h
  | succ j =>
    refine ⟨j, rfl, ?_⟩
    rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk, Nat.add_sub_cancel,
      List.getElem?_take_of_lt (by omega)] at h
    exact h

/-- An event that is no poll leaves the successful polls of a prefix. -/
theorem okPolls_take_succ {g j : Nat} {x : Event} (m : Loc) (he : X.get (g, j) = some x)
    (hx : ∀ l p ok acq sc, x.kind ≠ .wait l p ok acq sc) :
    okPolls m ((X.tr g).take (j + 1)) = okPolls m ((X.tr g).take j) := by
  have he' : (X.tr g)[j]? = some x := he
  rw [List.take_add_one, he', Option.toList_some, okPolls_snoc, okPoll_notWait hx]
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof
