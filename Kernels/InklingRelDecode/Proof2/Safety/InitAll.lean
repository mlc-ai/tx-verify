-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvInit
public import Kernels.InklingRelDecode.Proof2.Safety.KvDecl

@[expose] public section

/-! # The twelve barriers are initialized first and published to every use

`Safety/KvInit.lean` proved `InitFirst` for the six ring barriers. This file extends it to all
twelve barriers of a CTA and to the two safety fields about initialization:

* `UseAt`: a state that uses a barrier: a ring user (`UserAt`: a prologue state after `bar2`, a
  loader or MMA state) or a state of the softmax region or the epilogue, which has made a
  barrier-1 event (`c1_inv`);
* `use_info`: every use of an mbarrier (`UsesMbar`) other than an initialization is an event of a
  `UseAt` state on a barrier of the thread's own CTA (`IsBar`), read off the shapes: arrivals
  (`arrive_use`), polls (`wait_use`), commits (`commit_use`) and copies (`copy_ring_ev`);
* `pub_use`, `init_exists_use`: the initialization is published to such a use (barrier 0's third
  instance or barrier 1's first) and exists once a use does;
* `all_initFirst`: `InitFirst` for each of the twelve barriers; `mbar_init`:
  `¬ MbarUninit L X`; `objects_published`: every record lies in a published lifetime. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Barriers and users -/

/-- `mo` is one of the twelve barriers of CTA `c`. -/
def IsBar (L : Launch) (c : Nat) (mo : Loc) : Prop := ∃ b : Proof.EvD.Bar, mo = b.loc L c

theorem isBar_kvReady (c : Nat) {s : Nat} (hs : s < 3) : IsBar L c (Proof.EvW.kvReady L c s) :=
  ⟨.kvReady ⟨s, hs⟩, by simp [Proof.EvW.kvReady, Proof.EvW.barLoc, Proof.EvW.kvReadyOff,
    Proof.EvD.Bar.loc, Proof.EvD.Bar.off]⟩

theorem isBar_kvEmpty (c : Nat) {s : Nat} (hs : s < 3) : IsBar L c (Proof.EvW.kvEmpty L c s) :=
  ⟨.kvEmpty ⟨s, hs⟩, by simp [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff,
    Proof.EvD.Bar.loc, Proof.EvD.Bar.off]⟩

theorem isBar_loc (c : Nat) (b : Proof.EvD.Bar) : IsBar L c (b.loc L c) := ⟨b, rfl⟩

/-- **A state that uses a barrier**: a ring user, or a state of the softmax region or the
epilogue. -/
def UseAt (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  UserAt Q L X g k ∨ ∃ tm bw dt τ n, Frame.stateAt (thread Q L) X g k =
    some (some (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, τ⟩⟩, n))

/-- A state of the softmax region or the epilogue has made a barrier-1 event. -/
theorem tail_c1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {tm : Nat} {bw : Value}
    {dt : Proof.ProA.Dat} {τ : Tail.St} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, τ⟩⟩, n))) :
    1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) := by
  have h := c1_inv hp hX hg k hk _ hσ
  cases τ with
  | sm d =>
    have h' : _ = smPh d := h
    simp only [smPh] at h'
    split at h' <;> omega
  | epi d =>
    have h' : _ = epiPh d := h
    simp only [epiPh] at h'
    split at h' <;> omega

/-! ### The uses of a barrier, by kind -/

/-- **An arrival** is a use on a barrier of the thread's CTA. -/
theorem arrive_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {mo : Loc} {tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive mo tx cnt rel sc⟩) :
    UseAt Q L X g k ∧ IsBar L (g / L.block) mo := by
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hg := Frame.lt_of_get hX he
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := arr_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_arr st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
          rcases pro_ev_kv hp (hJ : ProRef Q L g tm bw d n) hat hi.1 hxd hc hf with
            ⟨b, hs, hk⟩ | ⟨b, j, hs, a, sp, hk, -⟩ | ⟨hna, -⟩
          · simp only [Kind.arrive.injEq] at hk
            obtain ⟨rfl, -⟩ := hk
            exact ⟨.inl (.inl ⟨tm, bw, d, n, hσ, by rw [hs]; fin_cases b <;> decide⟩),
              isBar_kvReady _ b.isLt⟩
          · cases hk
          · exact absurd rfl (hna _ _ _ _ _)
        · cases τ with
          | sm d =>
            have hs := sm_arr d.site hpc
            have h' : Proof.Sm.Shape L g d ⟨pc, .arrive mo tx cnt rel sc⟩ := hev
            simp only [Proof.Sm.Shape, hs] at h'
            obtain ⟨-, h'⟩ := h'
            simp only [Event.mk.injEq, Kind.arrive.injEq] at h'
            obtain ⟨-, rfl, -⟩ := h'
            exact ⟨.inr ⟨tm, bw, _, _, n, hσ⟩, isBar_loc _ _⟩
          | epi d => exact (epi_arr d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_arr d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          simp only [Proof.EvW.LdShape, hs, Event.mk.injEq, Kind.arrive.injEq] at hsh
          obtain ⟨-, rfl, -⟩ := hsh
          exact ⟨.inl (.inr (.inl ⟨w, d, P, n, hσ⟩)), isBar_kvReady _ (Nat.mod_lt _ (by omega))⟩
        | worker w => exact (worker_arr w.site hpc).elim
        | idle d => exact (idle_arr d.site hpc).elim
        | mma d P => exact (mma_arr d.site hpc).elim
        | exit x => exact (exitsite_arr x.site hpc).elim
    · exact hJ.elim

/-- **A commit's target** is a barrier of the thread's CTA, notified from an MMA state. -/
theorem commit_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {sp : TcCommit.Spec} (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    {r : Fin 16} {mo : Loc} (ht : TcCommit.target sp r = some mo) :
    UseAt Q L X g k ∧ IsBar L (g / L.block) mo := by
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hg := Frame.lt_of_get hX he
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := commit_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r', d⟩
    · exact (startup_commit st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        exfalso
        rcases d with d | ⟨_ | _, τ⟩
        · exact proA_commit d.site hpc
        · cases τ with
          | sm d => exact sm_commit d.site hpc
          | epi d => exact epi_commit d.site hpc
        · exact hJ.elim
      | worker w =>
        cases d with
        | mma d P =>
          have hsh : Proof.EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩ := hev
          refine ⟨.inl (.inr (.inr ⟨w, d, P, n, hσ⟩)), ?_⟩
          rcases mma_commit d.site hpc with hs | hs | hs | hs <;>
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.tc.injEq,
              TcKind.commit.injEq] at hsh <;> obtain ⟨-, rfl⟩ := hsh <;>
            obtain ⟨-, rfl⟩ := target_commitSpec ht
          · exact ⟨.sReady ⟨d.i % 2, Nat.mod_lt _ (by omega)⟩, by
              simp [Proof.EvW.sReady, Proof.EvW.barLoc, Proof.EvW.sReadyOff, Proof.EvD.Bar.loc,
                Proof.EvD.Bar.off]⟩
          · exact ⟨.kvEmpty ⟨(d.i - 1) % 3, Nat.mod_lt _ (by omega)⟩, by
              simp [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff,
                Proof.EvD.Bar.loc, Proof.EvD.Bar.off]⟩
          · exact ⟨.oDone, by
              simp [Proof.EvW.oDone, Proof.EvW.barLoc, Proof.EvW.oDoneOff, Proof.EvD.Bar.loc,
                Proof.EvD.Bar.off]⟩
          · exact ⟨.oFinal, by
              simp [Proof.EvW.oFinal, Proof.EvW.barLoc, Proof.EvW.oFinalOff, Proof.EvD.Bar.loc,
                Proof.EvD.Bar.off]⟩
        | worker w => exact (worker_commit w.site hpc).elim
        | idle d => exact (idle_commit d.site hpc).elim
        | loader d P => exact (loader_commit d.site hpc).elim
        | exit x => exact (exitsite_commit x.site hpc).elim
    · exact hJ.elim

/-- **A poll** is a use on a barrier of the thread's CTA. -/
theorem wait_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc p : Nat} {mo : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait mo p ok acq sc⟩) :
    UseAt Q L X g k ∧ IsBar L (g / L.block) mo := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := wait_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r', d⟩
    · exact (startup_wait st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact (proA_wait d.site hpc).elim
        · refine ⟨.inr ⟨tm, bw, _, τ, n, hσ⟩, ?_⟩
          cases τ with
          | sm d =>
            rcases sm_wait d.site hpc with hs | hs
            · have h' : Proof.Sm.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
              simp only [Proof.Sm.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨ok', -, rfl, -⟩ := h'
              exact isBar_loc _ _
            · obtain ⟨ok', h'⟩ := Proof.Sm.shape_waitO (Proof.ProA.sharedOk_of_pre hp)
                (sm_fired hat hi hc hf) hs
              simp only [Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨-, rfl, -⟩ := h'
              exact isBar_loc _ _
          | epi d =>
            have hs := epi_wait d.site hpc
            have h' : Proof.Epi.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
            simp only [Proof.Epi.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
            obtain ⟨ok', -, rfl, -⟩ := h'
            have hM : Proof.Epi.Means Q L g d.pr := tm_means hp hX hg k hlen _ hσ
            have hmb := hM.mb
            simp only [Proof.EvD.Bar.off] at hmb
            rw [Nat.mod_eq_of_lt (by omega)] at hmb
            refine ⟨.oFinal, ?_⟩
            simp only [Proof.EvD.Bar.loc, Proof.EvD.Bar.off]
            rw [hmb]
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_wait d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          simp only [Proof.EvW.LdShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh
          obtain ⟨ok', -, rfl, -⟩ := hsh
          exact ⟨.inl (.inr (.inl ⟨w, d, P, n, hσ⟩)), isBar_kvEmpty _ (Nat.mod_lt _ (by omega))⟩
        | mma d P =>
          refine ⟨.inl (.inr (.inr ⟨w, d, P, n, hσ⟩)), ?_⟩
          have hsh : Proof.EvW.MmShape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
          rcases mma_wait d.site hpc with hs | hs <;>
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh <;>
            obtain ⟨ok', -, rfl, -⟩ := hsh
          · exact isBar_kvReady _ (Nat.mod_lt _ (by omega))
          · exact ⟨.pReady ⟨(d.i - 1) % 2, Nat.mod_lt _ (by omega)⟩, by
              simp [Proof.EvW.pReady, Proof.EvW.barLoc, Proof.EvW.pReadyOff, Proof.EvD.Bar.loc,
                Proof.EvD.Bar.off]⟩
        | worker w => exact (worker_wait w.site hpc).elim
        | idle d => exact (idle_wait d.site hpc).elim
        | exit x => exact (exitsite_wait x.site hpc).elim
    · exact hJ.elim

/-- **Every use of a barrier other than an initialization** is an event of a `UseAt` state on a
barrier of the thread's CTA. -/
theorem use_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {e : EvId}
    {mo : Loc} (hu : X.UsesMbar e mo) (hni : ∀ c, ¬ X.MbInit e mo c) :
    e.2 < (X.tr e.1).length ∧ UseAt Q L X e.1 e.2 ∧ IsBar L (e.1 / L.block) mo := by
  have hlen : ∀ {i : EvId} {ev : Event}, X.get i = some ev → i.2 < (X.tr i.1).length :=
    fun he => (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨g, k⟩ := e
  rcases hu with ⟨tx, count, rel, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, -⟩ | ⟨noinc, pc, he⟩ |
    ⟨s, rank, ⟨pc, he⟩, htg⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ | ⟨address, s, ⟨pc, he⟩, rfl⟩ |
    ⟨s, targets, c, ⟨pc, he⟩, -⟩ | ⟨count, hin⟩
  · exact ⟨hlen he, arrive_use hp hX he⟩
  · exact absurd he (no_copy hX)
  · exact absurd he (no_asyncArrive hX)
  · exact ⟨hlen he, commit_use hp hX he htg⟩
  · exact ⟨hlen he, wait_use hp hX he⟩
  · exact absurd he (no_inval hX)
  · obtain ⟨⟨-, s', hs', hmo, -⟩, hU⟩ := copy_ring_ev hp hX he
    exact ⟨hlen he, .inl hU, by rw [hmo]; exact isBar_kvReady _ hs'⟩
  · exact absurd he (no_clc hX)
  · exact absurd hin (hni count)

/-- **A record's issuer**: of a record other than an initialization's, an event that uses the
object and does not initialize it (as the first tree's `Bar.record_user`). -/
theorem record_issuer (hX : Consistent L kernel Assumptions.all m X) {mo : Loc}
    {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects mo) (hna : ∀ n, r.action ≠ .init n) :
    X.UsesMbar r.id.issuer mo ∧ ∀ n, ¬ X.MbInit r.id.issuer mo n := by
  cases record_source hX.tma.2.2.1 hr with
  | init hid he ha => exact absurd ha (hna _)
  | inval hid he ha => exact absurd he (no_inval hX)
  | arrive hid he ha =>
    refine ⟨by rw [hid]; exact .inl ⟨_, _, _, _, _, he⟩, fun n ⟨pc', h⟩ => ?_⟩
    rw [hid] at h
    simp only [AsyncCopy.Ref.issuer] at h
    rw [he] at h
    cases h
  | wait hid he ha =>
    refine ⟨by rw [hid]; exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))),
      fun n ⟨pc', h⟩ => ?_⟩
    rw [hid] at h
    simp only [AsyncCopy.Ref.issuer] at h
    rw [he] at h
    cases h
  | increment hid he ha => exact absurd he (no_asyncArrive hX)
  | @tensor i pc a sp hid he hm ha =>
    subst hm
    refine ⟨by rw [hid]; exact Execution.UsesMbar.of_tensor ⟨_, he⟩, fun n ⟨pc', h⟩ => ?_⟩
    rw [hid] at h
    simp only [AsyncCopy.Ref.issuer] at h
    rw [he] at h
    cases h
  | arriveOn hid he hm hn ha => exact absurd he (no_asyncArrive hX)
  | bulk hid he hc hn ha => exact absurd he (no_copy hX)
  | @commit i pc sp rank hid he ht ha =>
    refine ⟨by rw [hid]; exact .inr (.inr (.inr (.inl ⟨sp, rank, ⟨pc, he⟩, ht⟩))),
      fun n ⟨pc', h⟩ => ?_⟩
    rw [hid] at h
    simp only [AsyncCopy.Ref.issuer] at h
    rw [he] at h
    cases h
  | clc hid he hm htg ha => exact absurd he (no_clc hX)

/-! ### Publication and existence -/

/-- **An initialization is published to a use.** -/
theorem pub_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {I kI pcI : Nat} {l : Loc} {c : Nat} (hI : X.get (I, kI) = some ⟨pcI, .mbInit l c⟩)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UseAt Q L X g k)
    (hsame : SameCta L I g) : baseCausality L X (I, kI) (g, k) := by
  have hb : L.block = 256 := hp.block
  rcases hU with hU | ⟨tm, bw, dt, τ, n, hσ⟩
  · exact pub_of hp hX hI hk hU hsame
  · obtain ⟨j, -, -, hw, -, -, hc0, hc1⟩ := init_info hp hX hI
    have h1' := tail_c1 hp hX hsame.2.1 hk hσ
    exact bar1_handoff hp hX I g kI k ⟨hsame, by
      simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega, trivial⟩ hk (by dsimp only; omega)

/-- **A thread with a barrier-1 event has passed barrier 1's first instance**, at which every
thread of warps 0 to 3 of its CTA has every election's facts. -/
theorem pass_c1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length)
    (h1' : 0 + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1))
    {T : Nat} (hT : T / L.block = g / L.block) (hT128 : T % L.block < 128) :
    ∃ i, ∀ j, ElF L T j ((X.tr T).take i) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨j0, pc0, c0', md0, hj0, hget0, hc0⟩ :=
    nth_bar (X := X) (g := g) (q := 0) (f := k) (id := 1) h1'
  have hmd : md0 = .sync := by
    cases md0 with
    | sync => rfl
    | arrive => exact absurd hget0 (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
  subst hmd
  have hcn : c0' = none := ((bar1_sources hp hX) (g, j0) pc0 c0' ⟨.sync, hget0⟩ hg).2
  subst hcn
  have hf : X.IsBarrier (g, j0) 1 none pc0 := hget0
  obtain ⟨i, pci, mi, hgeti, -⟩ := (bar1_sources hp hX).member_arrival_any hX
    (bar1_shape hp) hf (by dsimp only; omega) (g := T) hT
    (by simp only [Finset.mem_range, CtaBarrier.warps, hb]; omega)
    (fun hex => by
      obtain ⟨i, pc', hb', hc'⟩ := bar1Exits hp hX hf (by dsimp only; omega) hT hex
      exact ⟨i, pc', .sync, hb', hc'⟩)
  exact ⟨i, elF_at_bar hp hX hgeti hT128 (.inl rfl)⟩

/-- A use's CTA has passed the instance that publishes the initializations. -/
theorem use_pass (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UseAt Q L X g k) {T : Nat}
    (hT : T / L.block = g / L.block) (hT128 : T % L.block < 128) :
    ∃ i, ∀ j, ElF L T j ((X.tr T).take i) := by
  rcases hU with hU | ⟨tm, bw, dt, τ, n, hσ⟩
  · exact user_pass hp hX hk hU hT hT128
  · have hg := thread_lt_of_len hX hk
    exact pass_c1 hp hX hg hk (by have := tail_c1 hp hX hg hk hσ; omega) hT hT128

/-- **The initialization of barrier `j` of a CTA exists** once every thread of warps 0 to 3 of
the CTA has passed an instance with every election's facts. -/
theorem init_exists_of_pass (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hP : ∀ T, T / L.block = g / L.block → T % L.block < 128 →
      ∃ i, ∀ j, ElF L T j ((X.tr T).take i)) (j : Fin 12) :
    ∃ I kI, I / L.block = g / L.block ∧ X.get (I, kI) = some (initEv L I j) := by
  have hb : L.block = 256 := hp.block
  set c := g / L.block with hc
  have hT0 : c * L.block < L.threads := by
    unfold Launch.threads
    have : c < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    nlinarith
  have hT0c : c * L.block / L.block = c := by
    rw [Nat.mul_div_cancel _ (by omega)]
  obtain ⟨i0, hE0⟩ := hP (c * L.block) (by rw [hT0c]) (by rw [Nat.mul_mod_left]; omega)
  obtain ⟨k0, inst, ld, hk0, -⟩ := hE0 j
  obtain ⟨-, hget0⟩ := get_of_take hk0
  obtain ⟨-, -, hmem⟩ := hX.elect.1 _ _ _ _ _ hget0
  have hld : ld < 32 := hmem.1
  set I := c * L.block + ld with hI
  have hIt : I < L.threads := by
    unfold Launch.threads
    have : c < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    nlinarith
  have hIc : I / L.block = c := by
    rw [hI, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
    simp
  have hImod : I % L.block = ld := by
    rw [hI, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨i1, hE1⟩ := hP I (by rw [hIc]) (by omega)
  obtain ⟨k1, inst1, ld1, hk1, hpost⟩ := hE1 j
  obtain ⟨-, hget1⟩ := get_of_take hk1
  have hsw : SameWarp L (c * L.block) I :=
    ⟨⟨hT0, hIt, by rw [hT0c, hIc]⟩, by rw [Nat.mul_mod_left, hImod]; omega⟩
  have heq := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hget0 hget1 hsw
  obtain ⟨kI, hkI⟩ := hpost (by rw [laneOf_w0 (by omega), hImod, heq]) (by omega)
  obtain ⟨-, hgetI⟩ := get_of_take hkI
  exact ⟨I, kI, hIc, hgetI⟩

/-- **The initialization of barrier `j` of a CTA exists once a use in the CTA exists.** -/
theorem init_exists_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length) (hU : UseAt Q L X g k) (j : Fin 12) :
    ∃ I kI, I / L.block = g / L.block ∧ X.get (I, kI) = some (initEv L I j) :=
  init_exists_of_pass hp hX (thread_lt_of_len hX hk)
    (fun _ hT hT128 => use_pass hp hX hk hU hT hT128) j

/-- **The initialization of barrier `j` of a CTA exists once a thread of the CTA has made a
barrier-1 event.** -/
theorem init_exists_c1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length)
    (h1 : 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) (j : Fin 12) :
    ∃ I kI, I / L.block = g / L.block ∧ X.get (I, kI) = some (initEv L I j) :=
  init_exists_of_pass hp hX (thread_lt_of_len hX hk)
    (fun _ hT hT128 => pass_c1 hp hX (thread_lt_of_len hX hk) hk (by omega) hT hT128) j

/-! ### The twelve barriers -/

/-- Every barrier is one of the twelve the prologue initializes. -/
theorem bar_idx (b : Proof.EvD.Bar) : ∃ j : Fin 12, Proof.ProA.initBar j.val = b := by
  cases b with
  | kvReady s => fin_cases s <;> first | exact ⟨0, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨4, rfl⟩
  | kvEmpty s => fin_cases s <;> first | exact ⟨1, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨5, rfl⟩
  | sReady s => fin_cases s <;> first | exact ⟨6, rfl⟩ | exact ⟨8, rfl⟩
  | pReady s => fin_cases s <;> first | exact ⟨7, rfl⟩ | exact ⟨9, rfl⟩
  | oDone => exact ⟨10, rfl⟩
  | oFinal => exact ⟨11, rfl⟩

/-- **The initialization of barrier `j` of CTA `c`, once the object has a record**: one event,
the object's only initialization, published to every other record's issuer. -/
theorem init_pub (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (c : Nat)
    (j : Fin 12) {r : MBarrier.Record AsyncCopy.Ref}
    (hrm : r ∈ X.objects ((Proof.ProA.initBar j.val).loc L c)) :
    ∃ E pcE, X.get E = some ⟨pcE, .mbInit ((Proof.ProA.initBar j.val).loc L c) 1⟩ ∧
      (∀ i pc n, X.get i = some ⟨pc, .mbInit ((Proof.ProA.initBar j.val).loc L c) n⟩ →
        i = E ∧ n = 1) ∧
      ∀ s ∈ X.objects ((Proof.ProA.initBar j.val).loc L c), (∀ n, s.action ≠ .init n) →
        InitPublished L X E s.id.issuer ((Proof.ProA.initBar j.val).loc L c) := by
  set mo := (Proof.ProA.initBar j.val).loc L c with hmo
  have hcta : ∀ s ∈ X.objects mo, (∀ n, s.action ≠ .init n) →
      s.id.issuer.2 < (X.tr s.id.issuer.1).length ∧ UseAt Q L X s.id.issuer.1 s.id.issuer.2 ∧
        c = s.id.issuer.1 / L.block := by
    intro s hs hna
    obtain ⟨hu, hni⟩ := record_issuer hX hs hna
    obtain ⟨hk, hU, b, hb⟩ := use_info hp hX hu hni
    exact ⟨hk, hU, by have := congrArg Loc.cta hb; simpa [hmo, Proof.EvD.Bar.loc] using this⟩
  obtain ⟨E, pcE, hE⟩ : ∃ E pcE, X.get E = some ⟨pcE, .mbInit mo 1⟩ := by
    by_cases hi : ∃ n, r.action = .init n
    · obtain ⟨n, ha⟩ := hi
      cases record_source hX.tma.2.2.1 hrm with
      | @init g k pc c' hid he ha' =>
        obtain ⟨-, -, rfl, -⟩ := init_info hp hX he
        exact ⟨(g, k), pc, he⟩
      | _ => simp_all
    · push Not at hi
      obtain ⟨hk, hU, hc⟩ := hcta r hrm hi
      obtain ⟨I, kI, hIc, hget⟩ := init_exists_use hp hX hk hU j
      refine ⟨(I, kI), (ProA.Site.init j).pc, ?_⟩
      rw [hget]
      simp only [initEv, hIc, ← hc, hmo]
  obtain ⟨g0, k0⟩ := E
  have hg0 := Frame.lt_of_get hX hE
  refine ⟨(g0, k0), pcE, hE, fun i pc n hi => ?_, fun s hs hna => ?_⟩
  · obtain ⟨i1, i2⟩ := i
    obtain ⟨h1, -⟩ := init_unique hp hX hi hE
    obtain ⟨-, h2⟩ := init_unique hp hX hi hi
    exact ⟨h1, h2⟩
  · obtain ⟨hk, hU, hc⟩ := hcta s hs hna
    obtain ⟨j', hl, -⟩ := init_info hp hX hE
    have hc0 : g0 / L.block = c := by
      have := congrArg Loc.cta hl
      simpa [hmo, Proof.EvD.Bar.loc] using this.symm
    exact .inl (pub_use hp hX hE hk hU ⟨hg0, thread_lt_of_len hX hk, hc0.trans hc⟩)

/-- **Each of the twelve barriers of a CTA is initialized first.** -/
theorem all_initFirst (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (c : Nat)
    (b : Proof.EvD.Bar) : PairTmaRing.InitFirst X (b.loc L c) 1 := by
  obtain ⟨j, rfl⟩ := bar_idx b
  intro r hrm
  obtain ⟨E, pcE, hE, hsite, hpub⟩ := init_pub hp hX c j hrm
  exact Proof.Mbar.initFirst_of_published hX ⟨pcE, hE⟩ validCount_one' hsite hpub r hrm

/-- **`Safety.Protocol.objectsPublished`**: every record of an mbarrier lies in an initialized
lifetime published to its issue. -/
theorem objects_published (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ mo r, r ∈ X.objects mo → ObjectPublished L X mo r := by
  intro mo r hr
  -- the object is a barrier
  obtain ⟨c, j, rfl⟩ : ∃ c, ∃ j : Fin 12, mo = (Proof.ProA.initBar j.val).loc L c := by
    by_cases hi : ∃ n, r.action = .init n
    · obtain ⟨n, ha⟩ := hi
      cases record_source hX.tma.2.2.1 hr with
      | @init g k pc c' hid he ha' =>
        obtain ⟨j, hl, -⟩ := init_info hp hX he
        exact ⟨_, j, hl⟩
      | _ => simp_all
    · push Not at hi
      obtain ⟨hu, hni⟩ := record_issuer hX hr hi
      obtain ⟨-, -, b, hb⟩ := use_info hp hX hu hni
      obtain ⟨j, hj⟩ := bar_idx b
      exact ⟨_, j, by rw [hb, hj]⟩
  obtain ⟨E, pcE, hE, hsite, hpub⟩ := init_pub hp hX c j hr
  exact Proof.Mbar.objectPublished_of_init hX ⟨pcE, hE⟩ validCount_one' hsite
    (fun v m' ⟨pc, h⟩ => no_inval hX h) hpub r hr

/-- **`Safety.Protocol.mbarInit`**: every use of an mbarrier has an initialization published to
it. -/
theorem mbar_init (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ¬ MbarUninit L X := by
  rintro ⟨⟨g, k⟩, mo, hu, hni, hnp⟩
  obtain ⟨hk, hU, b, rfl⟩ := use_info hp hX hu hni
  obtain ⟨j, rfl⟩ := bar_idx b
  obtain ⟨I, kI, hIc, hget⟩ := init_exists_use hp hX hk hU j
  have hg := thread_lt_of_len hX hk
  have hI := Frame.lt_of_get hX hget
  refine hnp ⟨(I, kI), 1, ⟨(ProA.Site.init j).pc, ?_⟩,
    .inl (pub_use hp hX hget hk hU ⟨hI, hg, hIc⟩)⟩
  rw [hget]
  simp only [initEv, hIc]

end
end PTX.Kernels.InklingRelDecode.Proof2
