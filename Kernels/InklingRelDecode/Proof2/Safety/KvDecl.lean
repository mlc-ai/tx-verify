-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvInit
public import Lemmas.Flow.NthEv
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Protocol.SingleTmaRing.Hyp

@[expose] public section

/-! # The KV ring as a declaration (`SingleTmaRing.Decl`)

The ring of CTA `c` (`kvDecl`): three slots, full barrier `kv_ready s`, empty barrier `kv_empty s`;
lane 0 of warp 6 arrives, the lane of warp 6 that leads its elections copies (`leadT … 6`) and
the one of warp 7 commits (`leadT … 7`); eight copies of 8192 bytes per use; slot `s` is preloaded
when `s < num_pre`, by thread 0's first arrival on `kv_ready s` and the first four copies to it of
the elected lanes of warps 0 and 1 (`preCp`: a position past the trace's end when the lane made
fewer, so that the eight positions are distinct).

* the code facts: every poll heads a canonical spin (`poll_spins`), no bulk copy, no
  `cp.async.mbarrier.arrive`, no cluster launch control, no `mbarrier.inval` (`Lib/NoEvents.lean`);
* `kv_events`: `Decl.Events` from the ring's events by state (`arrive_ring`, `copy_ring_ev`,
  `commit_ring`, `wait_ring`) and `kv_initFirst`; so `kv_hyp`: `SingleTmaRing.Hyp` for every slot
  (`Decl.hyp`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Every poll is a canonical spin -/

/-- The poll at `pc` heads a canonical spin of the kernel. -/
def spinOk (pc : Nat) : Bool :=
  (kernel.spinExit? pc).isSome &&
    (match kernel.pollDst pc with
      | some p => kernel.spinPred p
      | none => false)

theorem kernel_spins : waitPcs.all spinOk = true := by decide +kernel

theorem canonical_of_spinOk {pc : Nat} (h : spinOk pc = true) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  unfold spinOk at h
  cases hs : kernel.spinExit? pc with
  | none => simp [hs] at h
  | some ex =>
    cases hp : kernel.pollDst pc with
    | none => simp [hs, hp] at h
    | some p =>
      simp only [hs, hp, Option.isSome_some, Bool.true_and] at h
      exact ⟨ex, hs, p, hp, h⟩

/-- **Every poll fires from a canonical spin.** -/
theorem poll_spins (hX : Consistent L kernel Assumptions.all m X) {e : EvId} {pc : Nat} {mo : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait mo p ok acq sc⟩) : ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · have hmem := wait_pc (g := e.1) hc hf rfl
    exact canonical_of_spinOk (List.all_eq_true.mp kernel_spins _ hmem)

/-! ### The lanes of the declaration -/

theorem leadT_cta (hc : c < L.grid) {w : Nat} (hw : w < 8) (hb : L.block = 256) :
    leadT L X c w / L.block = c ∧ leadT L X c w < L.threads ∧
      leadT L X c w % L.block / 32 = w := by
  unfold leadT
  split
  · rename_i h
    obtain ⟨h1, h2, h3, -⟩ := Classical.choose_spec h
    exact ⟨h2, h1, h3⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hb, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
      simp
    · unfold Launch.threads; rw [hb]; nlinarith
    · rw [hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega

/-- The position of `g`'s `n`-th event satisfying `p`, past the end of its trace (and distinct for
distinct `n`) when it made fewer. -/
def nthPos (X : Execution) (p : Event → Bool) (g n : Nat) : Nat :=
  if n < (X.tr g).countP p then nthEv X p g n else (X.tr g).length + n

theorem nthPos_eq {p : Event → Bool} {j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hp : p e = true) : nthPos X p g (((X.tr g).take j).countP p) = j := by
  have hlt : ((X.tr g).take j).countP p < (X.tr g).countP p := by
    have h1 := countP_take_succ he hp
    have h2 := countP_take_mono p (X.tr g) (show j + 1 ≤ (X.tr g).length from
      (List.getElem?_eq_some_iff.mp he).1)
    rw [List.take_length] at h2
    omega
  unfold nthPos
  rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  exact nthEv_eq he hp

theorem nthPos_inj {p : Event → Bool} {n n' : Nat} (h : nthPos X p g n = nthPos X p g n') :
    n = n' := by
  unfold nthPos at h
  have hlen : ∀ {k}, k < (X.tr g).countP p → nthEv X p g k < (X.tr g).length := by
    intro k hk
    obtain ⟨e, he, -, -⟩ := nthEv_spec (X := X) hk
    exact (List.getElem?_eq_some_iff.mp he).1
  split at h <;> split at h
  · rename_i h1 h2
    obtain ⟨e, he, hp, hc⟩ := nthEv_spec (X := X) h1
    obtain ⟨e', he', hp', hc'⟩ := nthEv_spec (X := X) h2
    rw [← hc, ← hc', h]
  · rename_i h1 _; have := hlen h1; omega
  · rename_i _ h2; have := hlen h2; omega
  · omega

/-- The thread 0 of CTA `c`. -/
abbrev t0 (L : Launch) (c : Nat) : Nat := c * L.block

/-- The preloading copy `i` of slot `s`: the `(i % 4)`-th copy to `kv_ready s` of the elected lane
of warp `i / 4`. -/
def preCp (L : Launch) (X : Execution) (c s : Nat) (i : Nat) : EvId :=
  (leadT L X c (i / 4), nthPos X (issuesTo (Proof.EvW.kvReady L c s)) (leadT L X c (i / 4)) (i % 4))

/-- **The KV ring of CTA `c`.** -/
def kvDecl (Q : Params) (L : Launch) (X : Execution) (c : Nat) : SingleTmaRing.Decl where
  depth := 3
  full s := Proof.EvW.kvReady L c s
  empty s := Proof.EvW.kvEmpty L c s
  ap := t0 L c + 192
  cp := leadT L X c 6
  cm := leadT L X c 7
  n := 8
  bytes := 8192
  δ s := if s.val < npOf Q L (t0 L c) then 1 else 0
  pArr s := (t0 L c, nthPos X (arrivesOn (Proof.EvW.kvReady L c s)) (t0 L c) 0)
  pCp s i := preCp L X c s i

theorem npOf_cta {h : Nat} (hc : h / L.block = c) (hb : 0 < L.block) :
    npOf Q L h = npOf Q L (t0 L c) := by
  have : t0 L c / L.block = c := by simp [t0, Nat.mul_div_cancel _ hb]
  simp only [npOf, Proof.ProA.cta, hc, this]

theorem thread_eq {h : Nat} (hc : h / L.block = c) {r : Nat} (hr : h % L.block = r) :
    h = t0 L c + r := by
  have := Nat.div_add_mod h L.block
  rw [hc, hr] at this
  simp only [t0]; rw [Nat.mul_comm]; omega

theorem kvReady_cta {c c' s s' : Nat} (_hs : s < 3) (_hs' : s' < 3)
    (h : Proof.EvW.kvReady L c s = Proof.EvW.kvReady L c' s') : c = c' ∧ s = s' := by
  simp only [Proof.EvW.kvReady, Proof.EvW.barLoc, Proof.EvW.kvReadyOff, Loc.mk.injEq,
    true_and] at h
  omega

theorem kvEmpty_cta {c c' s s' : Nat} (_hs : s < 3) (_hs' : s' < 3)
    (h : Proof.EvW.kvEmpty L c s = Proof.EvW.kvEmpty L c' s') : c = c' ∧ s = s' := by
  simp only [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff, Loc.mk.injEq,
    true_and] at h
  omega

/-! ### The events of the declaration -/

/-- **The KV ring's thread-side events** (`SingleTmaRing.Decl.Events`), for a CTA of the grid. -/
theorem kv_events (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {c : Nat}
    (hc : c < L.grid) : (kvDecl Q L X c).Events L kernel Assumptions.all X .cta := by
  have hb : L.block = 256 := hp.block
  have hb0 : 0 < L.block := by omega
  have hlt : ∀ {h k : Nat} {e : Event}, X.get (h, k) = some e → h < L.threads :=
    fun he => Frame.lt_of_get hX he
  obtain ⟨h7c, h7t, h7w⟩ := leadT_cta (X := X) hc (w := 7) (by omega) hb
  obtain ⟨h6c, h6t, h6w⟩ := leadT_cta (X := X) hc (w := 6) (by omega) hb
  have ht0 : t0 L c < L.threads := by unfold Launch.threads t0; nlinarith
  have ht0c : t0 L c / L.block = c := by simp [t0, Nat.mul_div_cancel _ hb0]
  refine
    { δ_le := fun s => by simp only [kvDecl]; split <;> omega
      arrive := ?_
      arrive_empty := ?_
      issue := ?_
      issue_empty := ?_
      commit := ?_
      commit_full := ?_
      no_bulk := no_copy hX
      no_arriveOn := no_asyncArrive hX
      no_clc := no_clc hX
      no_inval := no_inval hX
      full_init := fun s => (kv_initFirst hp hX c s.isLt).1
      empty_init := fun s => (kv_initFirst hp hX c s.isLt).2
      full_parity := ?_
      empty_parity := ?_
      spins := fun w pc mo q acq sc' he => poll_spins hX he
      full_acq := ?_
      empty_acq := ?_
      cta := ?_
      pre_cta := ?_
      pre_ne := ?_
      pre_inj := ?_ }
  · -- arrivals on a full barrier
    intro s h j pc tx cnt rel sc' he
    have he' : X.get (h, j) = some ⟨pc, .arrive (Proof.EvW.kvReady L c s.val) tx cnt rel sc'⟩ :=
      he
    obtain ⟨⟨htx, hcnt, s', hs', hmo, hw⟩, -⟩ :=
      arrive_ring hp hX he' (inRing_kvReady c s.isLt)
    obtain ⟨hcc, rfl⟩ := kvReady_cta s.isLt hs' hmo
    refine ⟨by simp [kvDecl, SingleTmaRing.Decl.slot, SingleTmaRing.Slot.tx, htx], hcnt, ?_⟩
    rcases hw with ⟨h192, hbud⟩ | ⟨h0, hnp, hz⟩
    · left
      refine ⟨thread_eq hcc.symm h192, ?_⟩
      simp only [kvDecl]; rw [hcc]; exact hbud
    · right
      have hh := thread_eq hcc.symm h0
      simp only [Nat.add_zero] at hh
      refine ⟨?_, ?_⟩
      · simp only [kvDecl]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [← npOf_cta hcc.symm hb0]; exact hnp))]
      · simp only [kvDecl]
        rw [← hcc] at hz
        have hpe : arrivesOn (Proof.EvW.kvReady L c s.val)
            ⟨pc, .arrive (Proof.EvW.kvReady L c s.val) tx cnt rel sc'⟩ = true := by
          simp [arrivesOn, sourceArrive]
        have := nthPos_eq he' hpe
        unfold arrivals at hz
        rw [hz] at this
        rw [← hh, this]
  · -- no arrival on an empty barrier
    intro s h j pc tx cnt rel sc' he
    obtain ⟨⟨-, -, s', hs', hmo, -⟩, -⟩ := arrive_ring hp hX he (inRing_kvEmpty c s.isLt)
    exact kvReady_ne_kvEmpty hs' s.isLt hmo.symm
  · -- copies to a full barrier
    intro s h k pc al sp he hm
    obtain ⟨⟨hby, s', hs', hmo, -, hw⟩, -⟩ := copy_ring_ev hp hX he
    have hmo' : Proof.EvW.kvReady L c s.val = Proof.EvW.kvReady L (h / L.block) s' :=
      hm.symm.trans hmo
    obtain ⟨hcc, rfl⟩ := kvReady_cta s.isLt hs' hmo'
    refine ⟨hby, ?_⟩
    rcases hw with ⟨h6, hbud⟩ | ⟨hnp, hw2, hl, h4⟩
    · left
      simp only [kvDecl]
      refine ⟨by rw [hcc]; exact h6, ?_⟩
      rw [hcc]; exact hbud
    · right
      set q := ((X.tr h).take k).countP (issuesTo (Proof.EvW.kvReady L (h / L.block) s.val))
        with hq
      refine ⟨?_, ⟨4 * (h % L.block / 32) + q, by simp only [kvDecl]; omega⟩, ?_⟩
      · simp only [kvDecl]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [← npOf_cta hcc.symm hb0]; exact hnp))]
      · simp only [kvDecl, preCp]
        have hd : (4 * (h % L.block / 32) + q) / 4 = h % L.block / 32 := by omega
        have hmd : (4 * (h % L.block / 32) + q) % 4 = q := by omega
        rw [hd, hmd, hcc, ← hl]
        have hpe : issuesTo (Proof.EvW.kvReady L (h / L.block) s.val)
            ⟨pc, .tensorIssue al sp⟩ = true := by
          simp [issuesTo, hmo]
        rw [hq, nthPos_eq he hpe]
  · -- no copy to an empty barrier
    intro s h k pc al sp he hm
    obtain ⟨⟨-, s', hs', hmo, -⟩, -⟩ := copy_ring_ev hp hX he
    rw [hmo] at hm
    exact kvReady_ne_kvEmpty hs' s.isLt hm
  · -- commits to an empty barrier
    intro s h j pc sp r he ht
    obtain ⟨⟨hl, hr0, s', hs', hmo, hsp, hbud⟩, -⟩ :=
      commit_ring hp hX he ht (inRing_kvEmpty c s.isLt)
    obtain ⟨hcc, rfl⟩ := kvEmpty_cta s.isLt hs' hmo
    refine ⟨by simp only [kvDecl]; rw [hcc]; exact hl, Fin.ext hr0, by rw [hsp], ?_⟩
    rw [← hcc] at hbud; exact hbud
  · -- no commit to a full barrier
    intro s h j pc sp r he hft
    obtain ⟨⟨-, -, s', hs', hmo, -⟩, -⟩ := commit_ring hp hX he hft (inRing_kvReady c s.isLt)
    exact kvReady_ne_kvEmpty s.isLt hs' hmo
  · -- the full barrier's polls
    intro s h k pc p acq sc' he
    obtain ⟨⟨-, -, s', hs', ⟨hmo, -, hpar⟩ | ⟨hmo, -⟩⟩, -⟩ :=
      wait_ring hp hX he (inRing_kvReady c s.isLt)
    · obtain ⟨hcc, rfl⟩ := kvReady_cta s.isLt hs' hmo
      rw [← hcc] at hpar; exact hpar
    · exact absurd hmo (kvReady_ne_kvEmpty s.isLt hs')
  · -- the empty barrier's polls
    intro s h k pc p acq sc' he
    obtain ⟨⟨-, -, s', hs', ⟨hmo, -⟩ | ⟨hmo, -, hpar⟩⟩, -⟩ :=
      wait_ring hp hX he (inRing_kvEmpty c s.isLt)
    · exact absurd hmo.symm (kvReady_ne_kvEmpty hs' s.isLt)
    · obtain ⟨hcc, rfl⟩ := kvEmpty_cta s.isLt hs' hmo
      rw [npOf_cta hcc.symm hb0, ← hcc] at hpar
      exact hpar
  · intro s h k pc p acq sc' he
    obtain ⟨⟨hacq, hsc, -⟩, -⟩ := wait_ring hp hX he (inRing_kvReady c s.isLt)
    exact ⟨hacq, hsc⟩
  · intro s h k pc p acq sc' he
    obtain ⟨⟨hacq, hsc, -⟩, -⟩ := wait_ring hp hX he (inRing_kvEmpty c s.isLt)
    exact ⟨hacq, hsc⟩
  · intro a
    simp only [kvDecl]
    split
    · exact ⟨by unfold Launch.threads t0; nlinarith, h7t, by
        rw [h7c]; simp [t0, hb]; omega⟩
    · exact ⟨h6t, h7t, by rw [h6c, h7c]⟩
  · intro s _ i
    have hi8 : i.val < 8 := i.isLt
    simp only [kvDecl, preCp]
    obtain ⟨hc', ht', -⟩ := leadT_cta (X := X) hc (w := i.val / 4) (by omega) hb
    exact ⟨ht', h7t, by rw [hc', h7c]⟩
  · intro s _
    refine ⟨by simp only [kvDecl]; omega, fun i => ?_⟩
    have hi8 : i.val < 8 := i.isLt
    simp only [kvDecl, preCp]
    intro heq
    obtain ⟨-, -, hw⟩ := leadT_cta (X := X) hc (w := i.val / 4) (by omega) hb
    rw [heq, h6w] at hw
    omega
  · intro s _ i i' heq
    have hi8 : i.val < 8 := i.isLt
    have hi8' : i'.val < 8 := i'.isLt
    simp only [kvDecl, preCp, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    obtain ⟨-, -, hw⟩ := leadT_cta (X := X) hc (w := i.val / 4) (by omega) hb
    obtain ⟨-, -, hw'⟩ := leadT_cta (X := X) hc (w := i'.val / 4) (by omega) hb
    rw [h1] at hw
    rw [h1] at h2
    have := nthPos_inj h2
    apply Fin.ext
    omega

/-- **Every slot of the KV ring has the library's hypotheses.** -/
theorem kv_hyp (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {c : Nat}
    (hc : c < L.grid) (s : Fin 3) :
    SingleTmaRing.Hyp L kernel Assumptions.all X ((kvDecl Q L X c).slot s) .cta :=
  SingleTmaRing.Decl.hyp hX (kv_events hp hX hc) s

end
end PTX.Kernels.InklingRelDecode.Proof2
