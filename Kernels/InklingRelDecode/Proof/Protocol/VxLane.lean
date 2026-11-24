-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.VxElect
public import Lemmas.Protocol.ElectCount

@[expose] public section

/-!
# `Mbar.Route.lane_commit` (`Hs.LaneCommit`)

A lane `h` of the MMA warp and the committing lane `cm` of its CTA. The commit of `cm` to
`s_ready b` at the QK commit of iteration `I` follows `cm`'s election at `qkElect` of `I`
(`qk_elect_back`). Lane `h`'s election of the same instance (`ElectOrd.partner`) is at the same
position (`ElectOk`), so at `qkElect` of an iteration `I'` of `h`'s run (`elect_site_state`). The
two elections have one ordinal (`electOrdinal`). So have `cm`'s first election in its run and its
partner in `h`, which is in `h`'s run too: so `h` made at most as many elections before the entry
of its run as `cm` (`elect_cnt`, with the unique entry `Rd.mma_entry_unique`). Hence `I' ≥ I`, and
at `qkElect` of `I'` lane `h` has polled `p_ready b` `below2 b (I' - 1)` times (`Hs.mma_cnt`),
more than `j`. The return of the poll with `j` earlier ones precedes the election (a spinning
poll, `MbarRing.Poll.guard`), which precedes the commit (`elect_depStep`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Vx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Hs (cmOf MmaOf)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal commitSpec)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into QK step `j`: from the election of the iteration (step 0) or from step
`j - 1` of the iteration. -/
theorem next_qk_back {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    {j : Fin 8} (hs : d.site = .qk j) :
    (j.val = 0 ∧ d0.site = .qkElect ∧ d0.i = d.i) ∨
      (∃ j' : Fin 8, j'.val + 1 = j.val ∧ d0.site = .qk j' ∧ d0.i = d.i) := by
  obtain ⟨site, i, n, tm, pro⟩ := d0
  cases site
  case qk j' =>
    simp only [Mma.next, Mma.qkNext] at hn
    split at hn
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      simp only [Mma.Site.qk.injEq] at hs
      subst hs
      exact .inr ⟨j', rfl, rfl, rfl⟩
    · obtain rfl := Option.some.inj (Option.some.inj hn)
      simp at hs
  case qkElect =>
    simp only [Mma.next] at hn
    split at hn
    · split at hn
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        simp only [Mma.Site.qk.injEq] at hs
        subst hs
        exact .inl ⟨rfl, rfl, rfl⟩
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        simp only [Mma.afterQk, Mma.iterNext] at hs
        repeat' split at hs
        all_goals simp at hs
    · cases hn
  all_goals
    simp only [Mma.next] at hn
    (repeat' split at hn)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj hn))
    all_goals try (cases hn)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.pvNext] at hs
    all_goals (repeat' split at hs)
    all_goals simp at hs

/-- An event that is an election. -/
theorem elect_get {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hi : isElectEv e = true) :
    ∃ mask inst l, X.Elect (g, k) e.pc mask inst l := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [isElectEv, Bool.false_eq_true] at hi
  exact ⟨_, _, _, he⟩

/-- **From a QK step back to the election of its iteration.** -/
theorem qk_elect_back (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) :
    ∀ (n : Nat) {k : Nat} {d : Mma.D} {P : Loader.Pro} {j : Fin 8}, j.val = n →
      k < (X.tr g).length → St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
      ∃ (k' : Nat) (d' : Mma.D), k' < k ∧ St Q L X g k' = some (some (.w (.mma d' P))) ∧
        d'.site = .qkElect ∧ d'.i = d.i ∧
        ∃ mask inst l, X.Elect (g, k') Mma.Site.qkElect.pc mask inst l := by
  intro n
  induction n with
  | zero =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, -, he, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_qk_back hn hs with ⟨-, hq, hi⟩ | ⟨j', hj', -⟩
    · refine ⟨k0, d0, by omega, hs0, hq, hi, ?_⟩
      have hel := next_elect_kind (by rw [hq]; rfl) hn
      obtain ⟨mask, inst, l, hE⟩ := elect_get he hel
      have hpc := Frame.event_pc hf.sound hX he hs0
      have hpc' : e.pc = Mma.Site.qkElect.pc := by rw [hpc, ← hq]; rfl
      rw [hpc'] at hE
      exact ⟨mask, inst, l, hE⟩
    · omega
  | succ n ih =>
    intro k d P j hj hk hσ hs
    obtain ⟨k0, e, d0, hadj, -, -, hs0, hn⟩ :=
      mma_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    rcases next_qk_back hn hs with ⟨hz, -⟩ | ⟨j', hj', hs', hi⟩
    · omega
    · obtain ⟨k', d', hk', h1, h2, h3, h4⟩ := ih (j := j') (by omega) (by omega) hs0 hs'
      exact ⟨k', d', by omega, h1, h2, by rw [h3, hi], h4⟩

/-- **`Mbar.Route.lane_commit`** for the committing lane `cmOf L X c` and the MMA warp's lanes. -/
theorem laneCommit_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X) {c : Nat}
    (hc : c < L.grid) : Hs.LaneCommit L X c := by
  intro h b j i pc sp hh _ hb he hm hj
  have hcm : MmaOf L c (cmOf L X c) := Hs.cm_mma hpre hc
  have hg : cmOf L X c < L.threads := event_thread_lt hX he
  have hk : i < (X.tr (cmOf L X c)).length := len_of_get he
  obtain ⟨d, P, hσ, hcs⟩ := Hs.commit_state hpre hX hf he
  rcases hcs with ⟨hs, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    simp only [commitSpec] at hm
  rotate_left 1
  all_goals try hs_loc hm
  have hm' := hm
  simp only [EvW.sReady, Hs.barLoc_eq, EvW.sReadyOff] at hm'
  obtain ⟨hcc, hbi⟩ := hm'
  have hlead := Hs.electLead_take (lead_of_qkCommit hpre hX hf hk hσ hs) i
  obtain ⟨-, hC⟩ := Hs.mma_cnt hpre hX hf hR hg hk hσ
  have hcnt := (hC hlead ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take i)).1 b hb
  rw [hcc] at hcnt
  rw [hcnt] at hj
  simp only [SO.Mm.qkDone, hs] at hj
  -- the election of the iteration, before the commit
  obtain ⟨k7, d7, hk7, hσ7, hs7, hi7, -, -, -⟩ := exists_qk7 hpre hX hf hk hσ hs
  obtain ⟨ke, de, hke, hσe, hse, hie, mask, inst, l, hel⟩ :=
    qk_elect_back hX hf 7 (j := 7) rfl (by omega) hσ7 hs7
  rw [hi7] at hie
  obtain rfl := elect_full hX hel
  -- lane `h`'s election of the same instance, at the same position
  have hhl : h < L.threads := hh.1
  have hw : SameWarp L (cmOf L X c) h :=
    ⟨⟨hg, hhl, hcm.2.1.trans hh.2.1.symm⟩, by rw [hcm.2.2, hh.2.2]⟩
  obtain ⟨x, pc1, pc2, mask1, mask2, inst1, l1, l2, hel1, hel2⟩ :=
    ElectOrd.partner hX hw hel (_root_.PTX.electMember_full L h)
  have hel1' := hel1
  unfold Execution.Elect at hel hel1'
  rw [hel] at hel1'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at hel1'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hel1'
  obtain ⟨hpc2, -, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hel1 hel2 hw
  obtain ⟨dh, Ph, hσh, hsh⟩ := elect_site_state hX hf (t := .qkElect) rfl hel2 hpc2.symm
  -- the counts of elections
  have hord : ElectOrdinal L X := electOrdinal hX (ElectMutual.of_full fun he => elect_full hX he)
  have hoe := hord (e := (cmOf L X c, ke)) (f := (h, x)) hw hel1 hel2
  have hkx : x < (X.tr h).length := len_of_get hel2
  obtain ⟨k0c, d0c, hk0c, h0c, hs0c, hec, hrunc⟩ :=
    elect_cnt hpre hX hf hR hB hg (by omega) hσe
  obtain ⟨k0h, d0h, hk0h, h0h, hs0h, heh, -⟩ := elect_cnt hpre hX hf hR hB hhl hkx hσh
  simp only [elects, hse, hsh] at hec heh
  have hI : 1 ≤ d.i := by
    by_contra h0
    have : d.i = 0 := by omega
    rw [this] at hj
    simp only [below2] at hj
    omega
  -- the first election of the committing lane's run, and its partner in `h`
  obtain ⟨y, hyk, ev, hev, hiev, hcy⟩ := Flow.exists_nth isElectEv (X.tr (cmOf L X c))
    (n := elections X (cmOf L X c) k0c) (k := ke) (by
      show _ < elections X (cmOf L X c) ke
      omega)
  have hevg : X.get (cmOf L X c, y) = some ev := hev
  obtain ⟨masky, insty, ly, hely⟩ := elect_get hevg hiev
  obtain rfl := elect_full hX hely
  have hyk0 : k0c ≤ y := by
    by_contra hlt
    have h1 := ElectOrd.elections_succ hely
    have h2 := Flow.countP_take_mono isElectEv (X.tr (cmOf L X c)) (show y + 1 ≤ k0c by omega)
    simp only [elections] at h1 h2 hcy
    omega
  obtain ⟨dy, hσy⟩ := hrunc y hyk0 hyk
  obtain ⟨hely_s, hely_pc⟩ := elect_at_site hpre hX hf hely hσy
  obtain ⟨x', qc1, qc2, nask1, nask2, inst2, k1, k2, hy1, hy2⟩ :=
    ElectOrd.partner hX hw hely (_root_.PTX.electMember_full L h)
  have hy1' := hy1
  unfold Execution.Elect at hely hy1'
  rw [hely] at hy1'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at hy1'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hy1'
  obtain ⟨hqc, -, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hy1 hy2 hw
  obtain ⟨dh', Ph', hσh', -⟩ :=
    elect_site_state hX hf hely_s hy2 (hqc.symm.trans hely_pc)
  have hkx' : x' < (X.tr h).length := len_of_get hy2
  obtain ⟨k0h', d0h', hk0h', h0h', hs0h', heh', -⟩ := elect_cnt hpre hX hf hR hB hhl hkx' hσh'
  have hent : k0h' = k0h :=
    Rd.mma_entry_unique hpre hX hf hR (by omega) (by omega) h0h' hs0h' h0h hs0h
  rw [hent] at heh'
  have hoy := hord (e := (cmOf L X c, y)) (f := (h, x')) hw hy1 hy2
  -- so lane `h` is at `qkElect` of an iteration at least `I`
  have hge : d.i ≤ dh.i := by
    simp only [elections] at hec heh heh' hcy hoe hoy
    omega
  -- its polls of `p_ready b` before the election
  obtain ⟨hP, -⟩ := Hs.mma_cnt hpre hX hf hR hhl hkx hσh
  have hpol := hP b hb
  rw [hh.2.1] at hpol
  simp only [SO.Mm.pPolled, hsh] at hpol
  have hjp : j + 1 ≤ okPolls (pReady L c b) ((X.tr h).take x) := by
    rw [hpol]
    simp only [below2] at hj ⊢
    omega
  refine ⟨?_, ?_⟩
  · have := MbarRing.Poll.okPolls_mono (pReady L c b) (X.tr h) (show x ≤ (X.tr h).length by omega)
    rw [List.take_of_length_le (le_refl _)] at this
    omega
  · exact Relation.TransGen.head
      (DepStep.of_resumes L (MbarRing.Poll.guard (fun _ _ _ _ _ _ he' => Safety.poll_spins hX he')
        hkx hjp))
      (elect_depStep hX (sameWarp_symm hw) hel2 hel1 (by omega) hk)

/-- **`Hs.PkgRest`**, proved. -/
theorem pkgRest_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X) :
    Hs.PkgRest L X :=
  ⟨fun _ hc => laneCommit_of hpre hX hf hR hB hc, hB⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Vx
