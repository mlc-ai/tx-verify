-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxKReach
public import Kernels.InklingRelDecode.Proof2.Lib.KvCover
public import Kernels.InklingRelDecode.Proof.Interface.IpMmaTrace
public import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-!
# The MMAs of a released use cover its KV ring slot

`kv_cover`: before the MMA lane's commit to `kv_empty s` of CTA `c` (with `u` earlier commits to
it), a byte of slot `s` (its K region or its V region) is the B operand byte of an earlier MMA of
the lane, with as many earlier commits to `kv_empty s` and at least `u + 1` successful polls of
`kv_ready s`; a wait observing that MMA's completion finds the read performed.

* The commit is at `pvCommit1` of iteration `b + 1`, `b % 3 = s` (`commit_site`), and the lane led
  its elections (`Lp.commit_lead`).
* A byte of the K region is the B operand byte of QK step `j` (`k_cover`), and the lane was at QK
  step `j` of iteration `b` before the commit (`reach_rank`): `b < num_iters`. A byte of the V
  region is that of PV step `j` (`v_cover`), and the lane was at PV step `j` of iteration
  `b + 1`.
* The counts at both events are those of the lane's states (`lane_counts`, from
  `Ring.mma_counts_exec` with the anchor `Lp.mma_anchor_full`): `below s (b - 1) = below s b = u`
  commits, and `below s (b + 1) = u + 1` polls or more.
* The read is present once the MMA is observed complete (`observed_mmaRead`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty MmShape QkIssue PvIssue
  mmEnv_of_pre commitSpec)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The commit and the counts -/

/-- **A commit to `kv_empty s` of CTA `c`** is at `pvCommit1` of an iteration `i` with
`(i - 1) % 3 = s`, by a thread of the CTA. -/
theorem commit_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc c s : Nat} {sp : TcCommit.Spec} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = kvEmpty L c s) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site = .pvCommit1 ∧ c = g / L.block ∧ (d.i - 1) % 3 = s := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  have hsite : d.site = .pvCommit1 ∧ sp = commitSpec (g / L.block)
      (kvEmpty L (g / L.block) ((d.i - 1) % 3)) := by
    unfold MmShape at hsh
    cases hst : d.site <;> rw [hst] at hsh
    all_goals first
      | (simp at hsh; done)
      | (unfold QkIssue at hsh
         obtain ⟨_, _, _, _, _, _, hev⟩ := hsh
         simp at hev)
      | (unfold PvIssue at hsh
         obtain ⟨_, _, _, _, hev⟩ := hsh
         simp at hev)
      | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
         obtain ⟨-, rfl⟩ := hsh
         exact ⟨rfl, rfl⟩)
      | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
         obtain ⟨-, rfl⟩ := hsh
         simp [commitSpec, EvW.oFinal, EvW.sReady, kvEmpty, EvW.oDone, EvW.barLoc, EvW.oFinalOff,
           EvW.sReadyOff, EvW.kvEmptyOff, EvW.oDoneOff] at hm
         omega)
  obtain ⟨hs1, rfl⟩ := hsite
  simp only [commitSpec, kvEmpty, EvW.barLoc, EvW.kvEmptyOff, Loc.mk.injEq] at hm
  exact ⟨d, P, hσ, hs1, hm.2.1.symm, by omega⟩

/-- **The ring counts of the MMA lane at a state**: the successful polls of `kv_ready s` and the
commits to `kv_empty s` before an MMA state are those of the state. -/
theorem lane_polls (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P)))) {s : Nat}
    (hs : s < 3) :
    okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) = below s (Mm.polled d) := by
  have hg : g < L.threads := by
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    exact Frame.lt_of_get hX he
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, -, hPl⟩ := Lp.mma_anchor_full hpre hX hf hR hk hσ
  have hp0 : Mm.polled d0 = 0 := by simp [Mm.polled, hs0]
  exact Ring.mma_polls_exec hpre hw hg hX hk0 h0 hd hin hp0 hs (hPl _)

theorem lane_counts (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hlead : ElectLead L g (X.tr g))
    (hbc : Mma.BcastRun (X.tr g)) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {s : Nat} (hs : s < 3) :
    okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) = below s (Mm.polled d) ∧
      ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) =
        below s (Mm.done d) := by
  have hg : g < L.threads := by
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    exact Frame.lt_of_get hX he
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, hC, hPl⟩ := Lp.mma_anchor_full hpre hX hf hR hk hσ
  have hp0 : Mm.polled d0 = 0 := by simp [Mm.polled, hs0]
  have hdn0 : Mm.done d0 = 0 := by simp [Mm.done, hs0]
  exact Ring.mma_counts_exec hpre hw hg hX hk0 hk h0 hd hin hp0 hdn0 hs (hlead.take k)
    (hbc.take k) (hPl _) (hC _)

/-- A state reached backward at a rank below the state's is at an earlier event. -/
theorem lt_of_rank {k k' : Nat} {d d' : Mma.D} {P : Loader.Pro} (hk : k' ≤ k)
    (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hσ' : St Q L X g k' = some (some (.w (.mma d' P)))) (hr : rank d' < rank d) : k' < k := by
  rcases Nat.lt_or_eq_of_le hk with h | rfl
  · exact h
  · rw [hσ] at hσ'
    cases hσ'
    omega

/-! ### The cover -/

/-- **The MMAs of a released use cover its KV ring slot.** Before the MMA lane's commit to
`kv_empty s` of CTA `c`, every byte of slot `s` (K or V region) is the B operand byte of an
earlier MMA of the lane, with as many earlier commits to `kv_empty s` and more successful polls of
`kv_ready s`; a wait observing that MMA's completion finds the read performed. -/
theorem kv_cover (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hB : Mma.MmaBcast L X)
    {g jc pc : Nat} {sp : TcCommit.Spec} {c s : Nat} (hs : s < 3)
    (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = EvW.kvEmpty L c s)
    {l : Loc} (hl : l.space = .shared ∧ l.cta = c ∧
      ((L.sharedBase + 32768 * s ≤ l.addr ∧ l.addr < L.sharedBase + 32768 * s + 32768) ∨
       (L.sharedBase + 98304 + 32768 * s ≤ l.addr ∧
         l.addr < L.sharedBase + 98304 + 32768 * s + 32768))) :
    ∃ kR idx, kR < jc ∧ X.TcAsync (g, kR) ∧
      ((X.tr g).take kR).countP (commitsTo (EvW.kvEmpty L c s)) =
        ((X.tr g).take jc).countP (commitsTo (EvW.kvEmpty L c s)) ∧
      ((X.tr g).take jc).countP (commitsTo (EvW.kvEmpty L c s)) + 1 ≤
        okPolls (EvW.kvReady L c s) ((X.tr g).take kR) ∧
      AsyncCovers X (g, kR) (.mmaRead true idx) l ∧
      ∀ w ws, AsyncCopy.AsyncObserved X (g, kR) .mmaDone w true ws →
        X.AsyncPresent (g, kR) (.mmaRead true idx) := by
  have hal := (mmEnv_of_pre hpre).align
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hjc : jc < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, hsite, rfl, hds⟩ := commit_site hpre hX hf hs he hm
  obtain ⟨-, -, -, -, hlead⟩ := Lp.commit_lead hpre hX hf hs he hm
  have hbc := bcast_of_mma hf.roleWarp hB hg hjc.le hσ
  have hI := mma_inv_at hX hf hjc hσ
  obtain ⟨hi1, hin, -⟩ := hI.pv (by rw [hsite]; trivial)
  obtain ⟨hpc, hcc⟩ := lane_counts hpre hX hf hR hlead hbc hjc hσ hs
  have hdone : Mm.done d = d.i - 1 := by simp [Mm.done, hsite]
  rw [hdone] at hcc
  have hrk : rank d = 29 * d.i + 27 := by simp [rank, pos, hsite]
  obtain ⟨hsp, hcta, hreg⟩ := hl
  -- the commit and poll counts at an earlier state of the lane, from its `done` and `polled`
  have fin : ∀ kR d' (j : Fin 8), kR < jc → St Q L X g kR = some (some (.w (.mma d' P))) →
      below s (Mm.done d') = below s (d.i - 1) → d.i ≤ Mm.polled d' →
      ((X.tr g).take kR).countP (commitsTo (kvEmpty L (g / L.block) s)) =
        ((X.tr g).take jc).countP (commitsTo (kvEmpty L (g / L.block) s)) ∧
      ((X.tr g).take jc).countP (commitsTo (kvEmpty L (g / L.block) s)) + 1 ≤
        okPolls (kvReady L (g / L.block) s) ((X.tr g).take kR) := by
    intro kR d' _ hkR hσ' h1 h3
    obtain ⟨hp', hc'⟩ := lane_counts hpre hX hf hR hlead hbc (by omega) hσ' hs
    rw [hc', hcc, hp', h1]
    unfold below
    refine ⟨rfl, ?_⟩
    have : (d.i - 1 + 2 - s) / 3 + 1 ≤ (d.i + 2 - s) / 3 := by omega
    have := Nat.div_le_div_right (c := 3) (show d.i + 2 - s ≤ Mm.polled d' + 2 - s by omega)
    omega
  rcases hreg with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · -- a byte of the K region: QK step `j` of iteration `d.i - 1`
    have hB : (L.sharedBase + 32768 * s) % 128 = 0 := by omega
    obtain ⟨j, idx, hcov⟩ := k_cover (a := l.addr - (L.sharedBase + 32768 * s)) hB (by omega)
    obtain ⟨k', d', hk', hσ', hr'⟩ := reach_rank hX hf hlead hbc (R := 29 * (d.i - 1) + (5 + j))
      (N := d.n) (.inr ⟨by omega, by omega, by omega⟩) jc hjc hσ (by omega) rfl
    have hkj := lt_of_rank hk' hσ hσ' (by omega)
    have hpl := pos_le d'.site
    unfold rank at hr'
    have hi' : d'.i = d.i - 1 := by omega
    have hs' : d'.site = .qk j := site_qk (by omega)
    obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k']? = some e' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hsh := mma_shape_at hpre hX hf.sound hg he' (by omega) hσ'
    obtain ⟨pc', dst, spec, acc, mask, rfl, hD, hlow, hb⟩ := qk_spec hpre hs' hsh
    have hiss : X.MmaIssue (g, k') dst spec acc mask := ⟨pc', he'⟩
    rw [hi'] at hb
    have hbl := hcov spec hD (by rw [hb]; congr 1; omega)
    have hl' : l = ⟨.shared, spec.lowCta, L.sharedBase + 32768 * s +
        (l.addr - (L.sharedBase + 32768 * s))⟩ := by
      obtain ⟨sp', c', a'⟩ := l
      simp only at hsp hcta hlo hhi ⊢
      subst hsp hcta
      simp only [Loc.mk.injEq, true_and, hlow]
      omega
    rw [← hl'] at hbl
    have hbl' : spec.byteLoc (if true then .b else .a) idx = some l := by simpa using hbl
    obtain ⟨h1, h2⟩ := fin k' d' j hkj hσ' (by simp [Mm.done, hs', below]; omega)
      (by simp [Mm.polled, hs']; omega)
    exact ⟨k', idx, hkj, .inl ⟨_, _, _, _, hiss⟩, h1, h2, covers_of_byteLoc hiss hbl',
      fun w ws hobs => observed_mmaRead hX hiss hbl' hobs⟩
  · -- a byte of the V region: PV step `j` of iteration `d.i`
    have hB : (L.sharedBase + 98304 + 32768 * s) % 128 = 0 := by omega
    obtain ⟨j, idx, hcov⟩ :=
      v_cover (a := l.addr - (L.sharedBase + 98304 + 32768 * s)) hB (by omega)
    obtain ⟨k', d', hk', hσ', hr'⟩ := reach_rank hX hf hlead hbc (R := 29 * d.i + (19 + j))
      (N := d.n) (.inl ⟨by omega, by omega⟩) jc hjc hσ (by omega) rfl
    have hkj := lt_of_rank hk' hσ hσ' (by omega)
    have hpl := pos_le d'.site
    unfold rank at hr'
    have hi' : d'.i = d.i := by omega
    have hs' : d'.site = .pv j := site_pv (by omega)
    obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k']? = some e' :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hsh := mma_shape_at hpre hX hf.sound hg he' (by omega) hσ'
    obtain ⟨pc', dst, spec, acc, mask, rfl, hD, hlow, hb⟩ := pv_spec hpre hs' hsh
    have hiss : X.MmaIssue (g, k') dst spec acc mask := ⟨pc', he'⟩
    rw [hi', hds] at hb
    have hbl := hcov spec hD hb
    have hl' : l = ⟨.shared, spec.lowCta, L.sharedBase + 98304 + 32768 * s +
        (l.addr - (L.sharedBase + 98304 + 32768 * s))⟩ := by
      obtain ⟨sp', c', a'⟩ := l
      simp only at hsp hcta hlo hhi ⊢
      subst hsp hcta
      simp only [Loc.mk.injEq, true_and, hlow]
      omega
    rw [← hl'] at hbl
    have hbl' : spec.byteLoc (if true then .b else .a) idx = some l := by simpa using hbl
    have hI' := mma_inv_at hX hf (by omega) hσ'
    obtain ⟨-, hin', -⟩ := hI'.pv (by rw [hs']; trivial)
    obtain ⟨h1, h2⟩ := fin k' d' j hkj hσ' (by simp [Mm.done, hs', below]; omega)
      (by simp [Mm.polled, hs']; omega)
    exact ⟨k', idx, hkj, .inl ⟨_, _, _, _, hiss⟩, h1, h2, covers_of_byteLoc hiss hbl',
      fun w ws hobs => observed_mmaRead hX hiss hbl' hobs⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Ring.Cover
