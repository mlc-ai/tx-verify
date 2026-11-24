-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingKvMma

@[expose] public section

/-!
# The MMA lane's commits to `kv_empty`, bounded without the broadcast word

`mma_commits` counts the PV commits to `kv_empty s` of a run whose elections return the thread's
lane and whose broadcasts receive 7 (`MmRun`): a lane that takes the branch after a broadcast that
skips a half (`Mma.Site.pvSkip`) commits less. The count is at most `below s (Mm.done d)` along
    every
run, with no premise on the elections or the broadcasts: every step raises `Mm.done` at least by the
commits it makes (`mm_next_done_le`). That bound is what the gate of `Kv.EmptySource.notify` needs
(`mma_commit_gate_le`): before the commit for block `b = i - 1` the lane has polled `kv_ready s`
more often than it has committed to `kv_empty s`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty mma_shape MmShape)

noncomputable section
set_option maxRecDepth 100000

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {M : Machine K A L g}

/-- **The count of a run is at most the change of the measure**, when every step raises the
measure at least by its count (`count_trace` with `≤`). -/
theorem count_trace_le (p : Event → Bool) (μ : M.St → Nat) (dom : M.St → Prop) (τ : M.St)
    (hstep : ∀ σ e σ', dom σ → ((∃ u, M.Fired σ e (some u)) ∨ Ends e) →
      M.next σ e = some σ' → (dom σ' ∨ σ' = τ) → μ σ + (if p e then 1 else 0) ≤ μ σ') :
    ∀ {σ : M.St} {es : List Event}, M.Trace σ es →
      (∀ j < es.length, ∃ τ, M.after σ (es.take j) = some τ ∧ dom τ) →
      M.after σ es = some τ → es.countP p + μ σ ≤ μ τ := by
  intro σ es h
  induction h with
  | nil σ =>
    intro _ ha
    simp only [Machine.after_nil, Option.some.injEq] at ha
    subst ha
    simp
  | @step σ σ1 e es u hf hn rest ih =>
    intro hall ha
    simp only [Machine.after_cons, hn, Option.bind_some] at ha
    obtain ⟨σ0, h0, hd0⟩ := hall 0 (by simp)
    simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at h0
    subst h0
    have hd1 : dom σ1 ∨ σ1 = τ := by
      cases es with
      | nil =>
        simp only [Machine.after_nil, Option.some.injEq] at ha
        exact .inr ha
      | cons e' es' =>
        obtain ⟨τ', h', hd'⟩ := hall 1 (by simp)
        simp only [List.take_succ_cons, List.take_zero, Machine.after_cons, hn, Option.bind_some,
          Machine.after_nil] at h'
        simp only [Option.some.injEq] at h'
        subst h'
        exact .inl hd'
    have hm1 := hstep σ e σ1 hd0 (.inl ⟨u, hf⟩) hn hd1
    have hall' : ∀ j < es.length, ∃ τ, M.after σ1 (es.take j) = some τ ∧ dom τ := by
      intro j hj
      obtain ⟨τ', h', hd'⟩ := hall (j + 1) (by simp; omega)
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at h'
      exact ⟨τ', h', hd'⟩
    have hmτ := ih hall' ha
    rw [List.countP_cons]
    omega
  | @last σ e hf =>
    intro hall ha
    simp only [Machine.after_cons, Machine.after_nil] at ha
    obtain ⟨σ0, h0, hd0⟩ := hall 0 (by simp)
    simp only [List.take_zero, Machine.after_nil, Option.some.injEq] at h0
    subst h0
    obtain ⟨u, hu⟩ : ∃ u, M.next σ e = some u := by
      cases hn : M.next σ e with
      | none => simp [hn] at ha
      | some u => exact ⟨u, rfl⟩
    obtain ⟨t, -, hfire⟩ := hf
    have hend := fires_none_ends hfire
    simp only [hu, Option.bind_some, Option.some.injEq] at ha
    have hm1 := hstep σ e _ hd0 (.inr hend) hu (.inr ha)
    subst ha
    simp only [List.countP_cons, List.countP_nil]
    omega
  | @dead σ e es u hf hn hlen hub =>
    intro _ ha
    simp only [Machine.after_cons, hn, Option.bind_none] at ha
    cases ha

end

/-- **A step of the MMA warp raises `Mm.done` at least by its PV commit**, for every lane and every
broadcast word. -/
theorem mm_next_done_le {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc) (h : Mma.next L g d e = some (some d')) :
    Mm.done d + (if d.site = .pvCommit1 then 1 else 0) ≤ Mm.done d' := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [Mm.done]

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

/-- **The PV commits along a run are at most the change of `below s (Mm.done d)`.** -/
theorem mma_commits_le (hpre : Pre Q L mem0) (hg : g < L.threads) {P : Loader.Pro} {d0 : Mma.D}
    {es : List Event} (hT : (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) es)
    (hin : ∀ j < es.length, ∃ d, (WComp.code L g Q).toMachine.after (some (.mma d0 P))
      (es.take j) = some (some (.mma d P)) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    {d : Mma.D}
    (hd : (WComp.code L g Q).toMachine.after (some (.mma d0 P)) es = some (some (.mma d P)))
    {s : Nat} (hs : s < 3) :
    es.countP (commitsTo (kvEmpty L (g / L.block) s)) + below s (Mm.done d0) ≤
      below s (Mm.done d) := by
  have h := count_trace_le (M := (WComp.code L g Q).toMachine)
    (commitsTo (kvEmpty L (g / L.block) s))
    (fun σ => match σ with | some (.mma d _) => below s (Mm.done d) | _ => 0)
    (fun σ => ∃ d, σ = some (.mma d P) ∧ Mma.Inv d ∧ d.site ≠ .setMaxRegInc)
    (some (.mma d P)) ?_ hT ?_ hd
  · exact h
  · rintro σ e σ' ⟨d1, rfl, hin1, hne⟩ hev hn hσ'
    have hn' : WComp.next L g (.mma d1 P) e = some σ' := hn
    rw [EvW.next_mma_map P hne] at hn'
    cases σ' with
    | none => rcases hσ' with ⟨_, h, _⟩ | h <;> cases h
    | some σ'' =>
      obtain ⟨a, ha, hfa⟩ := EvW.map_map_some hn'
      subst hfa
      have hdone := mm_next_done_le hin1 hne ha
      show below s (Mm.done d1) + (if commitsTo _ e = true then 1 else 0) ≤ below s (Mm.done a)
      rcases hev with ⟨u, hF⟩ | hend
      · have hcm := mm_commitsTo hpre hg hF hs
        rw [hcm]
        by_cases hw : d1.site = .pvCommit1
        · have hp : Mm.done d1 = d1.i - 1 := by simp [Mm.done, hw]
          rw [hw] at hdone
          simp only [ite_true] at hdone
          have hm := below_mono_of_succ (s := s) hdone
          rw [below_succ hs] at hm
          by_cases hm' : (d1.i - 1) % 3 = s
          · simp only [hw, hm', and_self, decide_true, ite_true]
            rw [hp] at hm
            simp only [hm', ite_true] at hm
            rw [hp]
            omega
          · simp only [hw, hm', and_false, decide_false, Bool.false_eq_true, ite_false,
              Nat.add_zero]
            omega
        · simp only [hw, false_and, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
          simp only [hw, ite_false, Nat.add_zero] at hdone
          exact below_mono_of_succ hdone
      · have hnc : commitsTo (kvEmpty L (g / L.block) s) e = false := by
          obtain ⟨pc, k⟩ := e
          rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;> rfl
        rw [hnc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        exact below_mono_of_succ (le_trans (Nat.le_add_right _ _) hdone)
  · intro j hj
    obtain ⟨d1, h1, h2, h3⟩ := hin j hj
    exact ⟨_, h1, d1, rfl, h2, h3⟩

/-- **The MMA lane's commit to `kv_empty s` follows more successful polls of `kv_ready s` than
its earlier commits to `kv_empty s`**, for every lane and every broadcast word: the gate of
`Kv.EmptySource.notify` (`mma_commit_gate_exec` without the premise on the elections and the
broadcasts). -/
theorem mma_commit_gate_le (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g)
    (hg : g < L.threads) (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k)
    {d0 d : Mma.D} {P : Loader.Pro}
    (h0 : wAt Q L X g k0 = some (some (.mma d0 P)))
    (hd : wAt Q L X g k = some (some (.mma d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc)
    (hp0 : Mm.polled d0 = 0) (hdn0 : Mm.done d0 = 0) {s : Nat} (hs : s < 3)
    (hfreshP : okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0)
    (hfreshC : ((X.tr g).take k0).countP (commitsTo (kvEmpty L (g / L.block) s)) = 0)
    {pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hsp : sp.mbar = kvEmpty L (g / L.block) s) :
    ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) + 1 ≤
      okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .tc (.commit sp)⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hcm := mm_commitsTo hpre hg hF hs
  rw [commitsTo_of_kind (sp := sp) rfl] at hcm
  simp only [hsp, decide_true] at hcm
  have hsite : d.site = .pvCommit1 ∧ (d.i - 1) % 3 = s := by
    have := hcm.symm
    simp only [decide_eq_true_eq] at this
    exact this
  obtain ⟨hsw, hs3⟩ := hsite
  obtain ⟨hwin, hend, hwin'⟩ := mma_window hpre hw hg hX hk h0 hd hin
  have hP := mma_polls hpre hg hwin hwin' hend hs
  have hC := mma_commits_le hpre hg hwin hwin' hend hs
  have hsplitP := countP_take_split (okPoll (kvReady L (g / L.block) s)) (X.tr g) hk
  have hsplitC := countP_take_split (commitsTo (kvEmpty L (g / L.block) s)) (X.tr g) hk
  have hb0 : below s 0 = 0 := by unfold below; omega
  have hI : Mma.Inv d := by
    obtain ⟨t, hgood, -⟩ := hF
    have hinv : (WComp.code L g Q).inv (.mma d P) := hgood.2
    exact hinv.1
  have hpv := hI.pv (by simp [Mma.PvSite, hsw])
  have hdone : Mm.done d = d.i - 1 := by simp [Mm.done, hsw]
  have hpol : Mm.polled d = min (d.i + 1) d.n := by simp [Mm.polled, hsw]
  unfold okPolls at hfreshP hP ⊢
  rw [hp0, hb0] at hP
  rw [hdn0, hb0] at hC
  rw [hsplitP, hfreshP, hsplitC, hfreshC]
  rw [hdone] at hC
  rw [hpol] at hP
  have hb1 := below_succ (i := d.i - 1) hs
  have hmono := below_mono_of_succ (s := s) (show d.i - 1 + 1 ≤ min (d.i + 1) d.n by omega)
  simp only [hs3, ite_true] at hb1
  simp only [below] at hb1 hmono hC hP ⊢
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
