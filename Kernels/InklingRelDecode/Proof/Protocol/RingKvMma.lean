-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingKvFoot

@[expose] public section

/-!
# The MMA lane's reads of the K and V tiles, on an execution

At an MMA of the elected lane of the MMA warp (a thread all of whose elections returned its lane,
`ElectLead`), in a run from the start of the loop (`Mm.polled d₀ = 0`, `Mm.done d₀ = 0`, no earlier
poll or commit on the slot):

* **QK MMA `j` of block `i`** (slot `s = i % 3`) reads B, the K tile, only from the half `j / 4` of
  the slot's K region `[sharedBase + 32768 s, + 32768)` (`Foot.qk_b_foot`) and A, the Q tile, only
  from the Q region `[sharedBase + 196608, + 16384)`; before it the lane has committed
  `i / 3` times to `kv_empty s` (its *use* of the slot) and polled `kv_ready s` successfully
  `i / 3 + 1` times.
* **PV MMA `j` of block `b = i - 1`** (slot `s = b % 3`) reads B, the V tile, only from the slot's
  V region `[sharedBase + 98304 + 32768 s, + 32768)` (`Foot.pv_b_foot`) and no byte of A (it is in
  Tensor Memory); before it the lane has committed `b / 3` times to `kv_empty s` and polled
  `kv_ready s` successfully at least `b / 3 + 1` times.

In both cases `readUse + 1 ≤ polls`, the gate of `Kv.copy_read_order`. The commit that completes
the reads of block `b` is the lane's `b / 3`-th commit to `kv_empty s` (`mma_commit_exec`): the
QK MMAs of block `b` precede it too (they are issued in iteration `b`, the commit in iteration
`b + 1`), the commit being a commit of all earlier MMAs of the thread.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty mma_shape MmShape QkIssue PvIssue
  mmQkALo mmQkBLo mmPvBLo mmEnv_of_pre MmEnv)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

theorem below_mono_of_succ {s a b : Nat} (hab : a ≤ b) : below s a ≤ below s b := by
  unfold below
  omega

variable (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k) {d0 d : Mma.D}
    {P : Loader.Pro} (h0 : wAt Q L X g k0 = some (some (.mma d0 P)))
    (hd : wAt Q L X g k = some (some (.mma d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc)
include hpre hw hg hX hk h0 hd hin

/-- **The window of an MMA run on an execution.** -/
theorem mma_window :
    (WComp.code L g Q).toMachine.Trace (some (.mma d0 P)) (((X.tr g).drop k0).take (k - k0)) ∧
      (WComp.code L g Q).toMachine.after (some (.mma d0 P))
        (((X.tr g).drop k0).take (k - k0)) = some (some (.mma d P)) ∧
      ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
        (WComp.code L g Q).toMachine.after (some (.mma d0 P))
          ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.mma d' P)) ∧
        Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
  have hrun := run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := run_states hk h0 hd
  refine ⟨hrun, hend, fun j hj => ?_⟩
  have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
  obtain ⟨d', h1, h2, h3⟩ := hin (k0 + j) (by omega) (by omega)
  exact ⟨d', (hmid j hj').trans h1, h2, h3⟩

/-- **The polls of the MMA lane on a slot, at an event**, for every lane and every broadcast
word. -/
theorem mma_polls_exec (hp0 : Mm.polled d0 = 0) {s : Nat} (hs : s < 3)
    (hfreshP : okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0) :
    okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) = below s (Mm.polled d) := by
  obtain ⟨hwin, hend, hwin'⟩ := mma_window hpre hw hg hX hk h0 hd hin
  have hP := mma_polls hpre hg hwin hwin' hend hs
  have hsplitP := countP_take_split (okPoll (kvReady L (g / L.block) s)) (X.tr g) hk
  have hb0 : below s 0 = 0 := by unfold below; omega
  unfold okPolls at hfreshP hP ⊢
  rw [hp0, hb0] at hP
  rw [hsplitP, hfreshP]
  omega

omit hpre hw hg hX hk h0 hd hin in
/-- **The polls and the commits of the MMA lane on a slot, at an event.** -/
theorem mma_counts_exec (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k)
    (hklt : k < (X.tr g).length) {d0 d : Mma.D} {P : Loader.Pro}
    (h0 : wAt Q L X g k0 = some (some (.mma d0 P)))
    (hd : wAt Q L X g k = some (some (.mma d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc)
    (hp0 : Mm.polled d0 = 0) (hdn0 : Mm.done d0 = 0) {s : Nat} (hs : s < 3)
    (hlead : ElectLead L g ((X.tr g).take k)) (hbc : Mma.BcastRun ((X.tr g).take k))
    (hfreshP : okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0)
    (hfreshC : ((X.tr g).take k0).countP (commitsTo (kvEmpty L (g / L.block) s)) = 0) :
    okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) = below s (Mm.polled d) ∧
      ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) = below s (Mm.done d) := by
  obtain ⟨hwin, hend, hwin'⟩ := mma_window hpre hw hg hX hk h0 hd hin
  have hsub : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), e ∈ (X.tr g).take k := by
    intro e he'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add]
    rw [Nat.add_sub_cancel_left] at he'
    exact List.mem_append_right _ he'
  have hE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), MmRun L g e :=
    fun e he' => ⟨⟨not_ends_take hg hX hklt e (hsub e he'), hlead e (hsub e he')⟩,
      hbc e (hsub e he')⟩
  have hP := mma_polls hpre hg hwin hwin' hend hs
  have hC := mma_commits hpre hg hwin hE hwin' hend hs
  have hsplitP := countP_take_split (okPoll (kvReady L (g / L.block) s)) (X.tr g) hk
  have hsplitC := countP_take_split (commitsTo (kvEmpty L (g / L.block) s)) (X.tr g) hk
  have hb0 : below s 0 = 0 := by unfold below; omega
  unfold okPolls at hfreshP hP ⊢
  rw [hp0, hb0] at hP
  rw [hdn0, hb0] at hC
  rw [hsplitP, hfreshP, hsplitC, hfreshC]
  omega

omit hpre hw hg hX hk h0 hd hin in
/-- A state at which an MMA event fires is a QK or a PV site. -/
theorem mma_site (d : Mma.D) {pc c : Nat} {spec : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hsh : MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩) :
    (∃ j, d.site = .qk j) ∨ (∃ j, d.site = .pv j) := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [MmShape] at hsh
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | exact .inr ⟨_, rfl⟩
    | (exfalso; simp at hsh)

/-- **A QK or PV MMA of the MMA lane.** -/
theorem mma_issue_exec (hp0 : Mm.polled d0 = 0) (hdn0 : Mm.done d0 = 0)
    (hlead : ElectLead L g ((X.tr g).take k)) (hbc : Mma.BcastRun ((X.tr g).take k))
    (hfreshP : ∀ s < 3, okPolls (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0)
    (hfreshC : ∀ s < 3, ((X.tr g).take k0).countP (commitsTo (kvEmpty L (g / L.block) s)) = 0)
    {pc c : Nat} {spec : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma c spec acc mask)⟩) :
    (∃ i s, s = i % 3 ∧
      ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) = i / 3 ∧
      okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) = i / 3 + 1 ∧
      (∀ idx l, spec.byteLoc .b idx = some l → l.space = .shared ∧ l.cta = g / L.block ∧
        L.sharedBase + 32768 * s ≤ l.addr ∧ l.addr < L.sharedBase + 32768 * s + 32768) ∧
      (∀ idx l, spec.byteLoc .a idx = some l → l.space = .shared ∧ l.cta = g / L.block ∧
        L.sharedBase + 196608 ≤ l.addr ∧ l.addr < L.sharedBase + 196608 + 16384)) ∨
    (∃ b s, s = b % 3 ∧
      ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) = b / 3 ∧
      b / 3 + 1 ≤ okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) ∧
      (∀ idx l, spec.byteLoc .b idx = some l → l.space = .shared ∧ l.cta = g / L.block ∧
        L.sharedBase + 98304 + 32768 * s ≤ l.addr ∧
        l.addr < L.sharedBase + 98304 + 32768 * s + 32768) ∧
      (∀ idx, spec.byteLoc .a idx = none)) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .tc (.mma c spec acc mask)⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hsh := mma_shape hpre hg hF
  have hI : Mma.Inv d := by
    obtain ⟨t, hgood, -⟩ := hF
    have hinv : (WComp.code L g Q).inv (.mma d P) := hgood.2
    exact hinv.1
  have hE := mmEnv_of_pre hpre
  have hal := hE.align
  have hsb := hE.sb
  have hcnt := fun s (hs : s < 3) =>
    mma_counts_exec hpre hw hg hX hk hklt h0 hd hin hp0 hdn0 hs hlead hbc (hfreshP s hs)
      (hfreshC s hs)
  rcases mma_site d hsh with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have hq := hI.qk (by simp [Mma.QkSite, hj])
    obtain ⟨site, i, n, tm, pro⟩ := d
    simp only at hj hq
    subst hj
    simp only [MmShape, QkIssue] at hsh
    obtain ⟨da, db, dsc, hdsc, hda, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    obtain ⟨hpoll, hcom⟩ := hcnt (i % 3) (Nat.mod_lt _ (by omega))
    have hdb' := Foot.decode_k (Ring.lo_lt_k hE (i % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hda' := Foot.decode_k (Ring.lo_lt_q hE j hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    have hdae := Option.some.inj (hda.symm.trans hda')
    subst hdbe hdae
    have hdsc' := Foot.qkDesc_eq hdsc
    subst hdsc'
    refine ⟨i, i % 3, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hcom]
      simp only [Mm.done]
      unfold below
      omega
    · rw [hpoll]
      simp only [Mm.polled]
      unfold below
      omega
    · intro idx l hl
      have hstart : (Mma.kLo L (i % 3) + 2 * (↑j % 4) + 1024 * (↑j / 4)) * 16 =
          L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4) + 32 * (↑j % 4) := by
        unfold Mma.kLo
        omega
      have hB : (L.sharedBase + 32768 * (i % 3) + 16384 * (↑j / 4)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Foot.qk_b_foot (B := L.sharedBase + 32768 * (i % 3) +
        16384 * (↑j / 4)) (c := 32 * (↑j % 4)) rfl hB (by omega) (by simp only [hstart]) hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
    · intro idx l hl
      have hstart : (Mma.qLo L + 2 * (↑j % 4) + 512 * (↑j / 4)) * 16 =
          L.sharedBase + 196608 + 8192 * (↑j / 4) + 32 * (↑j % 4) := by
        unfold Mma.qLo
        omega
      have hB : (L.sharedBase + 196608 + 8192 * (↑j / 4)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Foot.qk_a_foot (B := L.sharedBase + 196608 + 8192 * (↑j / 4))
        (c := 32 * (↑j % 4)) rfl hB (by omega) (by simp only [hstart]) rfl hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
  · right
    have hp := hI.pv (by simp [Mma.PvSite, hj])
    obtain ⟨site, i, n, tm, pro⟩ := d
    simp only at hj hp
    subst hj
    simp only [MmShape, PvIssue] at hsh
    obtain ⟨db, dsc, hdsc, hdb, hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
    obtain ⟨-, rfl, rfl, -⟩ := hev
    have hj8 : (j : Nat) < 8 := j.isLt
    obtain ⟨hpoll, hcom⟩ := hcnt ((i - 1) % 3) (Nat.mod_lt _ (by omega))
    have hdb' := Foot.decode_v (Ring.lo_lt_v hE ((i - 1) % 3) j (Nat.mod_lt _ (by omega)) hj8)
    have hdbe := Option.some.inj (hdb.symm.trans hdb')
    subst hdbe
    have hdsc' := Foot.pvDesc_eq hdsc
    subst hdsc'
    refine ⟨i - 1, (i - 1) % 3, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hcom]
      simp only [Mm.done]
      unfold below
      omega
    · rw [hpoll]
      simp only [Mm.polled]
      have h1 : below ((i - 1) % 3) (i - 1 + 1) ≤ below ((i - 1) % 3) (min (i + 1) n) :=
        below_mono_of_succ (by omega)
      have h2 : below ((i - 1) % 3) (i - 1 + 1) = (i - 1) / 3 + 1 := by
        unfold below
        omega
      omega
    · intro idx l hl
      have hstart : (Mma.vLo L ((i - 1) % 3) + 128 * ↑j) * 16 =
          L.sharedBase + 98304 + 32768 * ((i - 1) % 3) + 2048 * ↑j := by
        unfold Mma.vLo
        omega
      have hB : (L.sharedBase + 98304 + 32768 * ((i - 1) % 3)) % 128 = 0 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := Foot.pv_b_foot (B := L.sharedBase + 98304 + 32768 * ((i - 1) % 3))
        (j := ↑j) rfl hB hj8 (by simp only [hstart]) hl
      refine ⟨h1, by simpa using h2, by omega, by omega⟩
    · intro idx
      exact Foot.pv_a_none rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
