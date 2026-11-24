-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderCount

@[expose] public section

/-!
# The loader's arrivals and copies on an execution

`RingLoaderCount` counts the arrivals and copies along a run of the loader machine. Here they are
read on an execution `X`, at one event of a thread `g` (as `RingExec` does for the polls): the
loop runs from an anchor event `k₀` (the state `bar0`, after the loads of `(num_pre, num_iters)`,
`np = polled d₀`) to the event `k`, and nothing of the thread's earlier trace is an arrival or a
copy on the barrier (`hfresh…`).

* `loader_arrive_exec`: **the loader's arrival on `kv_ready s`** is the `arrive` site of an
  iteration of slot `s`, by the thread of lane 0, with `expect_tx 65536`, count 1, release, CTA
  scope; it is the thread's `n`-th arrival on the barrier with its block `loaderBlock np s n`,
  and the thread has polled `kv_empty s` successfully `n + 1` times before it:
  `arrivals + 1 = okPolls`.
* `loader_copy_exec`: **a loader copy on `kv_ready s`** (a thread all of whose elections returned
  its lane: `ElectLead`) is the copy `j = cpIn site` (`0 … 7`) of an iteration of slot `s`, of the
  `kv_rows` map at `Q.kvMap`, `ldCopy` of the state; it is the thread's `8 n + j`-th copy on the
  barrier, for the block `loaderBlock np s n`, and `copies / 8 + 1 = okPolls (kv_empty s)`.

Each iteration of slot `s` therefore adds one arrival and eight copies on `kv_ready s`, in the
unified schedule of `RingSched`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty MapReg LdShape loader_shape)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

/-- The events before `k` split at `k₀`: counts add. -/
theorem countP_take_split (p : Event → Bool) (l : List Event) {k0 k : Nat} (hk : k0 ≤ k) :
    (l.take k).countP p = (l.take k0).countP p + ((l.drop k0).take (k - k0)).countP p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.take_add, List.countP_append, Nat.add_sub_cancel_left]

/-- **A state of a loader that has an event has the loader's invariant.** -/
theorem loader_inv_at (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {j : Nat} (hj : j < (X.tr g).length)
    {d : Loader.D} {P : Loader.Pro} (hd : wAt Q L X g j = some (some (.loader d P))) :
    Loader.Inv L g d := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨o, t, hgood, -⟩ := (trace_of hpre hw hg hX).fired_at he hd
  have hinv : (WComp.code L g Q).inv (.loader d P) := hgood.2
  exact hinv.1

/-- **The window of a loader run on an execution.** The events of the thread from an anchor `k₀`
to `k`, with the abstract states before each of them in the loop, are a run of the loader machine
from the anchor state to the state at `k`; every state of the window has the loader's invariant. -/
theorem loader_window (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k)
    (hklt : k < (X.tr g).length) {d0 d : Loader.D} {P : Loader.Pro}
    (h0 : wAt Q L X g k0 = some (some (.loader d0 P)))
    (hd : wAt Q L X g k = some (some (.loader d P)))
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc) :
    (WComp.code L g Q).toMachine.Trace (some (.loader d0 P))
        (((X.tr g).drop k0).take (k - k0)) ∧
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        (((X.tr g).drop k0).take (k - k0)) = some (some (.loader d P)) ∧
      ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
        (WComp.code L g Q).toMachine.after (some (.loader d0 P))
          ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
        Ld.InLoop d' ∧ d'.site ≠ .setMaxInc ∧ Loader.Inv L g d' := by
  have hT := trace_of hpre hw hg hX
  have hrun := run_from hpre hw hg hX k h0
  obtain ⟨hend, hmid⟩ := run_states hk h0 hd
  refine ⟨hrun, hend, fun j hj => ?_⟩
  have hj' : j < k - k0 := lt_of_lt_of_le hj (List.length_take_le _ _)
  obtain ⟨d', h1, h2, h3⟩ := hin (k0 + j) (by omega) (by omega)
  refine ⟨d', (hmid j hj').trans h1, h2, h3, ?_⟩
  have hjl : k0 + j < (X.tr g).length := by omega
  exact loader_inv_at hpre hw hg hX hjl h1

variable (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
    (hX : Consistent L kernel WComp.asms mem0 X) {k0 k : Nat} (hk : k0 ≤ k) {d0 d : Loader.D}
    {P : Loader.Pro} (h0 : wAt Q L X g k0 = some (some (.loader d0 P)))
    (hd : wAt Q L X g k = some (some (.loader d P))) (hrg : Loader.Rng d)
    (hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc) (hbar : d0.site = .bar0) (hnp : d0.i ≤ 3)
include hpre hw hg hX hk h0 hd hrg hin hbar hnp

/-- **The loader's arrival on `kv_ready s`, on an execution.** -/
theorem loader_arrive_exec {s : Nat} (hs : s < 3)
    (hfreshA : arrivals (kvReady L (g / L.block) s) ((X.tr g).take k0) = 0)
    (hfreshP : okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k0) = 0) {pc tx cnt : Nat}
    {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive (kvReady L (g / L.block) s) tx cnt rel sc⟩) :
    d.site = .arrive ∧ d.i % 3 = s ∧ tx = 65536 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧
      laneOf L g = 0 ∧
      d.i = loaderBlock d0.i s (arrivals (kvReady L (g / L.block) s) ((X.tr g).take k)) ∧
      arrivals (kvReady L (g / L.block) s) ((X.tr g).take k) + 1 =
        okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .arrive (kvReady L (g / L.block) s) tx cnt rel sc⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hmap : MapReg P := EvW.after_mapReg hd
  have hok := ld_okArr hpre hmap hrg hF s
  rw [arrivesOn_arrive rfl] at hok
  simp only [decide_true] at hok
  obtain ⟨hsw, hs3⟩ : d.site = .arrive ∧ d.i % 3 = s := by
    have := hok.symm
    simpa using this
  have hsh := loader_shape hpre hmap hrg hF
  simp only [LdShape, hsw, Event.mk.injEq, Kind.arrive.injEq] at hsh
  obtain ⟨-, -, htx, hcnt, hrel, hsc⟩ := hsh
  obtain ⟨hwin, hend, hwin'⟩ := loader_window hpre hw hg hX hk hklt h0 hd hin
  have hin' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc ∧ (d'.site = .arrive → d'.ln = true) := by
    intro j hj
    obtain ⟨d', h1, h2, h3, h4⟩ := hwin' j hj
    exact ⟨d', h1, h2, h3, h4.lane⟩
  have hnE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), ¬ Ends e := by
    intro e he'
    refine not_ends_take hg hX hklt e ?_
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add]
    rw [Nat.add_sub_cancel_left] at he'
    exact List.mem_append_right _ he'
  have hA := loader_arrives hpre hmap hwin hnE hin' hend s hs
  have hin'' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj
    obtain ⟨d', h1, h2, h3, -⟩ := hwin' j hj
    exact ⟨d', h1, h2, h3⟩
  have hP := loader_polls hpre hmap hwin hin'' hend s hs
  have hsplitA := countP_take_split (arrivesOn (kvReady L (g / L.block) s)) (X.tr g) hk
  have hsplitP := countP_take_split (okPoll (kvEmpty L (g / L.block) s)) (X.tr g) hk
  unfold arrivals at hfreshA ⊢
  unfold okPolls at hfreshP hP ⊢
  rw [hsplitA, hfreshA]
  rw [hsplitP, hfreshP]
  have hlead : laneOf L g = 0 := by
    obtain ⟨t, hgood, -⟩ := hF
    have hinv : (WComp.code L g Q).inv (.loader d P) := hgood.2
    have hI : Loader.Inv L g d := hinv.1
    have h1 := hI.ln
    have h2 := hI.lane hsw
    rw [h2] at h1
    simpa using h1.symm
  have hI0 := loader_inv_at hpre hw hg hX (by omega : k0 < (X.tr g).length) h0
  have hId := loader_inv_at hpre hw hg hX hklt hd
  have hln0 : d0.ln = true := by rw [hI0.ln]; simp [hlead]
  have hln : d.ln = true := by rw [hId.ln]; simp [hlead]
  have hai0 : Ld.arrIters d0 = d0.i := by simp [Ld.arrIters, Ld.afterArrive, hbar]
  have hpo0 : Ld.polled d0 = d0.i := by simp [Ld.polled, Ld.afterWait, hbar]
  have hai : Ld.arrIters d = d.i := by simp [Ld.arrIters, Ld.afterArrive, hsw]
  have hpo : Ld.polled d = d.i + 1 := by simp [Ld.polled, Ld.afterWait, hsw]
  simp only [Ld.arrMu, hln0, hln, ite_true, hai0, hai] at hA
  rw [hpo0, hpo, below_succ hs] at hP
  simp only [hs3, ite_true] at hP
  rw [below_of_slot hs hs3] at hP
  rw [below_of_slot hs hs3, below_small hs hnp] at hA
  rw [below_small hs hnp] at hP
  refine ⟨hsw, hs3, htx, hcnt, hrel, hsc, hlead, ?_, ?_⟩
  · unfold loaderBlock loaderUse blockOf
    split at hA <;> split <;> omega
  · split at hA <;> split at hP <;> omega

omit hpre hw hg hX hk h0 hd hrg hin hbar hnp in
theorem Ld.afterWait_cp {site : Loader.Site} (h : Ld.isCp site = true) :
    Ld.afterWait site = true := by
  cases site <;> first | rfl | (exfalso; revert h; decide)

omit hpre hw hg hX hk h0 hd hrg hin hbar hnp in
theorem Ld.cpIn_lt {site : Loader.Site} (h : Ld.isCp site = true) : Ld.cpIn site < 8 := by
  cases site <;> simp_all [Ld.isCp, Ld.cpIn]

omit hpre hw hg hX hk h0 hd hrg hin hbar hnp in
/-- The event at a copy site is the site's tensor copy. -/
theorem ldShape_cp {d : Loader.D} {e : Event} (h : LdShape Q L g d e)
    (hc : Ld.isCp d.site = true) :
    ∃ b, EvW.ldBox d.site = some b ∧
      e = ⟨d.site.pc, .tensorIssue Q.kvMap (EvW.ldCopy Q L g d b)⟩ := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  cases site <;> simp only [Ld.isCp] at hc <;> first | exact absurd hc (by decide) | exact h

/-- **A loader copy on `kv_ready s`, on an execution.** -/
theorem loader_copy_exec {s : Nat} (hs : s < 3) (hlead : ElectLead L g ((X.tr g).take k))
    (hfreshC : ((X.tr g).take k0).countP (issuesTo (kvReady L (g / L.block) s)) = 0)
    (hfreshP : okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k0) = 0) {pc a : Nat}
    {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hsp : sp.mbar = kvReady L (g / L.block) s) :
    Ld.isCp d.site = true ∧ d.i % 3 = s ∧ a = Q.kvMap ∧
      (∃ b, EvW.ldBox d.site = some b ∧ sp = EvW.ldCopy Q L g d b) ∧
      ((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) s)) % 8 = Ld.cpIn d.site ∧
      d.i = loaderBlock d0.i s
        (((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) s)) / 8) ∧
      ((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) s)) / 8 + 1 =
        okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) := by
  have hT := trace_of hpre hw hg hX
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : ¬ Ends (⟨pc, .tensorIssue a sp⟩ : Event) := by
    rintro (⟨f, h⟩ | h) <;> simp only at h <;> cases h
  obtain ⟨u, hF⟩ := fired_some hT he hd hne
  have hmap : MapReg P := EvW.after_mapReg hd
  have hok := ld_okIssue hpre hmap hrg hF s
  rw [issuesTo_tensorIssue, hsp] at hok
  simp only [decide_true] at hok
  obtain ⟨hcp, hs3⟩ : Ld.isCp d.site = true ∧ d.i % 3 = s := by
    have := hok.symm
    simpa using this
  have hsh := loader_shape hpre hmap hrg hF
  obtain ⟨b, hb, hev⟩ := ldShape_cp hsh hcp
  simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
  obtain ⟨-, rfl, rfl⟩ := hev
  obtain ⟨hwin, hend, hwin'⟩ := loader_window hpre hw hg hX hk hklt h0 hd hin
  have hin'' : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d',
      (WComp.code L g Q).toMachine.after (some (.loader d0 P))
        ((((X.tr g).drop k0).take (k - k0)).take j) = some (some (.loader d' P)) ∧
      Ld.InLoop d' ∧ d'.site ≠ .setMaxInc := by
    intro j hj
    obtain ⟨d', h1, h2, h3, -⟩ := hwin' j hj
    exact ⟨d', h1, h2, h3⟩
  have hsub : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), e ∈ (X.tr g).take k := by
    intro e he'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [List.take_add]
    rw [Nat.add_sub_cancel_left] at he'
    exact List.mem_append_right _ he'
  have hE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), LeadRun L g e :=
    fun e he' => ⟨not_ends_take hg hX hklt e (hsub e he'), hlead e (hsub e he')⟩
  have hC := loader_copies hpre hmap hwin hE hin'' hend s hs
  have hP := loader_polls hpre hmap hwin hin'' hend s hs
  have hsplitC := countP_take_split (issuesTo (kvReady L (g / L.block) s)) (X.tr g) hk
  have hsplitP := countP_take_split (okPoll (kvEmpty L (g / L.block) s)) (X.tr g) hk
  unfold okPolls at hfreshP hP ⊢
  rw [hsplitC, hfreshC, hsplitP, hfreshP]
  have hpo0 : Ld.polled d0 = d0.i := by simp [Ld.polled, Ld.afterWait, hbar]
  have hpo : Ld.polled d = d.i + 1 := by simp [Ld.polled, Ld.afterWait_cp hcp]
  have hcp0 : Ld.cpMu s d0 = 8 * below s d0.i := by simp [Ld.cpMu, Ld.cpIn, hbar]
  have hcd : Ld.cpMu s d = 8 * (d.i / 3) + Ld.cpIn d.site := by
    simp only [Ld.cpMu, hs3, ite_true, below_of_slot hs hs3]
  have hlt := Ld.cpIn_lt hcp
  rw [hcp0, hcd] at hC
  rw [hpo0, hpo, below_succ hs] at hP
  simp only [hs3, ite_true] at hP
  rw [below_of_slot hs hs3] at hP
  rw [below_small hs hnp] at hC hP
  refine ⟨hcp, hs3, rfl, ⟨b, hb, rfl⟩, ?_, ?_, ?_⟩
  · split at hC <;> omega
  · unfold loaderBlock loaderUse blockOf
    split at hC <;> split <;> omega
  · split at hC <;> split at hP <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
