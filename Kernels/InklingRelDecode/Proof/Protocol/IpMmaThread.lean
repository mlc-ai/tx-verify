-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.IpMmaTrace
public import Kernels.InklingRelDecode.Proof.Interface.LedgerFacts
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess

@[expose] public section

/-!
# The MMA thread of a CTA

The thread-layer conjuncts of `Tmem1.OFinalFacts L X c` (`TmemAccess.lean`), for every launched CTA:

* the MMAs of the CTA are one thread's: an MMA event is fired after the PV or QK election that
  returned the thread's own lane (`mma_lead`); two such threads of one CTA are in warp 7 and, by
  `ElectOk` (one leader for the warp and the mask, whatever the instance), have one lane;
* the thread's first commit to `o_final` has no earlier one: a commit to `o_final` is the role's
  `finCommit`, after which the role's `barrier.sync 1` follows, so two of them would be separated
  by a barrier-1 event, and the register ledger's phases (`phase_inv`) give every state of the
  role between `ldNum` and the return the same number of barrier-1 events;
* every MMA of the CTA precedes that commit, for the same reason.

The thread `cm` is the MMA thread if some MMA of the CTA exists, the first thread of the CTA
otherwise (then the conjunct on MMAs is empty). The role byte protocol `RoleReads` enters through
the phases only.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpMma
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An MMA event is at a QK or a PV site.** -/
theorem mma_site {g : Nat} {d : Mma.D} {pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hsh : EvW.MmShape L g d ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    isQk d.site = true ∨ isPv d.site = true := by
  unfold EvW.MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh <;>
    first
    | (simp at hsh)
    | simp [isQk, isPv]

/-- **A commit to `o_final` is at `finCommit`.** -/
theorem commit_finCommit {g : Nat} {d : Mma.D} {pc : Nat} {sp : TcCommit.Spec}
    (hsh : EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩) (h : sp.mbar = EvW.oFinal L (g / L.block)) :
    d.site = .finCommit := by
  unfold EvW.MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh <;>
    first
    | (simp at hsh; done)
    | (unfold EvW.QkIssue at hsh
       obtain ⟨_, _, _, _, _, _, hev⟩ := hsh
       simp at hev)
    | (unfold EvW.PvIssue at hsh
       obtain ⟨_, _, _, _, hev⟩ := hsh
       simp at hev)
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
       obtain ⟨-, rfl⟩ := hsh
       simp [EvW.commitSpec, EvW.oFinal, EvW.sReady, EvW.kvEmpty, EvW.oDone, EvW.barLoc,
         EvW.oFinalOff, EvW.sReadyOff, EvW.kvEmptyOff, EvW.oDoneOff] at h
       all_goals first | rfl | omega)

/-- **The number of barrier-1 events of a thread at a state of the MMA role** after `ldNum`: two. -/
theorem b1_mma (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k : Nat}
    {d : Mma.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (h1 : d.site ≠ .setMaxReg)
    (h2 : d.site ≠ .ldNum) (h3 : d.site ≠ .bar0) (h4 : d.site ≠ .setMaxRegInc) :
    b1N X g k = 2 := by
  obtain ⟨hto, t, e1, e2, e3, e4, e5, e6⟩ := phase_inv hpre hX hS hR k _ hk hσ
  have ht : t = 0 := e4 rfl
  subst ht
  rw [e2]
  simp only [tPh, wPh]

/-- **After `finCommit` comes `bar1`.** -/
theorem succ_fin {g j : Nat} {d : Mma.D} {P : Loader.Pro} {s1 : TSt}
    (hj : j < (X.tr g).length) (hs1 : St Q L X g (j + 1) = some (some s1))
    (hσ : St Q L X g j = some (some (.w (.mma d P)))) (hfc : d.site = .finCommit) :
    ∃ d', s1 = .w (.mma d' P) ∧ d'.site = .bar1 := by
  obtain ⟨s0, e, hσ0, he, hn⟩ := step_pred hj hs1
  rw [hσ] at hσ0
  cases hσ0
  obtain ⟨w', hw', hnx⟩ : ∃ w', s1 = .w w' ∧ WComp.next L g (.mma d P) e = some (some w') := by
    cases s1 with
    | d x =>
      obtain ⟨a, -, hh⟩ := Ledger.mapInv (show (WComp.next L g (.mma d P) e).map
        (Option.map TSt.w) = some (some (.d x)) from hn)
      cases hh
    | w w' =>
      obtain ⟨a, ha', hh⟩ := Ledger.mapInv (show (WComp.next L g (.mma d P) e).map
        (Option.map TSt.w) = some (some (.w w')) from hn)
      cases hh
      exact ⟨_, rfl, ha'⟩
  obtain ⟨d', rfl, hnd⟩ := IpMma.wnext_mma_fwd hnx (by rw [hfc]; simp)
  refine ⟨d', hw', ?_⟩
  simp [Mma.next, hfc] at hnd
  rw [← hnd]

/-- **Between the last commit and the end of the role there is a barrier-1 event**: if a thread's
state at `j` is the role's `finCommit` and it has a state at `i ≥ j + 2`, it made a barrier-1 event
between. -/
theorem b1_gap (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g j i : Nat} {d : Mma.D} {P : Loader.Pro}
    {s : TSt} (hi : i ≤ (X.tr g).length) (hσi : St Q L X g i = some (some s)) (hji : j + 2 ≤ i)
    (hσ : St Q L X g j = some (some (.w (.mma d P)))) (hfc : d.site = .finCommit) :
    b1N X g j + 1 ≤ b1N X g i := by
  obtain ⟨s1, hs1⟩ := St_def_le hi hσi (j + 1) (by omega)
  obtain ⟨d', hd', hsite⟩ := succ_fin (by omega) hs1 hσ hfc
  subst hd'
  obtain ⟨e1, he1⟩ : ∃ e1, (X.tr g)[j + 1]? = some e1 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hb := event_b1 hpre hX hS (show X.get (g, j + 1) = some e1 from he1) hs1
  have hbt : Execution.isBarId 1 e1 = true := by
    rw [hb]
    simp [tB1, wB1S, hsite, mmaB1]
  have hsucc := countP_take_succ (Execution.isBarId 1) he1
  have hmono1 : b1N X g j ≤ b1N X g (j + 1) :=
    (List.take_sublist_take_left (by omega : j ≤ j + 1)).countP_le
  have hmono2 : b1N X g (j + 2) ≤ b1N X g i :=
    (List.take_sublist_take_left (by omega : j + 2 ≤ i)).countP_le
  have : b1N X g (j + 2) = b1N X g (j + 1) + 1 := by
    unfold b1N
    rw [show j + 2 = j + 1 + 1 from rfl, hsucc, hbt]
    rfl
  omega

/-- A commit event to the barrier `m` is a commit to it. -/
theorem commitsTo_spec {m : Loc} {y : Event} (h : commitsTo m y = true) :
    ∃ pc sp, y = ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = m := by
  obtain ⟨pc, k⟩ := y
  cases k <;> simp [commitsTo] at h
  rename_i tk
  cases tk <;> simp at h
  exact ⟨pc, _, rfl, h⟩

/-- **What an MMA event says of its thread**: it is in the MMA role at a QK or PV site, in warp 7,
and led an election of the warp with the full mask. -/
theorem mma_event_data (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hW : RoleWarps Q L X)
    {g k pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    g < L.threads ∧ Worker.warpOf L g = 7 ∧
      ∃ m0 pc0 inst ld, X.get (g, m0) = some ⟨pc0, .elect 4294967295 inst ld⟩ ∧
        laneOf L g = ld := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hS ht hg he (.inl ⟨dst, sp, acc, mask, rfl⟩)
  have h7 : Worker.warpOf L g = 7 := by
    simpa [RoleWarp, Ledger.roleWarp, Worker.warpOf] using roleWarp_inv hW k _ hk.le hσ
  refine ⟨hg, h7, ?_⟩
  rcases mma_site hsh with hq | hp
  · obtain ⟨m0, -, r⟩ := mma_lead hpre hX hS hg (isX := isQk) (el := .qkElect) (Or.inl rfl) rfl
      (fun h hs => next_qk h hs) k d P hk hσ hq
    exact ⟨m0, r⟩
  · obtain ⟨m0, -, r⟩ := mma_lead hpre hX hS hg (isX := isPv) (el := .pvElect) (Or.inr rfl) rfl
      (fun h hs => next_pv h hs) k d P hk hσ hp
    exact ⟨m0, r⟩

/-- **A commit to `o_final` is the only one of its thread**: two would be separated by the role's
`barrier.sync 1`, and the states of the role have one barrier-1 count. -/
theorem final_first (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {g i pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = EvW.oFinal L (g / L.block)) :
    ((X.tr g).take i).countP (commitsTo (EvW.oFinal L (g / L.block))) = 0 := by
  have hS := hf.sound
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  by_contra hne
  have hlt : 0 < ((X.tr g).take i).countP (commitsTo (EvW.oFinal L (g / L.block))) :=
    Nat.pos_of_ne_zero hne
  obtain ⟨j, y, hj, hy, -⟩ := CtaBarrier.countP_index
    (xs := (X.tr g).take i) (p := commitsTo (EvW.oFinal L (g / L.block))) hlt
  have hji : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hji] at hj
  obtain ⟨pcy, spy, rfl, hmy⟩ := commitsTo_spec hy
  have hjget : X.get (g, j) = some ⟨pcy, .tc (.commit spy)⟩ := hj
  obtain ⟨dj, Pj, hσj, hshj⟩ := mma_event_state hpre hX hS hf.tracked hg hjget (.inr ⟨spy, rfl⟩)
  obtain ⟨di, Pi, hσi, hshi⟩ := mma_event_state hpre hX hS hf.tracked hg he (.inr ⟨sp, rfl⟩)
  have hfj := commit_finCommit hshj hmy
  have hfi := commit_finCommit hshi hm
  by_cases h1 : i = j + 1
  · subst h1
    obtain ⟨d', hd', hs'⟩ := succ_fin (by omega) hσi hσj hfj
    cases hd'
    rw [hfi] at hs'
    cases hs'
  · have hgap := b1_gap hpre hX hS hi.le hσi (by omega) hσj hfj
    have e1 := b1_mma hpre hX hS hR (by omega) hσj (by rw [hfj]; simp) (by rw [hfj]; simp)
      (by rw [hfj]; simp) (by rw [hfj]; simp)
    have e2 := b1_mma hpre hX hS hR hi.le hσi (by rw [hfi]; simp) (by rw [hfi]; simp)
      (by rw [hfi]; simp) (by rw [hfi]; simp)
    omega

/-- **An MMA is before the thread's commit to `o_final`.** -/
theorem mma_before_final (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {g kx i pc dst : Nat}
    {sp : TcCommit.Spec} {ms : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, kx) = some ⟨pc, .tc (.mma dst ms acc mask)⟩)
    {pc' : Nat} (he : X.get (g, i) = some ⟨pc', .tc (.commit sp)⟩)
    (hm : sp.mbar = EvW.oFinal L (g / L.block)) : kx < i := by
  have hS := hf.sound
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hkx : kx < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨dx, Px, hσx, hshx⟩ := mma_event_state hpre hX hS hf.tracked hg hx
    (.inl ⟨dst, ms, acc, mask, rfl⟩)
  obtain ⟨di, Pi, hσi, hshi⟩ := mma_event_state hpre hX hS hf.tracked hg he (.inr ⟨sp, rfl⟩)
  have hfi := commit_finCommit hshi hm
  have hsite := mma_site hshx
  by_contra hle
  rcases Nat.lt_or_ge i kx with h1 | h1
  · by_cases h2 : kx = i + 1
    · subst h2
      obtain ⟨d', hd', hs'⟩ := succ_fin (by omega) hσx hσi hfi
      cases hd'
      rcases hsite with h | h <;> simp [hs', isQk, isPv] at h
    · have hgap := b1_gap hpre hX hS hkx.le hσx (by omega) hσi hfi
      have hn : ∀ s : Mma.Site, (isQk s = true ∨ isPv s = true) → s ≠ .setMaxReg ∧ s ≠ .ldNum ∧
          s ≠ .bar0 ∧ s ≠ .setMaxRegInc := by
        intro s hs
        cases s <;> simp_all [isQk, isPv]
      obtain ⟨n1, n2, n3, n4⟩ := hn _ hsite
      have e1 := b1_mma hpre hX hS hR hkx.le hσx n1 n2 n3 n4
      have e2 := b1_mma hpre hX hS hR hi.le hσi (by rw [hfi]; simp) (by rw [hfi]; simp)
        (by rw [hfi]; simp) (by rw [hfi]; simp)
      omega
  · have : kx = i := by omega
    subst this
    rw [hσx] at hσi
    cases hσi
    rw [hfi] at hsite
    simp [isQk, isPv] at hsite

end
end PTX.Kernels.InklingRelDecode.Proof.IpMma
