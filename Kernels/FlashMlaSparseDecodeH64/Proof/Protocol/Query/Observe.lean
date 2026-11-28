-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticClc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.TmaObj
public import Lemmas.Protocol.PairTmaRing.Order
public import Lemmas.Protocol.UnitNotify

@[expose] public section

/-! # What the query waits observe

Trace-level, from the rows and the two objects (`qTma_obj`, `qUtccp_obj`):

* `qTma` is used for one phase: the MMA lane's one arrival expecting 65536 bytes and its eight
  tensor loads of 8192 bytes. Its only successful poll is the MMA lane's first, at pc 1931, and it
  observes the arrival and each of the eight loads (`qTma_observes`): the phase it observes holds
  nine counted items (`TmaUnits.Obj.card_phase`), and with at most one arrival and eight loads
  there are no others.
* `qUtccp` is notified by the MMA lane's commit at pc 1982. A successful poll is a first poll with
  parity 0 of one of the three waiter kinds (1983, 2205, 2644) and observes that commit's
  notification (`qUtccp_observes`, `Notify.Obj.observes` with `Reach` vacuous: the lane commits
  to `qUtccp` once).

**Inputs owed by lane B** (counts of the MMA lane's trace; its machine runs each site once):
`(X.tr y).countP (issuesTo qTma) ≤ 8`, `arrivals qTma (X.tr y) ≤ 1` and
`(X.tr y).countP (commitsTo qUtccp) ≤ 1` for `y = mmaLane L X c`; and the inputs of `initFirst`
(`InitRows`, lane A; `Bar0Rows`, all roles). -/

/-! # The query copy's notify object `qUtccp`

From `mbar_use` and the rows only. The events that name `qUtccp` of CTA `c` are the startup's
initialization, the MMA lane's `tcgen05.commit` (pc 1982), and the first polls, with parity 0, of
its three waiter kinds: the MMA lane (1983), the TMA lane (2205) and warpgroup 2 (2644)
(`qUtccp_use`). So the object is a `Notify.Obj` of the CTA's MMA lane with offset 0
(`qUtccp_obj`): one commit notifies it, and every successful poll is a lane's first.

Input of `qUtccp_obj` beyond the rows: `MmaOne L X` (`Iface/Elect/Mma.lean`, producer B) and
the inputs of `initFirst` as for `qTma` (`Query/Obj.lean`). No cancellation request completes on it
(`no_clcGet`, the static scan of `Lib/StaticCode.lean`). -/

/-! # The query's TMA barrier `qTma` as a `TmaUnits` object

From `mbar_use` and the rows only. The events that name `qTma` of CTA `c` are the startup's
initialization and the MMA lane's eight tensor loads of 8192 bytes (pcs `qLoadPcs`), its arrival
expecting 65536 bytes (pc 1929) and its first poll with parity 0 (pc 1931) (`qTma_use`). With one
MMA lane per CTA (`MmaOne`, `Iface/Elect/Mma.lean`), all updates are the lane `mmaLane L X c`'s,
so the object is a `MbarRing.TmaUnits.Obj` with eight loads of 8192 bytes (`qTma_obj`).

The object's first record is its one initialization (`initFirst`, `Protocol/Mbar/InitFirst.lean`),
whose inputs `InitRows` and `Bar0Rows` the objects take. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The MMA pcs that name `qTma` are after the election. -/
private theorem mmaOn_of {g pc : Nat} (hw : MbarRow.MmaAt L g pc)
    (hpc : pc ∈ MbarRow.qLoadPcs ∨ pc = 1929 ∨ pc = 1931 ∨ pc = 1982 ∨ pc = 1983) :
    MmaOn L g pc := by
  refine ⟨hw, ?_⟩
  simp only [MbarRow.qLoadPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  omega

/-- **The uses of `qTma` of CTA `c`**: the startup's initialization, or the MMA lane of the CTA
loading 8192 bytes, arriving with 65536 expected bytes (pc 1929), or polling first with parity 0
(pc 1931). -/
theorem qTma_use (hR : MbarRows P L X) {c g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hm : Frame.MbarOf e (mbarLoc L c .qTma)) :
    (∃ n, e.kind = .mbInit (mbarLoc L c .qTma) n) ∨
      MmaOn L g e.pc ∧ g / L.block = c ∧
        ((e.pc ∈ MbarRow.qLoadPcs ∧ MbarRow.Issue e (mbarLoc L c .qTma) 8192) ∨
          (e.pc = 1929 ∧ MbarRow.Arrive e (mbarLoc L c .qTma) 65536) ∨
            (e.pc = 1931 ∧ MbarRow.Wait e (mbarLoc L c .qTma) 0 ∧
              okPolls (mbarLoc L c .qTma) ((X.tr g).take k) = 0)) := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _
    | svDone _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qLoad hpc hl hk =>
      exact .inr ⟨mmaOn_of hw (.inl hpc), (fam_eq hl).1.symm, .inl ⟨hpc, hk⟩⟩
    | qArrive hpc hl hk =>
      exact .inr ⟨mmaOn_of hw (.inr (.inl hpc)), (fam_eq hl).1.symm, .inr (.inl ⟨hpc, hk⟩)⟩
    | qWait hpc hl hk h0 =>
      exact .inr ⟨mmaOn_of hw (.inr (.inr (.inl hpc))), (fam_eq hl).1.symm,
        .inr (.inr ⟨hpc, hk, h0⟩)⟩
    | qCommit _ hl _ | qCopyWait _ hl _ _ | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _
    | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | rawLoad _ hl _
    | rawArrive _ hl _ | coordFree _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2

/-- **`qTma` of CTA `c` is a `TmaUnits` object of the CTA's MMA lane**: one arrival expecting
65536 bytes per use and eight tensor loads of 8192 bytes. -/
theorem qTma_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) {c : Nat} :
    TmaUnits.Obj X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192 :=
  tmaUnits_of_uses hX hR (initFirst hp hX hFw hR hI hB c .qTma) fun he hm => by
    rcases qTma_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨hat, hc, ⟨-, hk⟩ | ⟨-, hk⟩ |
      ⟨-, hk, -⟩⟩
    · exact .inl hk
    · have hy := laneOn_eq hO he (notUb_of_kind (mbar_kind hX hR he hm)) hat
      rw [hc] at hy
      exact .inr (.inr ⟨hy, .inl hk⟩)
    · have hy := laneOn_eq hO he (notUb_of_kind (mbar_kind hX hR he hm)) hat
      rw [hc] at hy
      exact .inr (.inr ⟨hy, .inr hk⟩)
    · exact .inr (.inl ⟨_, hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The waiter kinds of `qUtccp`: the lane's pc range and site. -/
def QWaiter (L : Launch) (g pc : Nat) : Prop :=
  (MbarRow.MmaAt L g pc ∧ pc = 1983) ∨ (MbarRow.TmaAt L g pc ∧ pc = 2205) ∨
    (MbarRow.DequantAt L g pc ∧ pc = 2644)

/-- **The uses of `qUtccp` of CTA `c`**: the startup's initialization, the MMA lane's commit, or
a first poll with parity 0 of one of the three waiter kinds; the lane is of the CTA. -/
theorem qUtccp_use (hR : MbarRows P L X) {c g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hm : Frame.MbarOf e (mbarLoc L c .qUtccp)) :
    (∃ n, e.kind = .mbInit (mbarLoc L c .qUtccp) n) ∨ g / L.block = c ∧
      ((MmaOn L g e.pc ∧ e.pc = 1982 ∧ MbarRow.Commit e (mbarLoc L c .qUtccp)) ∨
        (QWaiter L g e.pc ∧ MbarRow.Wait e (mbarLoc L c .qUtccp) 0 ∧
          okPolls (mbarLoc L c .qUtccp) ((X.tr g).take k) = 0)) := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨hw, h⟩ | ⟨hw, h⟩ | ⟨-, h⟩ |
    ⟨hw, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | coordReady _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _
    | svDone _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qCommit hpc hl hk =>
      exact .inr ⟨(fam_eq hl).1.symm, .inl ⟨⟨hw, by omega⟩, hpc, hk⟩⟩
    | qCopyWait hpc hl hk h0 =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr ⟨.inl ⟨hw, hpc⟩, hk, h0⟩⟩
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | kvWait _ hl _ | qkCommit _ hl _
    | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait hpc hl hk h0 =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr ⟨.inr (.inl ⟨hw, hpc⟩), hk, h0⟩⟩
    | lastWait _ hl _ _ | coordWait _ hl _ | freeWait _ hl _ | rawLoad _ hl _
    | rawArrive _ hl _ | coordFree _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | freeWait _ hl _ | readyArrive _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait hpc hl hk h0 =>
      exact .inr ⟨(fam_eq hl).1.symm, .inr ⟨.inr (.inr ⟨hw, hpc⟩), hk, h0⟩⟩
    | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2

/-- **`qUtccp` of CTA `c` is a notify object of the CTA's MMA lane**, with offset 0: its records
are its initialization, polls and the notifications of that lane's commits addressing it. -/
theorem qUtccp_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) {c : Nat} :
    Notify.Obj X (mbarLoc L c .qUtccp) (mmaLane L X c) (mbarLoc L c .qUtccp) 0 := by
  refine Notify.Obj.of_commits hX (initFirst hp hX hFw hR hI hB c .qUtccp) ?_ ?_ ?_ ?_
    (no_clcGet hX) ?_ ?_ ?_ (Nat.zero_le _)
  · intro h i pc tx cnt rel sc he
    rcases qUtccp_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
      ⟨-, ⟨-, -, s, hk, -⟩ | ⟨-, ⟨ok, hk⟩, -⟩⟩ <;> cases hk
  · intro i pc a sp he hm
    obtain ⟨h, j⟩ := i
    rcases qUtccp_use hR (Frame.lt_of_get hX he) he hm with ⟨n, hk⟩ |
      ⟨-, ⟨-, -, s, hk, -⟩ | ⟨-, ⟨ok, hk⟩, -⟩⟩ <;> cases hk
  · intro i pc s he hc
    exact no_copy hX hR he hc
  · intro i pc m' noinc he _
    exact no_asyncArrive hX hR he
  · intro i pc m' he
    exact no_inval hX hR i m' ⟨pc, he⟩
  · intro i pc sp r he ht
    obtain ⟨h, j⟩ := i
    rcases qUtccp_use hR (Frame.lt_of_get hX he) he ⟨r, ht⟩ with ⟨n, hk⟩ |
      ⟨hc, ⟨hat, -, s, hk, hs, -⟩ | ⟨-, ⟨ok, hk⟩, -⟩⟩
    · cases hk
    · simp only [Kind.tc.injEq, TcKind.commit.injEq] at hk
      subst hk
      have hy := laneOn_eq hO he (fun _ h => by cases h) hat
      rw [hc] at hy
      exact ⟨hy, hs⟩
    · cases hk
  · intro h k pc p acq sc he
    rcases qUtccp_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
      ⟨-, ⟨-, -, s, hk, -⟩ | ⟨-, ⟨ok, hk⟩, h0⟩⟩
    · cases hk
    · cases hk
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      rw [h0]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem countP_lt_of_get {p : Event → Bool} {i : EvId} {e : Event}
    (he : X.get i = some e) (hp : p e = true) :
    ((X.tr i.1).take i.2).countP p < (X.tr i.1).countP p := by
  obtain ⟨g, j⟩ := i
  show ((X.tr g).take j).countP p < (X.tr g).countP p
  have h1 := countP_take_succ he hp
  have h2 : ((X.tr g).take (j + 1)).countP p ≤ (X.tr g).countP p :=
    (List.take_sublist _ _).countP_le
  omega

/-- **The counted items of `qTma` are of use 0**, when the MMA lane arrives at most once and loads
at most eight times. -/
theorem qTma_items {c : Nat}
    (o : TmaUnits.Obj X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192)
    (hN : (X.tr (mmaLane L X c)).countP (issuesTo (mbarLoc L c .qTma)) ≤ 8)
    (hA : arrivals (mbarLoc L c .qTma) (X.tr (mmaLane L X c)) ≤ 1) {x : Fin 9 × Nat}
    (hx : x ∈ TmaUnits.S X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192) : x.2 = 0 := by
  obtain ⟨-, h0', h1'⟩ := o.source hx
  have e1 : (TmaUnits.op X (mbarLoc L c .qTma) (mmaLane L X c) 8 x.1 x.2).1 = mmaLane L X c :=
    rfl
  by_cases hz : x.1.val = 0
  · obtain ⟨⟨pc', rel, sc', hget⟩, hcnt⟩ := h0' hz
    have hlt' := countP_lt_of_get (p := arrivesOn (mbarLoc L c .qTma)) hget
      (by simp [arrivesOn, sourceArrive])
    rw [e1] at hlt'
    simp only [arrivals] at hcnt hA
    omega
  · obtain ⟨⟨pc', al, sp, hget, hm⟩, hcnt⟩ := h1' hz
    have hlt' := countP_lt_of_get (p := issuesTo (mbarLoc L c .qTma)) hget
      (by simp [issuesTo, hm])
    rw [e1] at hlt'
    omega

/-- Every successful poll of `qTma` has parity 0 and no earlier successful poll. -/
private theorem qTma_poll (hR : MbarRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {c h k pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait (mbarLoc L c .qTma) p true acq sc⟩) :
    MmaOn L h pc ∧ h / L.block = c ∧ pc = 1931 ∧ p = 0 ∧
      okPolls (mbarLoc L c .qTma) ((X.tr h).take k) = 0 := by
  rcases qTma_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
    ⟨hat, hc, ⟨-, a, s, hk, -⟩ | ⟨-, hk⟩ | ⟨hpc, ⟨ok, hk⟩, h0⟩⟩
  · cases hk
  · cases hk
  · cases hk
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨-, rfl, -⟩ := hk
    exact ⟨hat, hc, hpc, rfl, h0⟩

/-- **The query wait observes the query tile.** A successful poll of `qTma` of CTA `c` is the
MMA lane's at pc 1931, and it observes the lane's arrival and each of its eight tensor loads
(the load with `a` earlier loads to `qTma`). -/
theorem qTma_observes (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) {c : Nat}
    (hN : (X.tr (mmaLane L X c)).countP (issuesTo (mbarLoc L c .qTma)) ≤ 8)
    (hA : arrivals (mbarLoc L c .qTma) (X.tr (mmaLane L X c)) ≤ 1)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c .qTma) p true acq sc⟩) :
    h = mmaLane L X c ∧ pc = 1931 ∧
      (∃ i pc' rel sc', X.get (mmaLane L X c, i) =
          some ⟨pc', .arrive (mbarLoc L c .qTma) 65536 1 rel sc'⟩ ∧
        WaitObserves X (.thread (mmaLane L X c, i)) (h, j) (mbarLoc L c .qTma) acq sc) ∧
      ∀ a : Fin 8, ∃ i pc' al sp, X.get (mmaLane L X c, i) = some ⟨pc', .tensorIssue al sp⟩ ∧
        sp.mbar = mbarLoc L c .qTma ∧
        ((X.tr (mmaLane L X c)).take i).countP (issuesTo (mbarLoc L c .qTma)) = a.val ∧
        WaitObserves X (.async (mmaLane L X c, i) (.notify .load)) (h, j) (mbarLoc L c .qTma)
          acq sc := by
  classical
  have o := qTma_obj hp hX hFw hR hI hB hO (c := c)
  obtain ⟨hat, hc, hpc, -, h0⟩ := qTma_poll hR hX he
  have hhy : h = mmaLane L X c := by
    have := laneOn_eq hO he (fun _ h => by cases h) hat
    rw [hc] at this
    exact this
  have hAlt := MbarRing.Poll.alternates hX (o.counted.pclean hX) (δ := 0) (g := h)
    fun _ _ _ _ _ he' => by
      obtain ⟨-, -, -, rfl, h0'⟩ := qTma_poll hR hX he'
      rw [h0']
  have hlt : 0 < okPolls (mbarLoc L c .qTma) (X.tr h) := by
    rw [← h0]; exact PairTmaRing.okPolls_lt_of_get he
  have hcard :=
    o.card_phase hX (by decide) (by decide) (δ := 0) (j := 0) (by decide) hAlt le_rfl hlt
  -- the counted items are those of use 0
  let T : Finset (Fin 9 × Nat) := Finset.univ.image fun k => (k, 0)
  have hST : TmaUnits.S X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192 ⊆ T := fun x hx =>
    Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, Prod.ext rfl (qTma_items o hN hA hx).symm⟩
  let F := (TmaUnits.S X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192).filter fun x =>
    Counted.ph X (mbarLoc L c .qTma) (TmaUnits.it X (mbarLoc L c .qTma) (mmaLane L X c) 8) x =
      Unit.obsOf X (mbarLoc L c .qTma) h 0
  have hFT : F = T := by
    refine Finset.eq_of_subset_of_card_le ((Finset.filter_subset _ _).trans hST) ?_
    calc T.card ≤ (Finset.univ : Finset (Fin 9)).card := Finset.card_image_le
      _ = 9 := by simp
      _ ≤ F.card := hcard
  have hin : ∀ k : Fin 9, (k, 0) ∈ TmaUnits.S X (mbarLoc L c .qTma) (mmaLane L X c) 8 8192 ∧
      MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c .qTma))
        (TmaUnits.it X (mbarLoc L c .qTma) (mmaLane L X c) 8 k 0) (.thread (h, j)) := by
    intro k
    have hk : (k, 0) ∈ F := hFT ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    obtain ⟨hS, hph⟩ := Finset.mem_filter.mp hk
    have hub := o.counted.ubw hX (δ := 0) (n := 0) (by decide) hAlt le_rfl hlt hS hph
    rw [show Poll.nth X (mbarLoc L c .qTma) h 0 = j by rw [← h0]; exact Poll.nth_eq he] at hub
    exact ⟨hS, hub⟩
  refine ⟨hhy, hpc, ?_, fun a => ?_⟩
  · obtain ⟨hS, hub⟩ := hin 0
    obtain ⟨-, h0', -⟩ := o.source hS
    obtain ⟨⟨pc', rel, sc', hget⟩, -⟩ := h0' rfl
    refine ⟨_, pc', rel, sc', hget, ⟨⟨pc, p, he⟩, ?_⟩⟩
    simp only [TmaUnits.it, Fin.val_zero, ↓reduceIte] at hub
    exact hub
  · obtain ⟨hS, hub⟩ := hin a.succ
    obtain ⟨-, -, h1'⟩ := o.source hS
    obtain ⟨⟨pc', al, sp, hget, hm⟩, hcnt⟩ := h1' (by simp)
    refine ⟨(TmaUnits.op X (mbarLoc L c .qTma) (mmaLane L X c) 8 a.succ 0).2, pc', al, sp, hget,
      hm, hcnt.trans (by simp), ⟨⟨pc, p, he⟩, ?_⟩⟩
    simp only [TmaUnits.it, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte] at hub
    exact hub

/-- **The reuse paths of `qUtccp` are vacuous** when its lane commits at most once: a counted
unit's commit has no earlier one. -/
theorem qUtccp_reach {c : Nat} {y : Nat}
    (N : Notify.Obj X (mbarLoc L c .qUtccp) y (mbarLoc L c .qUtccp) 0)
    (hC1 : (X.tr y).countP (commitsTo (mbarLoc L c .qUtccp)) ≤ 1) (h : Nat) :
    Notify.Reach L kernel Assumptions.all X (mbarLoc L c .qUtccp) y (mbarLoc L c .qUtccp) 0 h := by
  intro x hx jj hjj
  obtain ⟨-, pc', sp, hget, hb, -, hcnt⟩ := N.S_rec hx
  have hlt := countP_lt_of_get (p := commitsTo (mbarLoc L c .qUtccp)) hget
    (by simp [commitsTo, hb])
  dsimp only at hlt
  omega

/-- **The query copy's waits observe its commit.** A successful poll of `qUtccp` of CTA `c` is a
first poll of one of its three waiter kinds (pcs 1983, 2205, 2644) of the CTA, and it observes the
notification of the MMA lane's commit at pc 1982. -/
theorem qUtccp_observes (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : MmaOne L X) {c : Nat}
    (hC1 : (X.tr (mmaLane L X c)).countP (commitsTo (mbarLoc L c .qUtccp)) ≤ 1)
    {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c .qUtccp) p true acq sc⟩) :
    QWaiter L h pc ∧ h / L.block = c ∧
      ∃ i sp rank, X.get (mmaLane L X c, i) = some ⟨1982, .tc (.commit sp)⟩ ∧
        sp.mbar = mbarLoc L c .qUtccp ∧ TcCommit.target sp rank = some (mbarLoc L c .qUtccp) ∧
        rank ∈ X.tcNotified (mmaLane L X c, i) ∧
        WaitObserves X (.async (mmaLane L X c, i) (.tcNotify rank)) (h, j)
          (mbarLoc L c .qUtccp) acq sc := by
  have N := qUtccp_obj hp hX hFw hR hI hB hO (c := c)
  rcases qUtccp_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
    ⟨hc, ⟨-, -, s, hk, -⟩ | ⟨hw, -, h0⟩⟩
  · cases hk
  · cases hk
  obtain ⟨i, pc', sp, rank, hget, hm, ht, -, hrank, hwo⟩ :=
    N.observes hX (qUtccp_reach N hC1 h) he (u := 0) h0
  refine ⟨hw, hc, i, sp, rank, ?_, hm, ht, hrank, hwo⟩
  rcases qUtccp_use hR (Frame.lt_of_get hX hget) hget ⟨rank, ht⟩ with ⟨n, hk⟩ |
    ⟨-, ⟨-, hpc, -⟩ | ⟨-, ⟨ok, hk⟩, -⟩⟩
  · cases hk
  · simp only at hpc
    rw [hget, hpc]
  · cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
