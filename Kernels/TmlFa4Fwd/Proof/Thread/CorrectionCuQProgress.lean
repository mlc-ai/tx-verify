-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionEntryProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionSchedulerEntry
import Lemmas.Step.Read
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The scalar CuQ footprint of a correction lane in its first scheduler group. -/
def laneCuQAcc (p : Params) (l : Launch) (g : Nat) : Acc :=
  {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}

private theorem schedulerReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {t ready : TState} {o : Option TState}
    (ht : At t 7759 (firstLaneFacts p l g))
    (hPrior : 9 ≤ (X.tr g).length)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) ready t)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take 9) (some ready))
    (hTail : Run kernel Assumptions.all l g ready ((X.tr g).drop 9) o)
    (hRelease : 9 = (X.tr g).length → Step.Released l X g) (hLane : laneOf l g ≤ p.batch)
    (hProtected : ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((laneCuQAcc p l g).loc.at k)) :
    ∃ u, X.get (g,9) = some ⟨7761, .rd (laneCuQAcc p l g)
      ((b32 (p.qOffset (laneOf l g))).toBytes.map some)⟩ ∧
      At u 7762 (firstShuffleFacts p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 10) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop 10) o := by
  let a := laneCuQAcc p l g
  let v := b32 (p.qOffset (laneOf l g))
  let bs := v.toBytes.map some
  have hValue : HasValue m a.loc v := by
    simpa [a, laneCuQAcc, v, b32, HasValue, Value.bytes] using hp.cuQ (laneOf l g) hLane
  obtain ⟨u, hPc, hNext, hAt⟩ := firstShuffleReadNext hp hLane ht
  have hn : Next kernel Assumptions.all l g ready u (.read a (afterLoad u [7267])) :=
    ⟨hLocal.trans hNext.steps, hNext.stop⟩
  have hSize : 9 < (X.tr g).length := by
    by_contra! hLe
    have hLen := Nat.le_antisymm hPrior hLe
    have hRel := hRelease hLen
    have hStarted : X.tr g ≠ [] := by
      intro hNil
      rw [hNil, List.length_nil] at hPrior
      omega
    have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some ready) := by
      rw [← List.take_of_length_le hLe]
      exact hPrefix
    let e : Event := ⟨u.pc, .rd a bs⟩
    have hRead : NewRead l m X g e (fun _ => none) a bs := by
      refine ⟨rfl, ?_, ?_⟩
      · intro k hk c hc
        have hEq := Option.some.inj (hc.symm.trans (hValue k hk))
        subst c
        simp [bs, Value.toBytes, show k < v.bytes from hk, Execution.initialByte]
      · intro k w dst bytes hk hWrite hCover _
        exact hProtected k hk w dst bytes hWrite hCover
    have hStep : EStep kernel Assumptions.all l g u e (some (afterLoad u [7267] bs)) :=
      ⟨_, hNext.stop, bs, rfl, rfl, rfl⟩
    exact hMax.not_grows (Step.read_counted_extension hMax.1 hg hStarted hRel hFull
      hn.steps hStep hRead (Assumptions.wf_snoc_initial hMax.1 hRead))
  obtain ⟨_, _, hGet, ⟨bytes, hLen, rfl, hRet⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, hBad⟩; cases hBad) hTail
    (fun hNil => Nat.not_le_of_lt hSize (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hRet
  have hMem : X.MemReads (.thread (g,9)) a bytes := .inl ⟨u.pc, hGet⟩
  have hBytes : bytes = bs := hMax.1.launch_value hMem rfl hProtected hValue
  subst bytes
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take 10)
      (some (afterLoad u [7267] bs)) := by
    rw [List.take_succ_eq_append_getElem hSize, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPrefix.snoc hn.steps ⟨_, hNext.stop, bs, hLen, rfl, rfl⟩
  exact ⟨_, hPc ▸ hGet, hAt, hPast, hRest⟩

/-- A maximal correction lane reaches the first shuffle with its protected CuQ word,
or with the zero word supplied by the sentinel branch. -/
theorem firstShuffleCursorOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((laneCuQAcc p l g).loc.at k)) :
    ∃ j t u o, 0 < j ∧ j ≤ (X.tr g).length ∧ Softmax.beforeFirstScan X g j ∧
      (j = (X.tr g).length → Step.Released l X g) ∧ At u 7762 (firstShuffleFacts p l g) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨t, o, ht, _, hCredit, hPrefix, hTail, hCount, hRelease⟩ :=
    schedulerEntryOfMaximal hp hMax hg hLo hHi
  obtain ⟨u, hu, hU⟩ := prepareSchedulerLane hp ht
  have hPrior : 9 ≤ (X.tr g).length := len_of_get hCredit
  by_cases hLane : laneOf l g ≤ p.batch
  · rw [ite_eq_right (not_lt.mpr hLane)] at hU
    obtain ⟨v, he, hv, hPast, hRest⟩ := schedulerReadOfMaximal hp hMax hg hU hPrior
      (run_rtg hu) hPrefix hTail hRelease hLane (hProtected hLane)
    have hCounts := Softmax.beforeFirstScan_advance hCount he rfl rfl
    exact ⟨10,v,v,o,by decide,len_of_get he,hCounts,releasedIfLast he (by intro h; cases h),
      hv,hPast,hRest,.refl⟩
  · have hSkip := Nat.lt_of_not_ge hLane
    rw [ite_eq_left hSkip] at hU
    exact ⟨9,t,u,o,by decide,hPrior,hCount,hRelease,firstShuffleSkip hSkip hU,hPrefix,hTail,
      run_rtg hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
