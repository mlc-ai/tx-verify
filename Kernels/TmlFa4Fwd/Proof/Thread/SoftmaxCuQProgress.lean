-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxEntryProgress
import Lemmas.Step.Read
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private theorem schedulerReadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g i : Nat} (hg : g < l.threads) {warp : Fin 8} {t : TState} {o : Option TState}
    (ht : At t 3104 (schedulerEntry p l g warp)) (hBar : X.IsBarrier (g,i+1) 2 (some 416) 3103)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (i+2)) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop (i+2)) o)
    (hRelease : i+2 = (X.tr g).length → Step.Released l X g) (hLane : laneOf l g ≤ p.batch)
    (hProtected : ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((laneCuQAcc p l g).loc.at k)) :
    ∃ u, X.get (g,i+2) = some ⟨3110, .rd (laneCuQAcc p l g)
      ((b32 (p.qOffset (laneOf l g))).toBytes.map some)⟩ ∧
      At u 3111 (schedulerLane p l g warp (p.qOffset (laneOf l g))) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (i+2+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i+2+1)) o := by
  let a := laneCuQAcc p l g
  let v := b32 (p.qOffset (laneOf l g))
  let bs := v.toBytes.map some
  have hValue : HasValue m a.loc v := by
    simpa [a, laneCuQAcc, v, b32, HasValue, Value.bytes] using hp.cuQ (laneOf l g) hLane
  obtain ⟨u, hPc, hNext, hAt⟩ := schedulerReadNext hp ht hLane
  have hSize : i + 2 < (X.tr g).length := by
    by_contra! hLe
    have hLo : i + 2 ≤ (X.tr g).length := len_of_get hBar
    have hLen := Nat.le_antisymm hLo hLe
    have hRel := hRelease hLen
    have hStarted : X.tr g ≠ [] := by
      intro hNil
      rw [hNil, List.length_nil] at hLo
      omega
    have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
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
    have hStep : EStep kernel Assumptions.all l g u e (some (afterLoad u [7237] bs)) :=
      ⟨_, hNext.stop, bs, rfl, rfl, rfl⟩
    exact hMax.not_grows (Step.read_counted_extension hMax.1 hg hStarted hRel hFull
      hNext.steps hStep hRead (Assumptions.wf_snoc_initial hMax.1 hRead))
  obtain ⟨_, _, hGet, ⟨bytes, hLen, rfl, hRet⟩, hRest⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, hBad⟩; cases hBad) hTail
    (fun hNil => Nat.not_le_of_lt hSize (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hRet
  have hMem : X.MemReads (.thread (g,i+2)) a bytes := .inl ⟨u.pc, hGet⟩
  have hBytes : bytes = bs := hMax.1.launch_value hMem rfl hProtected hValue
  subst bytes
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (i+2+1))
      (some (afterLoad u [7237] bs)) := by
    rw [List.take_succ_eq_append_getElem hSize, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPrefix.snoc hNext.steps ⟨_, hNext.stop, bs, hLen, rfl, rfl⟩
  exact ⟨_, hPc ▸ hGet, hAt, hPast, hRest⟩

/-- The actual softmax lane is ready for the first down shuffle, with the protected CuQ
word for an active lane or zero for a lane beyond the sentinel. -/
theorem firstShuffleCursorOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hSoft : warpIndex l g < 8)
    (hProtected : laneOf l g ≤ p.batch → ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((laneCuQAcc p l g).loc.at k)) :
    let warp : Fin 8 := ⟨warpIndex l g,hSoft⟩
    let q := if laneOf l g ≤ p.batch then p.qOffset (laneOf l g) else 0
    ∃ j t u o, 0 < j ∧ j ≤ (X.tr g).length ∧ beforeFirstScan X g j ∧
      (j = (X.tr g).length → Step.Released l X g) ∧ At u 3111 (schedulerLane p l g warp q) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  dsimp only
  obtain ⟨i, t, o, hBar, ht, hPrefix, hTail, hCount, hRelease⟩ :=
    schedulerEntryOfMaximal hp hMax hg hSoft
  by_cases hLane : laneOf l g ≤ p.batch
  · rw [ite_eq_left hLane]
    obtain ⟨u, he, hu, hPast, hRest⟩ :=
      schedulerReadOfMaximal hp hMax hg ht hBar hPrefix hTail hRelease hLane (hProtected hLane)
    exact ⟨i+2+1,u,u,o,by omega,len_of_get he,beforeFirstScan_advance hCount he rfl rfl,
      releasedIfLast he (by intro h; cases h),hu,hPast,hRest,.refl⟩
  · rw [ite_eq_right hLane]
    obtain ⟨u, hu, hl⟩ := schedulerSkipLocal hp ht (Nat.lt_of_not_ge hLane)
    exact ⟨i+2,t,u,o,by omega,len_of_get hBar,hCount,hRelease,hu,hPrefix,hTail,hl⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
