-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorAbi
public import Kernels.TmlFa4Fwd.Proof.MmaSchedulerEntry
import Lemmas.Flow.AllocTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (startupQRegistersCore startupQLow descriptorShufflePos
  entryFacts startupFacts localRun firstSchedulerNextWithFrame firstSchedulerSkipWithFrame
  firstSchedulerPos)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

private theorem firstSchedulerCursor (hw : warpIndex l g = 12) :
    let pos := descriptorShufflePos (laneOf l g)
    ∃ t u o flag,
      X.get (g,pos) =
        some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 (b32 (startupQLow l)) flag⟩ ∧
      X.ShflK (g,pos) 3 ∧
      At u 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)] ∧
      u.regs 1072 = some (b32 (g / l.block)) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨t, o, flag, hShfl, hOrdinal, ht, hPrefix, hTail⟩ :=
    TmlFa4Fwd.Mma.schedulerAbiAtDescriptorWithOrdinal hp hMax hg hw
  obtain ⟨u, hCore, hu⟩ := startupQRegistersCore hp g t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hLoc := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hCore
  have hFrame {r : Nat} (hm : r ∈ [7203, 7506, 1072]) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 1917) (len := 18) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hCore ht.1.ge (by rw [ht.1]) hm
  have hU : At u 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)] :=
    hu.mono ⟨hu.2.2.2.2.1,
      (hFrame (by decide)).trans (holds_mem ht.2.2.2.2 (by simp [entryFacts])),
      (hFrame (by decide)).trans (holds_mem ht.2.2.2.2 (by simp [entryFacts, startupFacts])),
      trivial⟩
  have hCta : u.regs 1072 = some (b32 (g / l.block)) := (hFrame (r := 1072) (by decide)).trans
    (holds_mem ht.2.2.2.2 (by simp [entryFacts]))
  exact ⟨t, u, o, flag, hShfl, hOrdinal, hU, hCta, hPrefix, run_rtg hLoc, hTail⟩

private theorem activeSchedulerRead (hLane : laneOf l g ≤ p.batch)
    (hProtected : ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * laneOf l g)).at k)) {t u : TState} {o : Option TState}
    {flag : Bool}
    (hShfl : X.get (g, descriptorShufflePos (laneOf l g)) =
      some ⟨1916, .shfl .idx (b32 (startupQLow l)) 0 31 (b32 (startupQLow l)) flag⟩)
    (hU : At u 1935 [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (7506, b64 p.cuQBase)])
    (hCta : u.regs 1072 = some (b32 (g / l.block)))
    (hPrefix : Run kernel Assumptions.all l g {}
      ((X.tr g).take (descriptorShufflePos (laneOf l g) + 1)) (some t))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hTail : Run kernel Assumptions.all l g t
      ((X.tr g).drop (descriptorShufflePos (laneOf l g) + 1)) o) :
    let pos := descriptorShufflePos (laneOf l g) + 1
    ∃ s, X.get (g,pos) = some ⟨1940,
        .rd {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
          ((b32 (p.qOffset (laneOf l g))).toBytes.map some)⟩ ∧
      At s 1941 [(7193, b32 (drainCuQ p (laneOf l g))),
        (1180, b32 (laneOf l g)), (7203, b32 p.batch), (1072, b32 (g / l.block))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1)) (some s) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨s, hS, hCtaReg, hn⟩ := firstSchedulerNextWithFrame hp hLane hU
  let a : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
  let v := b32 (p.qOffset (laneOf l g))
  let bs := v.toBytes.map some
  let pos := descriptorShufflePos (laneOf l g) + 1
  have hValue : HasValue m a.loc v := hp.cuQ _ hLane
  have hNext : Next kernel Assumptions.all l g t s (.read a (afterLoad s [7193])) :=
    ⟨hl.trans hn.steps, hn.stop⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hLower : pos ≤ (X.tr g).length := len_of_get hShfl
    have hEq : pos = (X.tr g).length := Nat.le_antisymm hLower hLe
    have hStart : X.tr g ≠ [] := by
      intro hNil
      have hi := len_of_get hShfl
      rw [hNil, List.length_nil] at hi
      omega
    have hReleased := releasedIfLast (l := l) hShfl (by intro h; cases h) hEq
    have hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
      rw [← List.take_of_length_le hLe]
      exact hPrefix
    let ev : Event := ⟨s.pc, .rd a bs⟩
    have hRead : NewRead l m X g ev (fun _ => none) a bs := by
      refine ⟨rfl, ?_, ?_⟩
      · intro k hk c hc
        have hByte := hValue k hk
        have hEq := Option.some.inj (hc.symm.trans hByte)
        subst c
        have hk' : k < v.bytes := hk
        simp [bs, Value.toBytes, hk', Execution.initialByte]
      · intro k w b bytes hk hWrite hCover _
        exact hProtected k hk w b bytes hWrite hCover
    exact hMax.not_grows (Step.read_counted_extension hMax.1 hg hStart hReleased
      hRun hNext.steps (⟨_, hNext.stop, bs, rfl, rfl, rfl⟩ :
        EStep kernel Assumptions.all l g s ev (some (afterLoad s [7193] bs)))
      hRead (Assumptions.wf_snoc_initial hMax.1 hRead))
  obtain ⟨_, _, he, ⟨bytes, hLen, rfl, hOut⟩, hRest⟩ := hNext.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hOut
  have hGet : X.get (g,pos) = some ⟨1940, .rd a bytes⟩ := hS.1 ▸ he
  have hMem : X.MemReads (.thread (g,pos)) a bytes := .inl ⟨1940, hGet⟩
  have hBytes := hMax.1.launch_value hMem rfl hProtected hValue
  subst bytes
  have hAt : At (afterLoad s [7193] bs) 1941
      [(7193, v), (1180, b32 (laneOf l g)), (7203, b32 p.batch), (1072, b32 (g / l.block))] := by
    have hRebuild := rebuild_b32 (p.qOffset (laneOf l g))
    have hLoad : afterLoad s [7193] bs = next (setReg s 7193 v) := by
      rw [afterLoad_ok hS.2.1 hS.2.2.1 hRebuild]
      simp [next, setReg, hS.2.1, hS.2.2.1, v]
    have hArgs : At s 1940
        [(1180, b32 (laneOf l g)), (7203, b32 p.batch), (1072, b32 (g / l.block))] :=
      hS.mono ⟨hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1, hCtaReg.trans hCta, trivial⟩
    exact hLoad ▸ hArgs.set (by
      intro pair hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact (by decide : 1180 ≠ 7193)
      · exact (by decide : 7203 ≠ 7193)
      · exact (by decide : 1072 ≠ 7193))
  have hAt' : At (afterLoad s [7193] bs) 1941
      [(7193, b32 (drainCuQ p (laneOf l g))), (1180, b32 (laneOf l g)), (7203, b32 p.batch),
        (1072, b32 (g / l.block))] := by
    simpa [drainCuQ, hLane, v] using hAt
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1))
      (some (afterLoad s [7193] bs)) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos] = ⟨s.pc, .rd a bs⟩ := by
      change (X.tr g)[pos]? = _ at he
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at he
    rw [hEq]
    exact hPrefix.snoc hNext.steps ⟨_, hNext.stop, bs, hLen, rfl, rfl⟩
  exact ⟨_, hGet, hAt', hPast, hRest⟩

/-- The initial scheduler has a local route to the down shuffle in every participating lane. -/
theorem schedulerDownCursorFramed (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) :
    let pos := firstSchedulerPos p (laneOf l g)
    ∃ t u o, pos ≤ (X.tr g).length ∧ ((X.tr g).take pos).countP Execution.isShfl = 4 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 1941 [(7193, b32 (drainCuQ p (laneOf l g))),
        (1180, b32 (laneOf l g)), (7203, b32 p.batch), (1072, b32 (g / l.block))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  obtain ⟨t, u, o, flag, hShfl, hOrd4, hu, hCta, hRun, hLocal, hTail⟩ :=
    firstSchedulerCursor hp hMax hg hw
  let pos := descriptorShufflePos (laneOf l g)
  have hCount : ((X.tr g).take (pos + 1)).countP Execution.isShfl = 4 := by
    rw [List.take_add_one, show (X.tr g)[pos]? = _ from hShfl]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    change ((X.tr g).take pos).countP Execution.isShfl + 1 = 4
    rw [show ((X.tr g).take pos).countP Execution.isShfl = 3 from hOrd4.2]
  by_cases hLane : laneOf l g ≤ p.batch
  · obtain ⟨w, he, ht, hPast, hRest⟩ := activeSchedulerRead hp hMax hg hLane
      (hProtected _ hLane) hShfl hu hCta hRun hLocal hTail
    have hLen : pos + 2 ≤ (X.tr g).length := len_of_get he
    have hCount' : ((X.tr g).take (pos + 2)).countP Execution.isShfl = 4 := by
      rw [show pos + 2 = pos + 1 + 1 by omega, List.take_add_one,
        show (X.tr g)[pos+1]? = _ from he]
      simpa [Execution.isShfl] using hCount
    have hRel : pos + 2 = (X.tr g).length → Step.Released l X g :=
      releasedIfLast he (by intro h; cases h)
    simpa [firstSchedulerPos, pos, hLane, Nat.add_assoc] using
      (show ∃ t u o, pos + 2 ≤ (X.tr g).length ∧
          ((X.tr g).take (pos + 2)).countP Execution.isShfl = 4 ∧
          (pos + 2 = (X.tr g).length → Step.Released l X g) ∧
          At u 1941 [(7193, b32 (drainCuQ p (laneOf l g))),
        (1180, b32 (laneOf l g)), (7203, b32 p.batch), (1072, b32 (g / l.block))] ∧
          Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 2)) (some t) ∧
          Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
          Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 2)) o from
        ⟨w, w, o, hLen, hCount', hRel, ht, hPast, .refl, hRest⟩)
  · obtain ⟨w, hW, hCtaReg, hTau⟩ := firstSchedulerSkipWithFrame hp (Nat.lt_of_not_ge hLane) hu
    have hRel : pos + 1 = (X.tr g).length → Step.Released l X g :=
      releasedIfLast hShfl (by intro h; cases h)
    simp only [firstSchedulerPos, hLane, ↓reduceIte, Nat.add_zero]
    exact ⟨t, w, o, len_of_get hShfl, hCount, hRel,
      hW.mono ⟨hW.2.2.2.2.1, hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.1, hCtaReg.trans hCta, trivial⟩,
      hRun, hLocal.trans hTau, hTail⟩

/-- The scheduler's first masked word is prepared when its down shuffle becomes runnable. -/
theorem schedulerDownCursor (hw : warpIndex l g = 12) (hProtected : DrainCuQProtected p X) :
    let pos := firstSchedulerPos p (laneOf l g)
    ∃ t u o, pos ≤ (X.tr g).length ∧ ((X.tr g).take pos).countP Execution.isShfl = 4 ∧
      (pos = (X.tr g).length → Step.Released l X g) ∧
      At u 1941 [(7193, b32 (drainCuQ p (laneOf l g)))] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  obtain ⟨t, u, o, hLen, hCount, hRel, hu, hPrefix, hl, hTail⟩ :=
    schedulerDownCursorFramed hp hMax hg hw hProtected
  exact ⟨t, u, o, hLen, hCount, hRel, hu.mono ⟨hu.2.2.2.2.1, trivial⟩,
    hPrefix, hl, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
