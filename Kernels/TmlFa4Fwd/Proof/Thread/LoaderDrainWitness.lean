-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRingDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyOrdinal
public import Lemmas.Kernel.ExitChain
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.PollSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvEmptyPhase kvUseStage_val emptySlot_address)

noncomputable section

private theorem drainStagesDistinct (use : Nat) {a b : Fin 3} (h : a ≠ b) :
    kvUseStage (use + a.val) ≠ kvUseStage (use + b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  intro he
  have hv := congrArg Fin.val he
  rw [kvUseStage_val, kvUseStage_val] at hv
  apply h
  exact Fin.ext (by omega)

private theorem drainRetryUnmarked {l : Launch} {g use n : Nat} (i : Fin 3) (m : Loc) :
    okPolls m (List.replicate n (drainPoll l g i use false)) = 0 := by
  have hPoll : okPoll m (drainPoll l g i use false) = false := okPoll_wait rfl
  simp [okPolls, hPoll]

private theorem drainOtherUnmarked {l : Launch} {g use n : Nat} {a b : Fin 3} (h : a ≠ b) :
    okPolls (emptyObject l g (kvUseStage (use + b.val)))
      (List.replicate n (drainPoll l g a (use + a.val) false) ++
        [drainPoll l g a (use + a.val) true]) = 0 := by
  have hSlot := drainStagesDistinct use h
  have hAddr : emptyObject l g (kvUseStage (use + a.val)) ≠
      emptyObject l g (kvUseStage (use + b.val)) := by
    intro hLoc
    have hEq := congrArg Loc.addr hLoc
    unfold emptyObject at hEq
    rw [emptySlot_address, emptySlot_address] at hEq
    simp only at hEq
    exact hSlot (Fin.ext (by omega))
  have hPoll : okPoll (emptyObject l g (kvUseStage (use + b.val)))
      (drainPoll l g a (use + a.val) true) = false := by
    rw [okPoll_wait (show drainPoll l g a (use + a.val) true = _ from rfl)]
    simp only [Bool.true_and, decide_eq_false_iff_not]
    exact hAddr
  rw [okPolls_snoc, drainRetryUnmarked, hPoll]
  rfl

private theorem drainCountAppend (m : Loc) (pre post : List Event) :
    okPolls m (pre ++ post) = okPolls m pre + okPolls m post := List.countP_append

private theorem drainPrefix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {s : TState} {events : List Event}
    (hs : At s 1863 (drainCarry l use)) (hr : Run kernel Assumptions.all l g s events none)
    (i : Fin 3) :
    ∃ pre tail, events = pre ++ drainPoll l g i (use + i.val) true :: tail ∧
      okPolls (emptyObject l g (kvUseStage (use + i.val))) pre = 0 := by
  obtain ⟨n0,n1,n2,_,rest,hEs,_,_,_⟩ := ringDrainTrace hp hs hr
  let block (j : Fin 3) (n : Nat) :=
    List.replicate n (drainPoll l g j (use + j.val) false) ++
      [drainPoll l g j (use + j.val) true]
  have hBlocks : events = block 0 n0 ++ (block 1 n1 ++ (block 2 n2 ++ rest)) := by
    simpa [block, List.append_assoc, Fin.val_zero, Fin.val_one] using hEs
  fin_cases i
  · refine ⟨List.replicate n0 (drainPoll l g 0 use false), block 1 n1 ++ (block 2 n2 ++ rest),
      ?_, drainRetryUnmarked 0 _⟩
    rw [hBlocks]
    simp [block, List.append_assoc]
  · refine ⟨block 0 n0 ++ List.replicate n1 (drainPoll l g 1 (use + 1) false),
      block 2 n2 ++ rest, ?_, ?_⟩
    · rw [hBlocks]
      simp [block, List.append_assoc]
    · let loc := emptyObject l g (kvUseStage (use + 1))
      change okPolls loc (block 0 n0 ++ List.replicate n1 (drainPoll l g 1 (use + 1) false)) = 0
      have h0 : okPolls loc (block 0 n0) = 0 := by
        simpa only [block, loc, Fin.val_zero, Fin.val_one, Nat.add_zero] using
          (drainOtherUnmarked (l := l) (g := g) (use := use) (n := n0)
          (by decide : (0 : Fin 3) ≠ 1))
      have h1 : okPolls loc (List.replicate n1 (drainPoll l g 1 (use + 1) false)) = 0 :=
        drainRetryUnmarked 1 loc
      rw [drainCountAppend, h0, h1]
  · refine ⟨block 0 n0 ++ block 1 n1 ++ List.replicate n2 (drainPoll l g 2 (use + 2) false),
      rest, ?_, ?_⟩
    · rw [hBlocks]
      simp [block, List.append_assoc]
    · let loc := emptyObject l g (kvUseStage (use + 2))
      have hTwo : (2 : Fin 3).val = 2 := rfl
      change okPolls loc
        (block 0 n0 ++ block 1 n1 ++ List.replicate n2 (drainPoll l g 2 (use + 2) false)) = 0
      have h0 : okPolls loc (block 0 n0) = 0 := by
        simpa only [block, loc, Fin.val_zero, Fin.val_one, Nat.add_zero, hTwo] using
          (drainOtherUnmarked (l := l) (g := g) (use := use) (n := n0)
          (by decide : (0 : Fin 3) ≠ 2))
      have h1 : okPolls loc (block 1 n1) = 0 := by
        simpa only [block, loc, Fin.val_zero, Fin.val_one, Nat.add_zero, hTwo] using
          (drainOtherUnmarked (l := l) (g := g) (use := use) (n := n1)
          (by decide : (1 : Fin 3) ≠ 2))
      have h2 : okPolls loc (List.replicate n2 (drainPoll l g 2 (use + 2) false)) = 0 :=
        drainRetryUnmarked 2 loc
      rw [drainCountAppend, drainCountAppend, h0, h1, h2]

/-- The final ring acquire at a selected slot has its actual wait index, parity,
and resume edge to exit. Earlier waits within the drain affect other slots. -/
theorem drainAcquireBeforeExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos use : Nat} {s : TState} (hs : At s 1863 (drainCarry l use))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) none)
    (hExit : Thread.Exited X g) (slot : Fin 3) :
    ∃ (wait finish parity : Nat), pos ≤ wait ∧
      parity = (((use + (2 - slot.val)) / 3) + 1) % 2 ∧
      EmptyAcquire l X (g,wait) slot parity ∧
      emptyOrdinal l X (g,wait) slot = okPolls (emptyObject l g slot) ((X.tr g).take pos) ∧
      Resumes kernel X (g,wait) (g,finish) ∧ OwnerExit l X (g / l.block) (g,finish) := by
  have hSlot := slot.isLt
  let offset : Fin 3 := ⟨(slot.val + 3 - use % 3) % 3, Nat.mod_lt _ (by decide)⟩
  have hOffset := offset.isLt
  have hStage : kvUseStage (use + offset.val) = slot := by
    apply Fin.ext
    rw [kvUseStage_val]
    dsimp [offset]
    omega
  let parity := if kvEmptyPhase (use + offset.val) then 1 else 0
  have hParity : parity = (((use + (2 - slot.val)) / 3) + 1) % 2 := by
    have h := congrArg Fin.val hStage
    rw [kvUseStage_val] at h
    have hDiv : (use + offset.val) / 3 = (use + (2 - slot.val)) / 3 := by omega
    unfold parity kvEmptyPhase Mma.kvParity
    rw [hDiv]
    simp only [beq_iff_eq]
    split <;> omega
  obtain ⟨pre, tail, hEs, hCount⟩ := drainPrefix hp hs hr offset
  let j := pos + pre.length
  let ev := drainPoll l g offset (use + offset.val) true
  have he : X.get (g,j) = some ev := by
    change (X.tr g)[pos + pre.length]? = _
    rw [← List.getElem?_drop, hEs, List.getElem?_append_right (by omega)]
    simp [ev]
  have hg := event_thread_lt hX he
  obtain ⟨site, hLast⟩ := hExit.lastEvent hX hg
  let finish := (X.tr g).length - 1
  have hFinish : X.get (g,finish) = some ⟨site,.exit⟩ := by
    change (X.tr g)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  have hJ := (List.getElem?_eq_some_iff.mp he).1
  have hLen := (List.getElem?_eq_some_iff.mp hFinish).1
  have hLt : j < finish := by
    by_contra! h
    have hEq : j = finish := by dsimp [finish] at *; omega
    rw [hEq, hFinish] at he
    have hKind := congrArg Event.kind (Option.some.inj he)
    cases hKind
  have hGet : X.get (g,j) =
      some ⟨ev.pc, .wait (emptyObject l g slot) parity true true .cta⟩ := by
    simpa only [ev, drainPoll, hStage, parity] using he
  obtain ⟨_, hSpin⟩ := actualCanonicalPoll hX hGet
  have hTake : (X.tr g).take j = (X.tr g).take pos ++ pre := by
    have hFull := List.take_append_drop pos (X.tr g)
    rw [hEs] at hFull
    have hPos : pos ≤ (X.tr g).length := by dsimp [j] at hJ; omega
    have hLeft : ((X.tr g).take pos).length = pos := by simp [Nat.min_eq_left hPos]
    have hLength : ((X.tr g).take pos ++ pre).length = j := by
      rw [List.length_append, hLeft]
    conv_lhs => rw [← hFull, ← List.append_assoc]
    exact List.take_left' hLength
  have hRank : emptyOrdinal l X (g,j) slot =
      okPolls (emptyObject l g slot) ((X.tr g).take pos) := by
    change okPolls (emptyObject l g slot) ((X.tr g).take j) = _
    rw [hTake, okPolls, List.countP_append]
    rw [hStage] at hCount
    change pre.countP (okPoll (emptyObject l g slot)) = 0 at hCount
    exact Nat.add_eq_left.mpr hCount
  exact ⟨j, finish, parity, by dsimp [j]; omega, hParity, ⟨_, hGet, rfl⟩, hRank,
    Resumes.of_spin hGet hSpin rfl hLt hLen, hg, rfl, site, hFinish⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
