-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainGates
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.MBarrier PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val kvEmptyPhase)

noncomputable section

private structure EmptyPollState (l : Launch) (X : Execution) (g index : Nat)
    (slot : Fin 3) (parity : Nat) where
  atRecord : Nat
  record : Record Ref
  state : State
  present : (X.objects (emptyObject l g slot))[atRecord]? = some record
  id : record.id = .thread (g,index)
  success : record.reply.waited = some true
  checked : stateBefore (X.objects (emptyObject l g slot)) atRecord = some state
  opposite : state.phase % 2 ≠ parity % 2
  completed : record.reply.completed = if 0 < state.phase then some (state.phase-1) else none

private theorem EmptyPollState.ofAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i parity : Nat} {slot : Fin 3} (h : EmptyAcquire l X (g,i) slot parity) :
    Nonempty (EmptyPollState l X g i slot parity) := by
  obtain ⟨j, r, hRecord, hId, hAction, _, hSuccess⟩ := h.record hp hX
  obtain ⟨st, q, hState, hQ, hOpposite, hCompleted⟩ :=
    (X.objects_checked hX (emptyObject l g slot)).okPoll hRecord hSuccess
  obtain rfl := (Action.pollParity.inj (hQ.symm.trans hAction)).1
  exact ⟨⟨j,r,st,hRecord,hId,hSuccess,hState,hOpposite,hCompleted⟩⟩

private theorem EmptyPollState.phase_lt {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j a b : Nat} {slot : Fin 3}
    (first : EmptyPollState l X g i slot a) (later : EmptyPollState l X g j slot b)
    (hOrder : i < j) (hParity : a % 2 ≠ b % 2) : first.state.phase < later.state.phase := by
  let loc := emptyObject l g slot
  have hNo : NoInval (X.objects loc) :=
    objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hBefore :=
    (hX.object_thread_index_iff first.present later.present first.id later.id).2 hOrder
  have hLen := (List.getElem?_eq_some_iff.mp later.present).1
  obtain ⟨s, hs, hMono⟩ := (X.objects_checked hX loc).phase_mono
    hNo hBefore.le hLen.le first.checked
  obtain rfl := Option.some.inj (hs.symm.trans later.checked)
  have hFirst := first.opposite
  have hLater := later.opposite
  omega

private theorem emptyParityOfUse (n : Nat) (slot : Fin 3) :
    (if kvEmptyPhase (3*n+slot.val) then 1 else 0) = (n+1)%2 := by
  have hLt := slot.isLt
  have hDiv : (3*n+slot.val)/3 = n := by omega
  simp only [kvEmptyPhase, Mma.kvParity, hDiv, beq_iff_eq]
  split <;> omega

private theorem alternatingPhaseLower {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g count : Nat} {slot : Fin 3} (position : Nat → Nat)
    (hAcquire : ∀ n, 0 < n → n ≤ count →
      EmptyAcquire l X (g,position n) slot ((n+1)%2))
    (hLt : ∀ n n', 0 < n → n < n' → n' ≤ count → position n < position n')
    (hPos : 0 < count) :
    ∃ (q : Nat) (r : Record Ref),
      (X.objects (emptyObject l g slot))[q]? = some r ∧ r.id = .thread (g,position count) ∧
      r.reply.waited = some true ∧
      ∃ phase, observedAt (X.objects (emptyObject l g slot)) q = some phase ∧ count ≤ phase+1 := by
  let getState (n : Nat) (hn : 0 < n) (hle : n ≤ count) :=
    Classical.choice (EmptyPollState.ofAcquire hp hX (hAcquire n hn hle))
  have lower (n : Nat) (hn : 0 < n) (hle : n ≤ count) :
      n ≤ (getState n hn hle).state.phase := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hBase : n = 1
      · have hOpp := (getState n hn hle).opposite
        omega
      · have hOld : 0 < n-1 := by omega
        have hSmall : n-1 < n := by omega
        have hEarlier : n-1 ≤ count := by omega
        have hParity : ((n-1+1)%2)%2 ≠ ((n+1)%2)%2 := by omega
        have hGrow := (getState (n-1) hOld hEarlier).phase_lt hX
          (getState n hn hle) (hLt (n-1) n hOld hSmall hle) hParity
        have hLower := ih (n-1) hSmall hOld hEarlier
        omega
  let last := getState count hPos (Nat.le_refl _)
  have hLower := lower count hPos (Nat.le_refl _)
  have hNonzero : 0 < last.state.phase := by dsimp [last]; omega
  refine ⟨last.atRecord,last.record,last.present,last.id,last.success,last.state.phase-1,?_,?_⟩
  · change ((X.objects (emptyObject l g slot))[last.atRecord]?).bind (·.reply.completed) = _
    rw [last.present, Option.bind_some, last.completed, ite_eq_left hNonzero]
  · dsimp only [last]
    omega

/-- The final acquire observes at least the phase corresponding to the lane's
actual final cursor. Each intermediate lower bound comes from a real gate of
that slot on the lane. -/
theorem drainObservedOfCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g seed final pos : Nat} {s : TState} {front : List Event}
    (hTake : (X.tr g).drop seed = front ++ (X.tr g).drop (seed + front.length))
    (hPackets : PacketsBeforeDrain l g 2 final front) (hBefore : seed + front.length ≤ pos)
    (hs : At s 1863 (drainCarry l final))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) none)
    (hExit : Thread.Exited X g) (slot : Fin 3) :
    let count := (final + (2-slot.val))/3
    0 < count →
    ∃ (wait finish index phase : Nat) (r : Record Ref),
      (X.objects (emptyObject l g slot))[index]? = some r ∧
      r.id = .thread (g,wait) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (emptyObject l g slot)) index = some phase ∧ count ≤ phase+1 ∧
      Resumes kernel X (g,wait) (g,finish) ∧ OwnerExit l X (g / l.block) (g,finish) := by
  let count := (final + (2-slot.val))/3
  change 0 < count → _
  intro hPositive
  obtain ⟨j, finish, parity, hJ, hParity, hDrain, _, hResumes, hOwner⟩ :=
    drainAcquireBeforeExit hp hX hs hRun hExit slot
  obtain ⟨gate, site, hGates, hOrder⟩ := hPackets.indexedGates
  let use := fun n => 3*n+slot.val
  let position := fun n => if n = count then j else seed + gate (use n)
  have hSlot := slot.isLt
  have hUse (n : Nat) (hn : 0 < n) (hle : n < count) : 2 ≤ use n ∧ use n < final := by
    dsimp [count,use] at hle ⊢
    omega
  have hIndex (n : Nat) (hn : 0 < n) (hle : n < count) : gate (use n) < front.length :=
    (List.getElem?_eq_some_iff.mp (hGates _ (hUse n hn hle).1 (hUse n hn hle).2)).1
  have hAcquire (n : Nat) (hn : 0 < n) (hle : n ≤ count) :
      EmptyAcquire l X (g,position n) slot ((n+1)%2) := by
    by_cases he : n = count
    · subst n
      simp only [position,ite_true]
      exact hParity ▸ hDrain
    have hLess := lt_of_le_of_ne hle he
    have hAt := hGates _ (hUse n hn hLess).1 (hUse n hn hLess).2
    have hGet : X.get (g, seed + gate (use n)) =
        some (cursorPoll l g (use n) (site (use n)) true) := by
        change (X.tr g)[seed + gate (use n)]? = _
        rw [← List.getElem?_drop, hTake, List.getElem?_append_left (hIndex n hn hLess)]
        exact hAt
    have hStage : kvUseStage (use n) = slot := by
      apply Fin.ext
      rw [kvUseStage_val]
      dsimp [use]
      omega
    refine ⟨_, by simpa only [position,ite_eq_right he] using hGet, ?_⟩
    change Kind.wait (emptyObject l g (kvUseStage (use n)))
      (if kvEmptyPhase (use n) then 1 else 0) true true .cta =
      .wait (emptyObject l g slot) ((n+1)%2) true true .cta
    rw [hStage, emptyParityOfUse]
  have hLt (n n' : Nat) (hn : 0 < n) (hlt : n < n') (hLe : n' ≤ count) :
      position n < position n' := by
    have hN : n ≠ count := by omega
    by_cases he : n' = count
    · simp only [position,ite_eq_right hN,ite_eq_left he]
      have := hIndex n hn (by omega)
      omega
    have hBefore' : use n < use n' := by dsimp [use]; omega
    have hOrd := hOrder (use n) (use n') (hUse n hn (by omega)).1 hBefore'
      (hUse n' (by omega) (lt_of_le_of_ne hLe he)).2
    simp only [position,ite_eq_right hN,ite_eq_right he]
    omega
  obtain ⟨index,r,hRecord,hId,hSuccess,phase,hSeen,hFloor⟩ :=
    alternatingPhaseLower hp hX position hAcquire hLt hPositive
  simp only [position,ite_true] at hId
  exact ⟨j,finish,index,phase,r,hRecord,hId,hSuccess,hSeen,hFloor,hResumes,hOwner⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
