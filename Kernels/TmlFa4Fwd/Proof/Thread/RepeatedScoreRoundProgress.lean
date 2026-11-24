-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePackProgress
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction TcMma

/-- A prefix of one round's four score collectives and their local packs. -/
structure PackedScorePrefix (l : Launch) (X : Execution) (g : Nat) (mode : Repeated)
    (stage : Fin 2) (n : Nat) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (scorePc mode.round 0) F) where
  cursor : OpeningTripCursor l X g (scorePc mode.round 0+17*n) []
  words : Fin 4 → List Value
  position : cursor.pos = input.pos+repeatedScoreStride mode*n
  ordinal : ((X.tr g).take cursor.pos).countP isTcColl =
    ((X.tr g).take input.pos).countP isTcColl+repeatedScoreStride mode*n
  ending : cursor.ending = input.ending
  length : ∀ q : Fin 4, q.val < n → (words q).length = 32
  score : ∀ q : Fin 4, q.val < n → X.get (g,input.pos+repeatedScoreStride mode*q.val) =
    some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) (words q) .s32x32b)⟩
  packed : ∀ (q : Fin 4), q.val < n → ∀ k < 16,
    cursor.ready.regs (repeatedScorePairReg mode q k) =
      some (joinValue ((words q).getD (2*k) (b32 0)) ((words q).getD (2*k+1) (b32 0)))
  preserved : ∀ r, (∀ q : Fin 4, q.val < n → RepeatedScorePreserved mode q r) →
    cursor.ready.regs r = input.ready.regs r

private def unpackedPrefix {l : Launch} {X : Execution} {g : Nat} (mode : Repeated)
    (stage : Fin 2) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (scorePc mode.round 0) F) :
    PackedScorePrefix l X g mode stage 0 input where
  cursor := ⟨input.pos,input.before,input.ready,input.ending,input.positive,input.bounded,
    input.released,input.checkpoint.mono trivial,input.recorded,input.remaining,input.localSteps⟩
  words := fun _ => []
  position := by simp
  ordinal := by simp
  ending := rfl
  length := fun _ h => by omega
  score := fun _ h => by omega
  packed := fun _ h => by omega
  preserved := fun _ _ => rfl

private def PackedScorePrefix.loadCursor {l : Launch} {X : Execution} {g n : Nat}
    {mode : Repeated} {stage : Fin 2} {F : List (Nat × Value)}
    {input : OpeningTripCursor l X g (scorePc mode.round 0) F}
    (c : PackedScorePrefix l X g mode stage n input) (q : Fin 4)
    (hq : q.val = n)
    (hReg : input.ready.regs (scoreReg mode.round q) = some (b32 (scoreAddress l g stage q))) :
    OpeningTripCursor l X g (scorePc mode.round q)
      [(scoreReg mode.round q,b32 (scoreAddress l g stage q))] := by
  have hFrame (j : Fin 4) (_ : j.val < n) : RepeatedScorePreserved mode j (scoreReg mode.round q) :=
    repeatedScoreAddressesSeparate mode j q
  have hPc := (repeatedScorePcOffset mode q).trans (by rw [hq])
  refine ⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
    c.cursor.bounded,c.cursor.released,?_,c.cursor.recorded,c.cursor.remaining,c.cursor.localSteps⟩
  exact hPc.symm ▸ c.cursor.checkpoint.mono
    ⟨(c.preserved _ hFrame).trans hReg,trivial⟩

private theorem PackedScorePrefix.extend {l : Launch} {X : Execution} {g n : Nat}
    {mode : Repeated} {stage : Fin 2} {F : List (Nat × Value)}
    {input : OpeningTripCursor l X g (scorePc mode.round 0) F}
    (c : PackedScorePrefix l X g mode stage n input) (q : Fin 4) (hq : q.val = n)
    (hReg : input.ready.regs (scoreReg mode.round q) = some (b32 (scoreAddress l g stage q)))
    (packed : PackedScoreQuarter l X g mode q stage (c.loadCursor q hq hReg)) :
    Nonempty (PackedScorePrefix l X g mode stage (n+1) input) := by
  have hPc := (repeatedScorePcSequence mode q).trans (by rw [hq])
  let b := packed.cursor
  let cur : OpeningTripCursor l X g (scorePc mode.round 0+17*(n+1)) [] :=
    ⟨b.pos,b.before,b.ready,b.ending,b.positive,b.bounded,b.released,
      hPc ▸ b.checkpoint,b.recorded,b.remaining,b.localSteps⟩
  have hCurPos : cur.pos = packed.cursor.pos := rfl
  have hCurEnd : cur.ending = packed.cursor.ending := rfl
  have hCurReg : cur.ready = packed.cursor.ready := rfl
  let words := fun i => if i = q then packed.words else c.words i
  have hNext (i : Fin 4) (hi : i.val < n+1) (hne : i ≠ q) : i.val < n := by
    have hne' : i.val ≠ q.val := fun h => hne (Fin.ext h)
    omega
  refine ⟨⟨cur,words,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [hCurPos,packed.position]
    change c.cursor.pos + _ = _
    rw [c.position,Nat.mul_succ,Nat.add_assoc]
  · rw [hCurPos,packed.ordinal]
    change ((X.tr g).take c.cursor.pos).countP isTcColl + _ = _
    rw [c.ordinal,Nat.mul_succ,Nat.add_assoc]
  · rw [hCurEnd,packed.ending]
    exact c.ending
  · intro i hi
    by_cases hEq : i = q
    · simpa only [words,hEq,ite_true] using packed.length
    · simpa only [words,hEq,ite_false] using c.length i (hNext i hi hEq)
  · intro i hi
    by_cases hEq : i = q
    · subst i
      have he := packed.score
      change X.get (g,c.cursor.pos) = _ at he
      rw [c.position] at he
      simpa only [words,ite_true,hq] using he
    · simpa only [words,hEq,ite_false] using c.score i (hNext i hi hEq)
  · intro i hi k hk
    rw [hCurReg]
    by_cases hEq : i = q
    · subst i
      simpa only [words,ite_true] using packed.packed k hk
    · have hSafe := repeatedScorePairsSeparate mode i q ⟨k,hk⟩ hEq
      rw [packed.preserved _ hSafe]
      change c.cursor.ready.regs _ = _
      simpa only [words,hEq,ite_false] using c.packed i (hNext i hi hEq) k hk
  · intro r hr
    rw [hCurReg,packed.preserved _ (hr q (by omega))]
    change c.cursor.ready.regs r = input.ready.regs r
    exact c.preserved r (fun i hi => hr i (by omega))

/-- The four score collectives of an active repeated visit all return and pack locally. -/
theorem warpRepeatedScoresOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : TcMma.LayoutInjective X)
    (lead ordinal : Nat) (mode : Repeated) (stage : Fin 2)
    {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (scorePc mode.round 0) (F g))
    (hAddresses : ∀ g, SameWarp l lead g → ∀ q : Fin 4,
      (scoreReg mode.round q,b32 (scoreAddress l g stage q)) ∈ F g)
    (hRank : ∀ g (hWarp : SameWarp l lead g),
      ((X.tr g).take (input g hWarp).pos).countP isTcColl = ordinal)
    (hWords : ∀ g, SameWarp l lead g → ∀ q : Fin 4, ∀ k < 32, ∀ v,
      TcMma.LastWrote l Assumptions.all X
        (tcDataCell l g .s32x32b (scoreAddress l g stage q) k) v → v.bytes = 4)
    (hBytes : ∀ g (hWarp : SameWarp l lead g) (q : Fin 4) (words : List Value),
      X.get (g,(input g hWarp).pos+repeatedScoreStride mode*q.val) =
        some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) words .s32x32b)⟩ →
      ∀ k < 32, (words.getD k (b32 0)).bytes = 4) :
    ∀ g (hWarp : SameWarp l lead g), Nonempty (PackedScorePrefix l X g mode stage 4
      (input g hWarp)) := by
  have hPrefix (n : Nat) (hn : n ≤ 4) :
      ∀ g (hWarp : SameWarp l lead g), Nonempty (PackedScorePrefix l X g mode stage n
        (input g hWarp)) := by
    induction n with
    | zero => exact fun g h => ⟨unpackedPrefix mode stage (input g h)⟩
    | succ n ih =>
      let q : Fin 4 := ⟨n,by omega⟩
      let cursors g (h : SameWarp l lead g) := Classical.choice (ih (by omega) g h)
      have hReg g (h : SameWarp l lead g) :=
        holds_mem (input g h).checkpoint.2.2.2.2 (hAddresses g h q)
      let loads g (h : SameWarp l lead g) := (cursors g h).loadCursor q rfl (hReg g h)
      have hOrdinal g (h : SameWarp l lead g) :
          ((X.tr g).take (loads g h).pos).countP isTcColl =
            ordinal+repeatedScoreStride mode*n := by
        change ((X.tr g).take (cursors g h).cursor.pos).countP isTcColl = _
        rw [(cursors g h).ordinal,hRank g h]
      have hWidth g (h : SameWarp l lead g) (values : List Value)
          (he : X.get (g,(loads g h).pos) =
            some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩) :=
        hBytes g h q values (by
          change X.get (g,(cursors g h).cursor.pos) = _ at he
          rwa [(cursors g h).position] at he)
      have hNext := warpScorePackOfMaximal hp hMax hGuard hLayout lead
        (ordinal+repeatedScoreStride mode*n) mode q stage loads
        (fun _ _ => .head _) hOrdinal (fun g h => hWords g h q) hWidth
      intro g h
      obtain ⟨u⟩ := hNext g h
      exact (cursors g h).extend q rfl (hReg g h) u
  exact hPrefix 4 (by decide)

end PTX.Kernels.TmlFa4Fwd.Softmax
