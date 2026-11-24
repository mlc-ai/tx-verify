-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreCollective
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction TcMma

/-- A register left unchanged by a repeated score load and its sixteen pair packs. -/
def RepeatedScorePreserved (mode : Repeated) (quarter : Fin 4) (reg : Nat) : Prop :=
  (reg < repeatedScoreWordBase mode quarter ∨ repeatedScoreWordBase mode quarter+32 ≤ reg) ∧
  ∀ pair : Fin 16, reg ≠ repeatedScorePairReg mode quarter pair.val

/-- The observed score words and their recorded, returning packed cursor. -/
structure PackedScoreQuarter (l : Launch) (X : Execution) (g : Nat) (mode : Repeated)
    (quarter : Fin 4) (stage : Fin 2) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (scorePc mode.round quarter) F) where
  words : List Value
  cursor : OpeningTripCursor l X g (scorePc mode.round quarter+17) []
  length : words.length = 32
  position : cursor.pos = input.pos+repeatedScoreStride mode
  ending : cursor.ending = input.ending
  score : X.get (g,input.pos) =
    some ⟨scorePc mode.round quarter,.tc (.ld (scoreAddress l g stage quarter) words .s32x32b)⟩
  packed : ∀ k < 16, cursor.ready.regs (repeatedScorePairReg mode quarter k) =
    some (joinValue (words.getD (2*k) (b32 0)) (words.getD (2*k+1) (b32 0)))
  preserved : ∀ r, RepeatedScorePreserved mode quarter r → cursor.ready.regs r = input.ready.regs r
  ordinal : ((X.tr g).take cursor.pos).countP isTcColl =
    ((X.tr g).take input.pos).countP isTcColl+repeatedScoreStride mode

private theorem scoreReturnedCount {X : Execution} {g pos : Nat}
    (mode : Repeated) (quarter : Fin 4) (stage : Fin 2) (words : List Value)
    (he : X.get (g,pos) =
      some ⟨scorePc mode.round quarter,.tc (.ld (scoreAddress l g stage quarter) words .s32x32b)⟩)
    (hw : mode.round = .unbiased →
      X.get (g,pos+1) = some ⟨scorePc mode.round quarter,.tc .waitLd⟩) :
    ((X.tr g).take (pos+repeatedScoreStride mode)).countP isTcColl =
      ((X.tr g).take pos).countP isTcColl+repeatedScoreStride mode := by
  cases mode
  · exact countP_take_succ (p := isTcColl) he rfl
  · change ((X.tr g).take (pos+1+1)).countP isTcColl = ((X.tr g).take pos).countP isTcColl+2
    rw [countP_take_succ (p := isTcColl) (hw rfl) rfl,countP_take_succ (p := isTcColl) he rfl]

/-- Every lane advances through the actual load and its event-free pack instructions. -/
theorem warpScorePackOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : TcMma.LayoutInjective X)
    (lead ordinal : Nat) (mode : Repeated) (quarter : Fin 4) (stage : Fin 2)
    {F : Nat → List (Nat × Value)}
    (c : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (scorePc mode.round quarter) (F g))
    (hAddress : ∀ g, SameWarp l lead g →
      (scoreReg mode.round quarter,b32 (scoreAddress l g stage quarter)) ∈ F g)
    (hRank : ∀ g (hWarp : SameWarp l lead g),
      ((X.tr g).take (c g hWarp).pos).countP isTcColl = ordinal)
    (hWords : ∀ g, SameWarp l lead g → ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4)
    (hBytes : ∀ g (hWarp : SameWarp l lead g) (words : List Value),
      X.get (g,(c g hWarp).pos) =
        some ⟨scorePc mode.round quarter,
          .tc (.ld (scoreAddress l g stage quarter) words .s32x32b)⟩ →
      ∀ k < 32, (words.getD k (b32 0)).bytes = 4) :
    ∀ g (hWarp : SameWarp l lead g), Nonempty (PackedScoreQuarter l X g mode quarter stage
      (c g hWarp)) := by
  intro g hWarp
  let t := c g hWarp
  obtain ⟨words,ds,hLen,_,hCode,he,hw,hPast,hTail,hRelease⟩ :=
    warpScoreLoadOfMaximal hp hMax hGuard hLayout lead ordinal mode.round quarter stage
      c hAddress hRank hWords g hWarp
  have hD := congrArg Instr.op
    (Option.some.inj (hCode.symm.trans (repeatedScoreDecode mode quarter)))
  have hEq := (Op.tcLd.inj hD).1
  subst ds
  obtain ⟨u,hAt,hLocal,hPacks,hFrame⟩ := repeatedScorePackLocal (l := l) (g := g)
    mode quarter t.checkpoint words hLen (hBytes g hWarp words he)
  let stop := t.pos+repeatedScoreStride mode
  have hStop : (if mode.round = .unbiased then t.pos+2 else t.pos+1) = stop := by
    cases mode <;> rfl
  change Run kernel Assumptions.all l g {}
    ((X.tr g).take (if mode.round = .unbiased then t.pos+2 else t.pos+1)) _ at hPast
  change Run kernel Assumptions.all l g _
    ((X.tr g).drop (if mode.round = .unbiased then t.pos+2 else t.pos+1)) t.ending at hTail
  rw [hStop] at hPast hTail hRelease
  have hBound : stop ≤ (X.tr g).length := by
    cases mode
    · exact len_of_get he
    · exact len_of_get (hw rfl)
  have hPositive : 0 < stop := by
    have := t.positive
    dsimp [stop]
    omega
  exact ⟨⟨words,⟨stop,_,u,t.ending,hPositive,hBound,hRelease,hAt,hPast,hTail,hLocal⟩,hLen,rfl,rfl,
    he,hPacks,(fun r h => hFrame r h.1 (fun k hk => h.2 ⟨k,hk⟩)),
    scoreReturnedCount mode quarter stage words he hw⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
