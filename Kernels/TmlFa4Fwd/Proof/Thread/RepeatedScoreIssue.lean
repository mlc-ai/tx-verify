-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreProgress
public import Lemmas.Step.TcLoadProgress
import all Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction TcMma

/-- The pending state follows the decoded distinction between a load and its implicit wait. -/
def scoreLoadResume (round : Round) (ready : TState) (ds : List Nat) (values : List Value) :
    TState :=
  if round = .unbiased then {setRegs (next ready) ds values with pc := ready.pc, sub := 1}
  else setRegs (next ready) ds values

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hGuard : SyncGuarded l kernel X)
include hp hMax hGuard

/-- TMEM score issue from a released cursor, with a separate obligation for
collective completion after the load. -/
theorem scoreLoadIssueWithStateOfMaximal (hLayout : TcMma.LayoutInjective X) {g : Nat}
    (hg : g < l.threads) (round : Round) (quarter : Fin 4) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (scorePc round quarter) F)
    (hAddress : (scoreReg round quarter,b32 (scoreAddress l g stage quarter)) ∈ F)
    (hWords : ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4) :
    ∃ vals ds, vals.length = 32 ∧ ds.length = 32 ∧
      kernel.code[scorePc round quarter]? =
        some ⟨none,.tcLd ds (scoreReg round quarter) .s32x32b none⟩ ∧
      let u := scoreLoadResume round c.ready ds vals
      X.get (g,c.pos) = some
        ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+1)) c.ending := by
  let addr := scoreAddress l g stage quarter
  obtain ⟨ds,hDs,hDecoded,hOut⟩ :=
    scoreLoadTemplateDecoded hp round quarter g stage c.ready c.checkpoint.1
      c.checkpoint.2.2.2.1 c.checkpoint.2.1 (holds_mem c.checkpoint.2.2.2.2 hAddress)
  let resume := scoreLoadResume round c.ready ds
  obtain ⟨vals,hLen,he,hPrefix,hRest⟩ := Step.tcLoadOfMaximal hMax hGuard hLayout hg
    c.positive c.bounded c.released c.recorded c.remaining c.localSteps hOut hWords
    (Assumptions.wfStep _ _ hMax.1 le_snoc (Execution.notifiedInOrder_of_eq rfl)
        (Execution.noNewRead_snoc rfl))
  rw [c.checkpoint.1] at he
  exact ⟨vals,ds,hLen,hDs,hDecoded,he,hPrefix,hRest⟩

theorem scoreLoadIssueOfMaximal (hLayout : TcMma.LayoutInjective X) {g : Nat} (hg : g < l.threads)
    (round : Round) (quarter : Fin 4) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (scorePc round quarter) F)
    (hAddress : (scoreReg round quarter,b32 (scoreAddress l g stage quarter)) ∈ F)
    (hWords : ∀ k < 32, ∀ v, TcMma.LastWrote l Assumptions.all X
      (tcDataCell l g .s32x32b (scoreAddress l g stage quarter) k) v → v.bytes = 4) :
    ∃ vals u, vals.length = 32 ∧
      X.get (g,c.pos) = some
        ⟨scorePc round quarter,.tc (.ld (scoreAddress l g stage quarter) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+1)) c.ending := by
  obtain ⟨vals,ds,hLen,_,_,he,hPast,hTail⟩ :=
    scoreLoadIssueWithStateOfMaximal hp hMax hGuard hLayout hg round quarter stage c hAddress
      hWords
  exact ⟨vals,scoreLoadResume round c.ready ds vals,hLen,he,hPast,hTail⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
