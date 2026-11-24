-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueRoles
public import Kernels.TmlFa4Fwd.Proof.PrologueBroadcast
public import Lemmas.Step.Released
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.PlainWriteProgress
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow Prologue

/-- A released loader cursor records an ordinary store in a maximal execution.
The loader role cannot own a pending Tensor Memory allocation result. -/
theorem plainLoaderStoreOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) {a : Acc} {bytes : List Byte}
    (hPlain : a.release = false)
    {t u dst : TState} {ending : Option TState}
    (hNext : Next kernel Assumptions.all l g t u (.write a bytes dst))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨u.pc,.wr a bytes⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run kernel Assumptions.all l g dst ((X.tr g).drop (pos+1)) ending := by
  refine Step.plain_write_of_maximal hMax hg hPlain hNext hPrefix hTail hPos hBound hRelease
    ?_ (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  intro c req hr hEq
  have hCovered := (hMax.1.tmemPair.1 c).1 req hr
  have hActor := (Tmem.Pair.WarpRequest.event_props hCovered.2.2 0).2.1
  have hWarp := Thread.allocatorWarp hp hMax.1 hr
  have hG : (req.own.event l 0).1 = g := congrArg Prod.fst hEq
  rw [hG,hWarp] at hActor
  change warpIndex l g = 12 at hActor
  omega

end PTX.Kernels.TmlFa4Fwd.Loader
