-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPack
public import Lemmas.Step.LocalReadProgress
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

/-- A live loader reloads the bytes of a saved lane-private scratch cell. -/
theorem scratchCellReadOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X)
    {g pos writePc : Nat} (hg : g < l.threads) {cell : Acc} {data : List Byte}
    (hLocal : cell.loc.space = .local) (hOwner : cell.loc.cta = g)
    (hSize : data.length = cell.size) (hCell : PrimingCellValue X g pos writePc cell data)
    {t u : TState} {ending : Option TState} {next : List (Option Byte) → TState}
    (hNext : Next kernel Assumptions.all l g t u (.read cell next))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨u.pc,.rd cell (data.map some)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next (data.map some))) ∧
      Run kernel Assumptions.all l g (next (data.map some)) ((X.tr g).drop (pos+1)) ending := by
  obtain ⟨write,hBefore,hStore,hLast⟩ := hCell
  refine Step.local_read_of_maximal hMax hg hLocal ⟨writePc,hStore⟩ hBefore
    (by simpa only [List.length_map] using hSize) ?_ ?_ hLast
    hNext hPrefix hTail hBound hRelease ?_
  · intro k hk
    exact ⟨Acc.covers_at hk,by simp [wbyte,Loc.at,hk,hSize]⟩
  · intro k _ w dst bytes hWrite hCover
    obtain ⟨j,hId,hAccess⟩ := localWriteOwner hMax.1 hWrite (loc := cell.loc.at k) hLocal hCover
    exact ⟨j,by simpa only [Loc.at,hOwner] using hId,
      by simpa only [Loc.at,hOwner] using hAccess⟩
  · exact Assumptions.wf_snoc_nonGlobal hMax.1 (by rw [hLocal]; decide)

end PTX.Kernels.TmlFa4Fwd.Loader
