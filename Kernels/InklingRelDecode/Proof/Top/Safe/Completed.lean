-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemInstruction
import Kernels.InklingRelDecode.Proof.Top.Safe.ValEnv
import Kernels.InklingRelDecode.Proof.Top.Safe.Rescale
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkResults
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
import Kernels.InklingRelDecode.Proof.Protocol.Values.Results
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryTile
import Kernels.InklingRelDecode.Proof.Protocol.Values.PElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.StoreElement
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Softmax.Export.PWordsAt

@[expose] public section

/-! # Every completed MMA's result cells have a value

The elements an MMA reads (`Elements`) are numbers: the K and V tiles and the query tile, the
probabilities, and the words of the rescale store; then one induction along the MMA lane gives the
value of every result cell (`Protocol.Values.results`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **Every completed MMA's unmasked result cells have a derived value.** -/
theorem Safe.completed (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : ¬HasUb X) (safe : ¬Race L X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    Safe.Completed L X := by
  have hou : NoUbOutside L X := .of_noUb hu
  obtain ⟨base, words, hG, hws, ht, hmd, form⟩ := Safe.valEnv hp hX hf safe rows init
  have W := @Safe.rescaleFloat _ _ _ hp _ hX hf hou safe rows init nub
  have E : Elements (fun _ => True) L X :=
    Safe.elementsOf hp hX hf hou safe rows init nub fun _ hrd hs hv =>
      store_element hp hX hf hou hG safe base rows init hrd hs hv fun hst => W hst
  intro i d s acc mask hi hd c ⟨d2, s2, a2, m2, r2, c2, hi2, hp2⟩
  obtain ⟨g, k⟩ := i
  obtain ⟨r, hr⟩ := results hp hX hf hou safe base rows init hG hws ht hmd E
    (fun _ _ _ _ _ _ _ => trivial) k g d2 s2 a2 m2 r2 c2 c
    trivial hi2 hp2 hd
  exact ⟨_, hr⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
