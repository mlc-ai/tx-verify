-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemInstruction
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.ASource
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccSource
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdSource
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AsyncDone
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
import Kernels.InklingRelDecode.Proof.Lib.Guarded
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTma

@[expose] public section

/-! # ERR-TMEM-READ-SOURCE: Tensor Memory reads have a source

`TcMma.SourceUnsafe` by reader kind. A PV MMA's A read has the latest write before it as its source
(`Tmem.a_source`), an accumulator read likewise (`Tmem.acc_source`), and a load register the latest
write before the load (`Tmem.ld_source_done`), every writer being ordered with the reader and
the MMAs having their values (`Safe.Completed`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The mbarrier records do not fault**, so the Tensor Core order is acyclic. -/
theorem Safe.guarded (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) : SyncGuarded L kernel X :=
  Lib.guardedOfNoObjectFault hX fun l r hr => by
    cases hf' : r.fault with
    | none => rfl
    | some f => exact absurd (.inl ⟨l, r, hr, by simp [hf']⟩) (Safe.noTma hp hX hf rows init)

/-- **ERR-TMEM-READ-SOURCE**: Tensor Memory reads have a source. -/
theorem Safe.noTmemSource (hp : Pre Q L m) {X : Execution}
    (base : Iface.BaseRead L X) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : ¬HasUb X) (safe : ¬Race L X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) (hCV : Safe.Completed L X) :
    ¬ TcMma.SourceUnsafe L Assumptions.all X := by
  unfold TcMma.SourceUnsafe
  rw [not_not, TcMma.sourceSafe_iff]
  have hG := Safe.guarded hp hX hf rows init
  have hws : TcMma.WritesSafe L X := not_not.mp
    (Tmem.writes_safe hp hX hf base (Tmem.qk_store_order hp hX hf safe base rows init)
      (Tmem.pv_store_order hp hX hf safe base rows init))
  have ht := Export.tmem_facts hp hX hf base
  have hcv : ∀ {r : EvId} {cell : TcMma.Cell}, ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      X.MmaCell i cell → TcMma.WriteBefore L X i r → TcMma.CompletedValues L Assumptions.all X i :=
    fun i d s acc mask hi _ _ => hCV i d s acc mask hi
  have hmd : Tmem.AccessCp.AsyncDoneDealloc L X := Tmem.async_done hp hX hf rows init base
  refine ⟨fun e j cell hl => by
      obtain ⟨s, v, h1, h2, -⟩ :=
        Tmem.ld_source_done hp hX hf (.of_noUb hu) safe base rows init hG hws ht hcv hl
      exact ⟨s, v, h1, h2⟩,
    fun i cell hd hc => ?_, fun i cell _ hc =>
    Tmem.a_source hp hX hf (.of_noUb hu) safe base rows init hG hws ht hmd hcv hc⟩
  by_cases hfirst : ∃ d s mask, X.get i = some ⟨Lib.pvIssue 0, .tc (.mma d s true mask)⟩
  · obtain ⟨g, kp⟩ := i
    obtain ⟨d, s, mask, e⟩ := hfirst
    exact Tmem.acc_source hp hX hf safe base rows init hG hws ht hmd hcv hd hc
      (Tmem.acc_first hp hX hf (.of_noUb hu) base hc e)
  · obtain ⟨g, kp⟩ := i
    exact Tmem.acc_source hp hX hf safe base rows init hG hws ht hmd hcv hd hc
      (Tmem.acc_prev hp hX hf (.of_noUb hu) base hc fun d s mask e => hfirst ⟨d, s, mask, e⟩)

end PTX.Kernels.InklingRelDecode.Proof.Top
