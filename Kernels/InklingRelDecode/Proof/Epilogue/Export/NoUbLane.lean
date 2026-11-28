-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.EpiEntry
import all Kernels.InklingRelDecode.Proof.Common.Export.EpiEntry
import Kernels.InklingRelDecode.Proof.Common.LateThread
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
public import Lemmas.Flow.StepsQFT
public import Lemmas.Kernel.NoUbStrictQPLane
public import Kernels.InklingRelDecode.Proof.Iface.RcpStep
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Lane

@[expose] public section

/-! # No undefined behaviour in the epilogue of a data lane

A data lane's undefined-behaviour event at a pc from 2565 on (`Epilogue.Strict.noUb_epi_core`),
given the entry of the epilogue (`EpiAt`: the lane's state at its first epilogue event with the
tags the softmax's window left), the words the broadcast delivers (`hnames`), the value facts
(`Iface.LateValues`, and the fact `R` of the lane's states with the reciprocal's step and the
single pieces under it). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow PTX.Flow.TyG PTX.Proof

/-- **No data lane has undefined behaviour at a pc of the epilogue.** -/
public theorem noUb_epi {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hv : Iface.LateValues L X) (lane : g % L.block < 128)
    {R : TState → Prop} (hRP : ∀ t, Frame.LaneAt kernel Assumptions.all L X g t → R t)
    (hR : Iface.RcpStep L g R)
    (hS : ∀ pc, 2642 ≤ pc → pc ≤ 2673 → SingleStep kernel Assumptions.all L g R pc)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = Proof.b32 (g % L.block / 32))
    {i k pc : Nat} {f : Fault} (hik : i ≤ k) (hat : EpiEntry Q L X g i)
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) : False :=
  Strict.noUb_epi_core hp hX hf hv lane hRP hR (fun pc h => by
    simp only [Strict.epiS, Bool.and_eq_true, decide_eq_true_eq] at h
    exact hS pc h.1 h.2) hnames hik hat he

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
