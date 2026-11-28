-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Proof.Iface.EntryEnv
public import Kernels.InklingRelDecode.Proof.Common.Export.EpiEntry
import all Kernels.InklingRelDecode.Proof.Common.Export.EpiEntry
import Kernels.InklingRelDecode.Proof.Common.LateThread
public import Lemmas.Flow.TauStar
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Lane
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Exit
import Kernels.InklingRelDecode.Proof.Common.BcastIdx
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasHalf
import Lemmas.Kernel.FrameU

public section

/-! # No undefined behaviour in the softmax of a data lane

A data lane's undefined-behaviour event at a pc from 574 to 2564, after its event at 573
(`Softmax.Soft.noUb_soft_core`), with the facts of the events its window reads supplied as
trace facts: the typed registers after the barrier (`hE`), the words the broadcasts deliver
(`hnames`) and the bytes the load of the row sum reads (`hld`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof PTX.Flow.TyG

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The events of the window are well formed. -/
private theorem lwf_events (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hv : Iface.LateValues L X) (lane : g % L.block < 128)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    (hld : ∀ i a bs, X.get (g, i) = some ⟨2252, .rd a bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    {j k : Nat} (nu : Frame.NoUbBefore X g k) :
    ∀ i ev, j < i → i < k → X.get (g, i) = some ev → Strict.LWf ev := by
  intro i ev hji hik hev
  obtain ⟨pc', kd⟩ := ev
  have clean : ∀ f, kd ≠ .ub f := fun f => nu i hik _ hev f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a vals sh hmem hk w hw
    obtain rfl : kd = .tc (.ld a vals sh) := hk
    exact hv.tcLd hev lane hmem w hw
  · intro hpc2 mode a b c recv ok hk
    obtain rfl : kd = .shfl mode a b c recv ok := hk
    have hshape := bcast_idx hp hX hf hev hpc2
    obtain ⟨rfl, rfl, rfl⟩ := hshape
    exact ⟨_, hnames _ pc' _ hpc2 ⟨i, a, ok, hev, rfl⟩⟩
  · intro hpc2 a bs hk
    obtain rfl : kd = .rd a bs := hk
    obtain rfl : pc' = 2252 := hpc2
    obtain ⟨v, hv'⟩ := hld i a bs hev
    refine ⟨v, hv', ?_⟩
    obtain ⟨w, hw, hd⟩ := hv.ld hev lane
    obtain rfl : v = w := Except.ok.inj (hv'.symm.trans hw)
    exact hd
  · intro hev2 hrng a bs hk
    obtain rfl : kd = .rd a bs := hk
    dsimp only at hev2 hrng
    have site : (∃ j : Fin 64, pc' = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc' = 1124 + 2 * j.val := by
      rcases hrng with h | h
      · exact .inl ⟨⟨(pc' - 680) / 2, by omega⟩, by simp only; omega⟩
      · exact .inr ⟨⟨(pc' - 1124) / 2, by omega⟩, by simp only; omega⟩
    obtain ⟨x, hx⟩ := bias_half hp hX hf hev site
    exact ⟨_, hx⟩
  · intro hmem mode a b c recv ok hk
    obtain rfl : kd = .shfl mode a b c recv ok := hk
    exact hv.bfly hev lane hmem


/-- **No data lane has undefined behaviour at a pc of the softmax before the epilogue.** -/
public theorem noUb_soft (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    (hld : ∀ i a bs, X.get (g, i) = some ⟨2252, .rd a bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    {j k pc : Nat} {e5 : Event} {f : Fault} (hjk : j < k) (he5 : X.get (g, j) = some e5)
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hpc : pc < 2565)
    (hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      TauStar kernel Assumptions.all L g t0 t1 →
      EStep kernel Assumptions.all L g t1 e5 (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u) : False :=
  Soft.noUb_soft_core hp hX hf base hv lane hnames hjk he5 he hpc hE
    (lwf_events hp hX hf hv lane hnames hld (Frame.noUbBefore_of_get hX he))

/-- **The lane enters the epilogue typed**: at the first event of a data lane from 2565 on. -/
public theorem epi_entry (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (hv : Iface.LateValues L X)
    (lane : g % L.block < 128)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    (hld : ∀ i a bs, X.get (g, i) = some ⟨2252, .rd a bs⟩ → ∃ v, rebuild 3 bs = .ok v)
    {j i : Nat} {e5 ei : Event} (hji : j < i) (he5 : X.get (g, j) = some e5)
    (hei : X.get (g, i) = some ei) (hge : 2565 ≤ ei.pc)
    (hpcw : ∀ i' ev, j < i' → i' < i → X.get (g, i') = some ev → ev.pc < 2565)
    (hE : ∀ t0 t1 u, Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0) →
      TauStar kernel Assumptions.all L g t0 t1 →
      EStep kernel Assumptions.all L g t1 e5 (some u) →
      u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u) : EpiEntry Q L X g i :=
  Soft.epi_at hp hX hf base hv lane hji he5 hei hge hpcw hE
    (lwf_events hp hX hf hv lane hnames hld (Frame.noUbBefore_of_get hX hei))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
