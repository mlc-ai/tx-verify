-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Cnt
public import Kernels.InklingRelDecode.Proof.Prologue.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue

structure Ref (d : Control.D) (c : Cnt) : Prop where
  once : ∀ p, 130 ≤ p → p ≤ 315 → c p ≤ 1
  fresh : ∀ p, 130 ≤ p → p ≤ 315 → d.site.rank ≤ 4*p → c p = 0

theorem initial_ref : Ref {} (fun _ => 0) := ⟨by simp,by simp⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue
