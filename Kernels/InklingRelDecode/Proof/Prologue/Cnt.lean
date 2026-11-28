-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Sites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue

/-- Per-PC visit counts across initialization and the three preload blocks. -/
abbrev Cnt := Nat → Nat

def bump (c : Cnt) (e : Event) (pc : Nat) := c pc + (e.pc == pc).toNat

end PTX.Kernels.InklingRelDecode.Proof.Prologue
