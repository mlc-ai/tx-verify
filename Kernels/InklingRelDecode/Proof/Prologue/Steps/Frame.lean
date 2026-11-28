-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Advance
public import Kernels.InklingRelDecode.Proof.Lib.ControlSpan

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- A silent local run whose stores to registers miss the next site's control facts. -/
noncomputable abbrev crossCheck := Lib.spanCheck ctlLive

theorem cross {Q L g w d p start stop} (checked : crossCheck p start stop) :
    SegU kernel Assumptions.all L g start (facts Q L g w d p) stop (facts Q L g w d stop) :=
  Lib.control_span checked

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
