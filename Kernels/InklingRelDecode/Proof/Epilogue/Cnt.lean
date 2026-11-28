-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Lemmas.Flow.PollRounds

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

/-- The number of successful final polls in this lane's prefix. -/
def polls (d : D) : Nat := if d.site = .wait then 0 else 1

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
