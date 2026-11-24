-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase
public import Kernels.InklingRelDecode.Proof.Thread.TmWorker
public import Kernels.InklingRelDecode.Proof.Thread.TmIdle
public import Kernels.InklingRelDecode.Proof.Thread.TmLoader
public import Kernels.InklingRelDecode.Proof.Thread.TmMma
public import Kernels.InklingRelDecode.Proof.Thread.TmWCode
public import Kernels.InklingRelDecode.Proof.Thread.TmDStart
public import Kernels.InklingRelDecode.Proof.Thread.TmProA
public import Kernels.InklingRelDecode.Proof.Thread.TmSm
public import Kernels.InklingRelDecode.Proof.Thread.TmEpi
public import Kernels.InklingRelDecode.Proof.Thread.TmDCode

@[expose] public section

/-! # Undefined-behaviour templates of the thread machines: umbrella

`TmBase` (the instruction forms), one file per role (`TmWorker`, `TmIdle`, `TmLoader`, `TmMma`,
`TmDStart`, `TmProA`, `TmSm`, `TmEpi`) and the two composed machines (`TmWCode`, `TmDCode`):
for every state outside `WComp.tmRest` and `DComp.tmRest`, the template of the instruction at
the state's site is not undefined behaviour. -/
