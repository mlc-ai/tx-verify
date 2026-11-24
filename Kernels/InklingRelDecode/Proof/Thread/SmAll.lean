-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSteps
public import Kernels.InklingRelDecode.Proof.Thread.SmGen
public import Kernels.InklingRelDecode.Proof.Thread.SmPst
public import Kernels.InklingRelDecode.Proof.Thread.SmArr
public import Kernels.InklingRelDecode.Proof.Thread.SmS
public import Kernels.InklingRelDecode.Proof.Thread.SmMin
public import Kernels.InklingRelDecode.Proof.Thread.SmEdge
public import Kernels.InklingRelDecode.Proof.Thread.SmBridge
public import Kernels.InklingRelDecode.Proof.Thread.SmWiden
public import Kernels.InklingRelDecode.Proof.Thread.SmSc
public import Kernels.InklingRelDecode.Proof.Thread.SmScW
public import Kernels.InklingRelDecode.Proof.Thread.SmScF
public import Kernels.InklingRelDecode.Proof.Thread.SmScZ
public import Kernels.InklingRelDecode.Proof.Thread.SmScP
public import Kernels.InklingRelDecode.Proof.Thread.SmScM
public import Kernels.InklingRelDecode.Proof.Thread.SmScN
public import Kernels.InklingRelDecode.Proof.Thread.SmScG
public import Kernels.InklingRelDecode.Proof.Thread.SmRng
public import Kernels.InklingRelDecode.Proof.Thread.SmMax
public import Kernels.InklingRelDecode.Proof.Thread.SmStg
public import Kernels.InklingRelDecode.Proof.Thread.SmFlt
public import Kernels.InklingRelDecode.Proof.Thread.SmStgA
public import Kernels.InklingRelDecode.Proof.Thread.SmStgB
public import Kernels.InklingRelDecode.Proof.Thread.SmTot
public import Kernels.InklingRelDecode.Proof.Thread.SmTotA
public import Kernels.InklingRelDecode.Proof.Thread.SmTotB
public import Kernels.InklingRelDecode.Proof.Thread.SmTotC
public import Kernels.InklingRelDecode.Proof.Thread.SmStgC
public import Kernels.InklingRelDecode.Proof.Thread.SmStgD
public import Kernels.InklingRelDecode.Proof.Thread.SmStgE
public import Kernels.InklingRelDecode.Proof.Thread.SmTab
public import Kernels.InklingRelDecode.Proof.Thread.SmTotV
public import Kernels.InklingRelDecode.Proof.Thread.SmTotD
public import Kernels.InklingRelDecode.Proof.Thread.SmTotE
public import Kernels.InklingRelDecode.Proof.Thread.SmTotF
public import Kernels.InklingRelDecode.Proof.Thread.SmTotG
public import Kernels.InklingRelDecode.Proof.Thread.SmTotH
public import Kernels.InklingRelDecode.Proof.Thread.SmExit
public import Kernels.InklingRelDecode.Proof.Thread.SmPeer

/-! # The Inkling softmax region: umbrella

`Sm` (the machine and its register table), `SmBits` and `SmFloat` (tools, the three floating
instructions of the setup and the moves of the zero half-word), `SmSegA` (the setup before the
preloads), `SmSegB` (the next block's pointers), `SmLoads` (the bias loads' guards and the step of
a preload), `SmPackBase`, `SmPack`, `SmMask` and `SmStretch` (the packs of the bias words and of
the key positions, the next block's mask and the stretch from the last preload to the first loop
load), `SmNxt` (the loop's bias loads), `SmSkip` (the masked lanes' skip of the loads) and
`SmSteps` (the steps of `bar0`, the last preload and the loop loads), `SmGen` (generic steps, the
table's last section, the frame lemmas), `SmPst` (the P store), `SmArr` (the arrival on `p_ready`,
the second round's packs and loop test, and the step of `setmaxnreg`), `SmS` (the S-tile poll,
broadcast and load), `SmMin` (the outcome of `min.f32`), `SmEdge` (the running maximum and sum, and
the pieces of the edges into the P store and of the rescale test: the `o_done` parity, the
`min` and the `setp`; the edge from the O rescale's last wait),
`SmBridge` (the running maximum and sum after the update are `Softmax.step`'s) and `SmWiden` (the
`cvt.f32.bf16` and `mov.b32` unpack steps and the bias widening's group of four instructions),
`SmRng` (the score stage's range premise from `Pre`), `SmMax` (the row maximum, pcs 1764 to
1837) and `SmStg` (the machine's maximum, decision and `alpha` as `Softmax.step`'s, and the
bridge lemmas with `alpha` and the row sum read as numbers), `SmFlt` (extended-real exec lemmas
for the stage's floating instructions, the software `exp2` instance as a piece) and `SmStgA` (pcs
1839 to 1848: `m_new`, the decision, `alpha`, `m_use` in the registers; the fused multiply-adds, the
software and `ex2` exponentials and the selections, pcs 1849 to 2168) and `SmStgB` (the packs and
the sum tree, pcs 2169 to 2233; `seg_stageB` from the shuffle of the row maximum to the shuffle of
the half sums, and `step_shfl5`) and `SmTot`, `SmTotA`, `SmTotB`, `SmTotC` (the stage's first
half on any S words: the registers as Core's outcomes, the scores, the mask and the row maximum as
pieces that kill the thread where an instruction faults, and their reading on `f32` numbers) and
`SmStgC` (`step_waitLd`: the S tile's wait to the shuffle of the row maximum) and `SmStgD` (the
steps of the row sum's exchange and the `o_done` poll:
`step_shfl6` to `step_shfl12`, `step_waitO`, `step_bar22`, `step_store10`, `step_bar23`,
`step_ldL`) and `SmStgE` (the O rescale after the test: `step_ldO`, `step_waitLdO` with the 64
products, `step_bar24`, `step_stO`) and `SmExit` (the runs from the four events that end the loop
to pc 2560: `exit_bar0`, `exit_pre`, `exit_bar21`, `exit_arrive`) and `SmPeer` (the partner lane's
facts the two exchanges need: `Peer`, `PeerExchange`, the shared decision, the row sum). `SmBase`
(sites, state, entry numbers) and `SmFin` (the numbers of the score stage as functions of the
state) are below `Sm`. -/
