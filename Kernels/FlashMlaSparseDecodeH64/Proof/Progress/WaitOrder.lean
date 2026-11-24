-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMachine

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Proof _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

noncomputable section

/-- Each block's work is ordered from index publication through raw copy, dequantization,
QK, softmax and PV. Reuse waits depend on a strictly earlier block of the same row. -/
def blockTime (block offset : Nat) : Nat := 200 + 4096 * block + offset

/-- The common barrier after all blocks and the result stores. -/
def completionTime (P : Params) (L : Launch) (g : Nat) : Nat :=
  blockTime (Result.blocks P (ctaidY L g)) 4096

def softmaxTime (P : Params) (L : Launch) (g : Nat) (d : Wg0.D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore => 103 + wg0Ordinal d.site
  | .everyone => completionTime P L g
  | .exit => completionTime P L g + 1
  | .lseBar | .lseStore0 | .lseBar2 | .lseRead | .lseStore | .svDone | .fenceEpilogue |
    .oLoad _ | .oWait _ | .oStage _ _ | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _ |
    .commit => blockTime (Result.blocks P (ctaidY L g)) (4 * wg0Ordinal d.site + d.sub)
  | _ => blockTime d.block (600 + 4 * wg0Ordinal d.site + d.sub)

def matmulTime (P : Params) (L : Launch) (g : Nat) (d : Wg1Mma.D) : Nat :=
  match d.site with
  | .outBar => completionTime P L g
  | .exit => completionTime P L g + 2
  | .head => 101
  | .elect | .loadTopk | .loadExtra | .qLoad _ | .qArrive | .qWait | .qFence |
    .qCopy _ | .qCopyCommit | .qCopyWait | .qCopyFence => 110 + mmaOrdinal d.site
  | .soWait | .soFence | .pvMma _ | .pvCommit => blockTime d.i (1400 + mmaOrdinal d.site)
  | _ => blockTime d.i (400 + mmaOrdinal d.site)

def gatherTime (P : Params) (L : Launch) (g : Nat) (d : Wg1Tma.D) : Nat :=
  match d.site with
  | .barrier => completionTime P L g
  | .exit => completionTime P L g + 2
  | .elect | .lenOrig | .lenExtra => 108 + tmaOrdinal d.site
  | .waitQ | .waitLast => 150 + tmaOrdinal d.site
  | _ => blockTime d.block (100 + tmaOrdinal d.site)

def indexTime (P : Params) (L : Launch) (g : Nat) (d : Wg1Index.D) : Nat :=
  match d.site with
  | .barrier => completionTime P L g
  | .lenOrig | .lenExtra => 110 + indexOrdinal d.site
  | _ => blockTime d.block (indexOrdinal d.site)

def quantTime (P : Params) (L : Launch) (g : Nat) (d : Wg2.D) : Nat :=
  match d.site with
  | .barrier => completionTime P L g
  | .lenOrig | .lenExtra => 108 + wg2Ordinal d.site
  | .qUtccp => 150
  | _ => blockTime d.block (256 + wg2Ordinal d.site)

/-- Position of a role's current abstract event in the CTA's dependency order. -/
def priority (P : Params) (L : Launch) (g : Nat) : Machine.ThreadD → Nat
  | .prologue s => 100 - prologueRank s
  | .head => 101
  | .wg0 d => softmaxTime P L g d
  | .mma d => matmulTime P L g d
  | .tma d => gatherTime P L g d
  | .index d => indexTime P L g d
  | .idle .loadTopk => 114
  | .idle .loadExtra => 115
  | .idle .sync => completionTime P L g
  | .idle .exit | .done => completionTime P L g + 2
  | .wg2 d => quantTime P L g d

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
