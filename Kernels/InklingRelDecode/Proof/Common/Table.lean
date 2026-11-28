-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DispatchRef
public import Kernels.InklingRelDecode.Proof.Lib.Rounds

public import Kernels.InklingRelDecode.Proof.Loader.PollCount
public import Kernels.InklingRelDecode.Proof.Loader.PageRef
public import Kernels.InklingRelDecode.Proof.Lib.PageWord
public import Kernels.InklingRelDecode.Proof.Mma.Ref
public import Kernels.InklingRelDecode.Proof.Prologue.History
public import Kernels.InklingRelDecode.Proof.Epilogue.Ref
public import Kernels.InklingRelDecode.Proof.Softmax.Ref
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

def iterCount (Q : Params) (L : Launch) (c : Nat) :=
  Lib.blocksOf Q L c

/-- The two worker loops' interpretation of the shared bounds and their successful-poll
ordinals. Dispatch can select either machine on any byte; the reference table records
which warp actually reaches each of them. -/
def workerInv (Q : Params) (L : Launch) (g : Nat) (w : Value) (x : BitVec 64)
    (d : (workerCode Q L g w x).D) (n : Cls → Nat) : Prop :=
  let lo := Iface.preloadCount Q L (g / L.block)
  let hi := iterCount Q L (g / L.block)
  match d with
  | .inl s => DispatchRef (g % L.block / 32) lo hi s n
  | .inr ⟨.loader r, s⟩ => g % L.block / 32 = 6 ∧ Loader.Ref lo hi s ∧
    n (.poll 2374) = Loader.polls lo hi s ∧
    Loader.PageRef (Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x)) s ∧ r = 0
  | .inr ⟨.mma r, s⟩ => g % L.block / 32 = 7 ∧ Mma.Ref hi s ∧
    n (.poll 2462) = (Mma.polls s).1 ∧ n (.poll 2510) = (Mma.polls s).2 ∧
    n (.atPc 2550) + n (.atPc 2551) = s.site.fin ∧ r = 0

def softCounts (n : Cls → Nat) : Softmax.Cnt :=
  ⟨n (.poll 1257),n (.poll 2239),n (.atPc 1013)⟩

def proCounts (L : Launch) (g : Nat) (n : Cls → Nat) : Prologue.Counts :=
  let l := fun b => MbarRow.loc L g (Iface.kvReady b)
  ⟨fun p => n (.atPc p),fun p => n (.voteAt p (laneOf L g)),fun b => n (.arrivalTo (l b)),
   fun b => n (.issueTo (l b)),fun i => n (.bar i)⟩

def tableInv (Q : Params) (L : Launch) (g : Nat) (d : (thread Q L g).D) : Prop :=
  (thread Q L g).inv d ∧ match d with
    | (.inr ⟨.inl (.dispatch w x), s⟩, n) => workerInv Q L g w x s n
    | (.inr ⟨.inl (.prologue _), .inl s⟩, n) =>
      g%L.block<128 ∧ Prologue.History Q L g s (proCounts L g n)
    | (.inr ⟨.inl (.prologue _), .inr ⟨_,.inl s⟩⟩, n) => Softmax.Ref (g%L.block) s (softCounts n)
    | (.inr ⟨.inl (.prologue _), .inr ⟨_,.inr ⟨_,s⟩⟩⟩, n) => Epilogue.Ref s (n (.poll 2565))
    | _ => True

/-- Ghost information is needed only until the lane's first fault. The count is
taken from the outer, continuously counted thread across all role handoffs. -/
def guardedTable (Q : Params) (L : Launch) (g : Nat) (s : (thread Q L g).D) : Prop :=
  s.2 .ub = 0 → tableInv Q L g s

end PTX.Kernels.InklingRelDecode.Proof
