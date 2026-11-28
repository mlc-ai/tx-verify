-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Flow.Sites
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Facts

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Proof PTX.Flow

noncomputable section

inductive Site where
  | head | sync | read
  | idleDec | idleSync | idleSyncAgain | idleInc
  | badSync | badSyncAgain
  | loaderEntry | mmaEntry
  | exitSync | exitDealloc | ret
  deriving DecidableEq

def Site.pc : Site → Nat
  | .head => 2337 | .sync => 2338 | .read => 2340
  | .idleDec => 2333 | .idleSync => 2334 | .idleSyncAgain => 2335 | .idleInc => 2336
  | .badSync => 2557 | .badSyncAgain => 2558
  | .loaderEntry => 2344 | .mmaEntry => 2422
  | .exitSync => 2853 | .exitDealloc => 2854 | .ret => 2855

/-- The byte is the index of the branch table at PC 2343. Larger indices take the
guarded branch at PC 2342 and rendezvous twice before retrying dispatch. -/
def target : Nat → Site
  | 0 => .loaderEntry | 1 => .mmaEntry | 2 => .idleDec | 3 => .exitSync
  | _ => .badSync

def readTarget (bs : List (Option Byte)) : Option Site := do
  let v ← (rebuild 3 bs).toOption
  let .bits 32 r ← (extendLoaded (.zero 32) 8 v).toOption | none
  pure (target (truncBits 32 r).toNat)

structure D where
  site : Site
  round : Nat

def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go := fun s => some (some {d with site := s})
  let again := some (some ⟨.head, d.round + 1⟩)
  match d.site with
  | .head => go .sync
  | .sync => go .read
  | .read =>
    match e.kind with
    | .rd _ bs => (readTarget bs).map fun s => some {d with site := s}
    | _ => none
  | .idleDec => go .idleSync
  | .idleSync => go .idleSyncAgain
  | .idleSyncAgain => go .idleInc
  | .idleInc | .badSyncAgain => again
  | .badSync => go .badSyncAgain
  | .exitSync => go (if g % L.block < 32 then .exitDealloc else .ret)
  | .exitDealloc => go .ret
  | .ret => none
  | .loaderEntry | .mmaEntry => some none

/-- Inherited live registers survive every dispatch round. The address register 536 is
recomputed by the add at 2339 from the shared base and the startup shuffle result. -/
def valueOf (L : Launch) (g : Nat) (x : BitVec 64) (inherited : Nat → Value) : Nat → Value
  | 3 => .pred (decide (g % L.block < 32))
  | 465 => .bits 32 x
  | 534 => .bits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)))
  | 536 => .bits 32 (truncBits 32 (
      truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))) +
      truncBits 32 x))
  | r => inherited r

@[reducible] def code (L : Launch) (g : Nat) (inherited : Nat → Value) (x : BitVec 64)
    (round : Nat) : Flow.Code kernel Assumptions.all L g where
  D := D
  init := ⟨.head, round⟩
  pc := (·.site.pc)
  facts := fun d => Flow.factsFrom (Flow.live d.site.pc) (valueOf L g x inherited)
  inv := fun d => d.site = .exitDealloc → g % L.block < 32
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof.Dispatch
