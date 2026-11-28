-- SPDX-License-Identifier: Apache-2.0
-- iface: KvPreload producer=P status=row-proved domain=consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.Objects
public import Lemmas.Flow.ElectLead
public import Lemmas.Flow.NotTensor

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX.Flow

def kvReadyLoc (L : Launch) (cta : Nat) (slot : Fin 3) : Loc :=
  ⟨.shared, cta, L.sharedBase + kvReady slot⟩

/-- The first stages containing only old keys, limited by the work of this split. -/
def preloadCount (Q : Params) (L : Launch) (c : Nat) : Nat :=
  let request := (L.ctaidOf c).get .z
  let split := (L.ctaidOf c).get .x
  let old := (Q.past request / 128 - split + (Q.splits - 1)) / Q.splits
  min 3 (min old (Q.numIters request split))

/-- The prologue's contributions to each full barrier. At a prefix, the arrival and the
copies are classified individually, even if some of the eight issues are still pending. -/
structure KvPreload (Q : Params) (L : Launch) (X : Execution) : Prop where
  arrive : ∀ {g k pc c slot tx count rel scope}, 27 ≤ pc → pc < 574 →
    X.get (g, k) = some ⟨pc, .arrive (kvReadyLoc L c slot) tx count rel scope⟩ →
    g / L.block = c ∧ g % L.block = 0 ∧ slot.val < preloadCount Q L c ∧
    pc = ([193, 237, 279] : List Nat)[slot.val]! ∧ tx = 65536 ∧ count = 1 ∧
    arrivals (kvReadyLoc L c slot) ((X.tr g).take k) = 0
  copy : ∀ {g k pc c slot a sp}, 27 ≤ pc → pc < 574 →
    X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar = kvReadyLoc L c slot →
    g / L.block = c ∧ slot.val < preloadCount Q L c ∧ g % L.block / 32 < 2 ∧
    Elected ((X.tr g).take k) (laneOf L g) ∧ TensorTransfer.bytes sp.descriptor = 8192 ∧
    ((X.tr g).take k).countP (issuesTo (kvReadyLoc L c slot)) < 4

end PTX.Kernels.InklingRelDecode.Proof.Iface
