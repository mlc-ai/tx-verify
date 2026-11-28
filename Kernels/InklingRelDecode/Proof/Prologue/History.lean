-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.RefNext
public import Kernels.InklingRelDecode.Proof.Prologue.RefGate
public import Kernels.InklingRelDecode.Proof.Prologue.RefWords
public import Kernels.InklingRelDecode.Proof.Prologue.Ev

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow Control

def wonAt (p lane : Nat) (e : Event) := e.pc == p && match e.kind with
  | .elect _ _ l => l == lane
  | _ => false

structure Counts where
  visits : Cnt
  vote : Nat → Nat
  arrivals : Fin 3 → Nat
  copies : Fin 3 → Nat
  bars : Nat → Nat

def Counts.zero : Counts := ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def Counts.bump (L : Launch) (g : Nat) (c : Counts) (e : Event) : Counts :=
  let l := fun b => MbarRow.loc L g (Iface.kvReady b)
  ⟨Prologue.bump c.visits e,fun p => c.vote p+(wonAt p (laneOf L g) e).toNat,
   fun b => c.arrivals b+(arrivesOn (l b) e).toNat,
   fun b => c.copies b+(issuesTo (l b) e).toNat,fun id => c.bars id+(Execution.isBarId id e).toNat⟩

def four (c : Cnt) (b : Fin 3) :=
  c (ptcPc b 0)+c (ptcPc b 1)+c (ptcPc b 2)+c (ptcPc b 3)

/-- The arrival and issue counts are charged to distinct instruction visits. The two startup
barriers have already fired on entry. -/
structure History (Q : Params) (L : Launch) (g : Nat) (d : D) (c : Counts) : Prop where
  visits : Ref d c.visits
  known : Known Q ((L.ctaidOf (g/L.block)).get .z) d
  block : OpenBlock d (preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d)
  won : ∀ p, d.site.votePc = some p → 0<c.vote p
  arrive : ∀ b, c.arrivals b ≤ c.visits (arrPc b)
  copy : ∀ b, c.copies b ≤ four c.visits b
  bars : d.site.rank ≤ 4*179 → c.bars 0=2 ∧ c.bars 1=0

theorem history_init (Q L g) (bars : Nat → Nat) (h0 : bars 0=2) (h1 : bars 1=0) :
    History Q L g {} {Counts.zero with bars} := by
  refine ⟨initial_ref,known_init ..,?_,?_,fun _ => Nat.zero_le _,fun _ => Nat.zero_le _,
    fun _ => ⟨h0,h1⟩⟩ <;> intro _ h <;> cases h

/-- There are at most three preceding issues on the object of the current issue. -/
theorem History.copy_lt {Q L g d c} (h : History Q L g d c) (b j) (hs : d.site=.ptc b j) :
    c.copies b<4 := by
  have bounds : ∀ b j, 130≤ptcPc b j ∧ ptcPc b j≤315 := by decide +kernel
  have once (k : Fin 4) := h.visits.once (ptcPc b k) (bounds b k).1 (bounds b k).2
  have fresh := h.visits.fresh (ptcPc b j) (bounds b j).1 (bounds b j).2 (by rw [hs]; rfl)
  have charge := h.copy b
  unfold four at charge
  have := once 0
  have := once 1
  have := once 2
  have := once 3
  fin_cases j
  · change c.visits (ptcPc b 0)=0 at fresh; omega
  · change c.visits (ptcPc b 1)=0 at fresh; omega
  · change c.visits (ptcPc b 2)=0 at fresh; omega
  · change c.visits (ptcPc b 3)=0 at fresh; omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue
