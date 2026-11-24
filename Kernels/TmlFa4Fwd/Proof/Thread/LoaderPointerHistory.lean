-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStackHistory
public import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape)

noncomputable section

/-- Each packet prepares both source-pointer cells before issuing its two vector reloads. -/
structure PointerPacket where
  save : ScalarSite
  test : Nat
  seed : Nat
  low : Nat
  high : Nat

def pointerPacket : Fin 6 → PointerPacket
  | 0 => ⟨⟨⟨520, 535, 537, 9535, true⟩, 532, 7544, 533, 7545, 534, 0⟩, 5, 773, 543, 609⟩
  | 1 => ⟨⟨⟨785, 800, 802, 9536, true⟩, 797, 7608, 798, 7609, 799, 0⟩, 6, 774, 804, 854⟩
  | 2 => ⟨⟨⟨963, 978, 980, 9537, true⟩, 975, 7663, 976, 7664, 977, 1⟩, 9, 776, 1003, 1072⟩
  | 3 => ⟨⟨⟨1209, 1224, 1226, 9538, true⟩, 1221, 7717, 1222, 7718, 1223, 0⟩,
      10, 777, 1238, 1292⟩
  | 4 => ⟨⟨⟨1433, 1448, 1450, 9539, true⟩, 1445, 7778, 1446, 7779, 1447, 1⟩,
      12, 779, 1469, 1537⟩
  | 5 => ⟨⟨⟨1614, 1629, 1631, 9540, true⟩, 1626, 7822, 1627, 7823, 1628, 0⟩,
      13, 780, 1632, 1685⟩

abbrev PointerPacket.first (p : PointerPacket) : Nat := p.save.loop.first
abbrev PointerPacket.store (p : PointerPacket) : Nat := p.save.accessPc
def PointerPacket.head (p : PointerPacket) : Nat := p.first + 2
def PointerPacket.back (p : PointerPacket) : Nat := p.store + 3

def PointerPacket.inside (p : PointerPacket) (pc : Nat) : Prop := p.first < pc ∧ pc ≤ p.high

def PointerPacket.cell (p : PointerPacket) (l : Launch) (g : Nat) (slot : Fin 2) : Acc :=
  {loc := ⟨.local, g, l.localBase + kvLocalOffset p.save.array slot⟩, size := 8}

def PointerPacket.write (p : PointerPacket) (l : Launch) (g : Nat) (slot : Fin 2)
    (data : List Byte) : Event :=
  ⟨p.store, .wr (p.cell l g slot) data⟩

theorem packetBounds (i : Fin 6) :
    let p := pointerPacket i
    174 < p.first ∧ p.head < p.store ∧ p.back < p.low ∧ p.low < p.high ∧ p.high < 1901 ∧
      p.save.array.val < 2 ∧ p.save.loop.wide = true ∧ p.save ∈ scalarSites := by
  fin_cases i <;> simp [pointerPacket, PointerPacket.head, PointerPacket.back, PointerPacket.first,
    PointerPacket.store, scalarSites,
    storeWords, loadWordsSavePointer]

theorem packetStoreActive (i : Fin 6) :
    (pointerPacket i).save.active .address (pointerPacket i).store := by
  fin_cases i <;> decide

/-- Position of an element within the selected 64-bit pointer cell. -/
def PointerPacket.element (p : PointerPacket) (l : Launch) (g : Nat) (slot word : Fin 2) : Acc :=
  {loc := (p.cell l g slot).loc.at (4 * word.val), size := 4, elem := word.val}

/-- The packet's saved pointer and the suffix that keeps the chosen slot live. -/
def LatestSave (l : Launch) (g : Nat) (p : PointerPacket) (slot : Fin 2)
    (history : List Event) : Prop :=
  LatestCellWrite p.store (p.cell l g slot) history

theorem LatestSave.step {l : Launch} {g : Nat} {p : PointerPacket}
    {slot : Fin 2} {history : List Event} {e : Option Event}
    (h : LatestSave l g p slot history)
    (hKeep : ∀ ev ∈ e.toList, DoesNotClobber (p.cell l g slot) ev) :
    LatestSave l g p slot (history ++ e.toList) :=
  LatestCellWrite.step h hKeep

theorem cellsApart {l : Launch} {g : Nat} {p : PointerPacket}
    (hArray : p.save.array.val < 2) :
    ¬ (p.cell l g 0).Overlap (p.cell l g 1) := by
  rintro ⟨loc, hZero, hOne⟩
  have hA := hZero.2.2.2
  have hB := hOne.2.2.1
  simp [PointerPacket.cell, kvLocalOffset, hArray] at hA hB
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
