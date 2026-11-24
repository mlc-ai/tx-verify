-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerInstructions

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

/-- The two unsigned words in the lane-private metadata arrays. -/
inductive MetadataWord
  | page
  | row
  deriving DecidableEq

namespace LocalAccessCode

/-- A refresh loop initializes both fields of each entry for the following K/V pair. -/
structure MetadataLoop where
  page : ScalarSite
  row : ScalarSite
  test : Nat
  seed : Nat
  endPc : Nat

abbrev MetadataLoop.first (s : MetadataLoop) : Nat := s.row.loop.first
abbrev MetadataLoop.idx (s : MetadataLoop) : Nat := s.row.loop.reg
abbrev MetadataLoop.rowPc (s : MetadataLoop) : Nat := s.row.accessPc

def MetadataLoop.head (s : MetadataLoop) : Nat := s.first + 2
def MetadataLoop.back (s : MetadataLoop) : Nat := s.rowPc + 3

def MetadataLoop.inside (s : MetadataLoop) (pc : Nat) : Prop :=
  s.first < pc ∧ pc ≤ s.endPc

def MetadataLoop.save (s : MetadataLoop) : MetadataWord → ScalarSite
  | .page => s.page
  | .row => s.row

def metadataArray : MetadataWord → Fin 4
  | .page => 3
  | .row => 2

def metadataCell (l : Launch) (g : Nat) (field : MetadataWord) (slot : Fin 2) : Acc :=
  {loc := ⟨.local, g, l.localBase + kvLocalOffset (metadataArray field) slot⟩, size := 4}

def MetadataLoop.latest (s : MetadataLoop) (l : Launch) (g : Nat) (field : MetadataWord)
    (slot : Fin 2) (history : List Event) : Prop :=
  LatestCellWrite (s.save field).accessPc (metadataCell l g field slot) history

def MetadataLoop.saved (s : MetadataLoop) (l : Launch) (g : Nat) (slot : Fin 2)
    (history : List Event) : Prop :=
  s.latest l g .page slot history ∧ s.latest l g .row slot history

theorem metadataCellsApart {l : Launch} {g : Nat}
    {x y : MetadataWord} {a b : Fin 2} (h : x ≠ y ∨ a ≠ b) :
    ¬ (metadataCell l g x a).Overlap (metadataCell l g y b) := by
  rintro ⟨loc, ha, hb⟩
  have hlo := ha.2.2.1
  have hhi := ha.2.2.2
  have hlo' := hb.2.2.1
  have hhi' := hb.2.2.2
  cases x <;> cases y <;> fin_cases a <;> fin_cases b <;>
    simp [metadataCell, metadataArray, kvLocalOffset] at h hlo hhi hlo' hhi'
  all_goals omega

theorem metadataPointerApart {l : Launch} {g : Nat} {p : PointerPacket}
    (hArray : p.save.array.val < 2) (w : MetadataWord) (a b : Fin 2) :
    ¬ (metadataCell l g w a).Overlap (p.cell l g b) := by
  rintro ⟨loc, ha, hb⟩
  have hLo := ha.2.2.1
  have hHi := hb.2.2.2
  have hSlot := b.isLt
  cases w <;> simp [metadataCell, metadataArray, PointerPacket.cell, kvLocalOffset, hArray]
    at hLo hHi
  all_goals omega

end LocalAccessCode
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
