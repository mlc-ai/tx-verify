-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.Loader.RefBase

@[expose] public section

/-! # The loader's local loads and the stores they read back

For the sources of the words the pointer rounds and the packets load from local memory
(`Frame.local_read_of_last_store`, `Lemmas/Kernel/Source/Local.lean`): the location of each local
load, and the local stores before it at that location.

* The pointer rounds' loads read `L.localBase + 96 + 4 it` (the page) and `L.localBase + 64 + 4 it`
  (the row), which page round `it` of the same block stored; the packets' address loads read
  element `k` of `L.localBase + b + 8 h` (`b = 32` for a later block's K half, else 0), which
  pointer round `h` of the same half stored as an 8-byte word (`ptP_loc`, `ptR_loc`; the
  packets' loads by `Ev` with `lwBase_val`).
* Every local store of the lane is at one of the offsets `lstOffs` and is counted by the ledger's
  class `lst o` (`RefCounts`, last conjunct: the count is `lstAt`). At a load the count at its
  offset is positive (`lst_ptP`, `lst_ptR`, `lst_lw`); with the ledger (`ledger`), the last store
  before the load at that offset is the event at which the count reached its value, and no store
  of the lane at that offset lies between. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

/-- The page load of pointer round `it`. -/
theorem ptP_loc (hp : Pre p L m) {per : Per} {b : Bool} {it : Fin 2} {v : V} {kk : Fin 2}
    {e : Event} (hev : Ev p L g w ⟨.ptP per b it, v, kk⟩ e) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = ⟨.local, g, L.localBase + (96 + 4 * it.val)⟩ ∧
      a.size = 4 := by
  simp only [Ev] at hev
  obtain ⟨bs, hk⟩ := hev
  refine ⟨_, bs, hk, ?_, rfl⟩
  have hx : rv p L g w ⟨.ptP per b it, v, kk⟩ (ptRegs (pk per b)).b =
      add64 (BitVec.ofNat 64 (L.localBase + 96)) (shl64 (m64 ((it.val : Nat) : Int)) 2) := by
    cases per <;> cases b <;> rfl
  rw [hx, shl64_fin2, add64_ofNat, Nat.add_assoc]
  exact lacc_loc hp (by omega) 4

/-- The row load of pointer round `it`. -/
theorem ptR_loc (hp : Pre p L m) {per : Per} {b : Bool} {it : Fin 2} {v : V} {kk : Fin 2}
    {e : Event} (hev : Ev p L g w ⟨.ptR per b it, v, kk⟩ e) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = ⟨.local, g, L.localBase + (64 + 4 * it.val)⟩ ∧
      a.size = 4 := by
  simp only [Ev] at hev
  obtain ⟨bs, hk⟩ := hev
  refine ⟨_, bs, hk, ?_, rfl⟩
  have hx : rv p L g w ⟨.ptR per b it, v, kk⟩ (ptRegs (pk per b)).c =
      add64 (BitVec.ofNat 64 (L.localBase + 64)) (shl64 (m64 ((it.val : Nat) : Int)) 2) := by
    cases per <;> cases b <;> rfl
  rw [hx, shl64_fin2, add64_ofNat, Nat.add_assoc]
  exact lacc_loc hp (by omega) 4

/-- At a pointer round's page load, the lane has stored the page at its offset. -/
theorem lst_ptP (per : Per) (b : Bool) (it : Fin 2) (k A : Nat) :
    1 ≤ lstAt (.ptP per b it) k A (96 + 4 * it.val) := by
  cases per <;> cases b <;> fin_cases it <;>
    simp (config := { decide := true }) [lstAt, lstPos, lstCum, lstSeq, List.take,
      List.count_cons]

/-- At a pointer round's row load, the lane has stored the row at its offset. -/
theorem lst_ptR (per : Per) (b : Bool) (it : Fin 2) (k A : Nat) :
    1 ≤ lstAt (.ptR per b it) k A (64 + 4 * it.val) := by
  cases per <;> cases b <;> fin_cases it <;>
    simp (config := { decide := true }) [lstAt, lstPos, lstCum, lstSeq, List.take,
      List.count_cons]

/-- The local array of a packet's address loads: the second one for a later block's K half. -/
theorem lwBase_val (per : Per) (b : Bool) :
    lwBase (pk per b) = if per ≠ .prime ∧ b = false then 7293 else 7292 := by
  cases per <;> cases b <;> rfl

/-- At a packet's address load of half `h`, the lane has stored the address at its offset. -/
theorem lst_lw (per : Per) (b : Bool) (h : Fin 2) (k A : Nat) :
    1 ≤ lstAt (.lw per b h) k A ((if per ≠ .prime ∧ b = false then 32 else 0) + 8 * h.val) := by
  cases per <;> cases b <;> fin_cases h <;>
    simp (config := { decide := true }) [lstAt, lstPos, lstCum, lstSeq, List.take,
      List.count_cons]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
