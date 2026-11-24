-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Spec
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # The kernel's mbarriers

Every CTA initializes 37 mbarriers in its dynamic shared memory, 36 at offsets `0, 8, …, 280`
(warp 0's elected lane, in offset order) and one at `320` (warp 12's elected lane). Each has a
name by its protocol (`FBar`), an offset, an arrival count and a poll offset: a thread that
polls a barrier whose waiters start at parity 1 (the "empty" or credit barriers) uses the parity
after its own successful polls plus one (`pollOffset`). Three pairs (`+176/+184`, `+208/+216`,
`+224/+232`) are initialized and never used (`spare`).

| Offset | Barrier | Count |
|---|---|---|
| `0 + 8 st` | `qFull st` | 1 |
| `16 + 8 st` | `qEmpty st` | 1 |
| `32 + 8 s` | `kvFull s` (`s < 6`) | 1 |
| `80 + 8 s` | `kvEmpty s` | 1 |
| `128 + 8 st` | `sFull st` | 1 |
| `144 + 8 st` | `pReady st` | 512 |
| `160 + 8 st` | `pReady2 st` | 8 |
| `176 + 8 st` | `spare 0 st` | 1 |
| `192 + 8 st` | `oFull st` | 1 |
| `208 + 8 st` | `spare 1 st` | 256 |
| `224 + 8 st` | `spare 2 st` | 128 |
| `240 + 8 st` | `stats st` | 128 |
| `256 + 8 st` | `oStaged st` | 128 |
| `272 + 8 st` | `oFree st` | 32 |
| `320` | `dealloc` | 32 |
-/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

/-- The kernel's mbarriers, by protocol. -/
inductive FBar where
  | qFull (st : Fin 2)
  | qEmpty (st : Fin 2)
  | kvFull (s : Fin 6)
  | kvEmpty (s : Fin 6)
  | sFull (st : Fin 2)
  | pReady (st : Fin 2)
  | pReady2 (st : Fin 2)
  | oFull (st : Fin 2)
  | stats (st : Fin 2)
  | oStaged (st : Fin 2)
  | oFree (st : Fin 2)
  /-- The initialized, unused pairs at `+176`, `+208`, `+224`. -/
  | spare (k : Fin 3) (st : Fin 2)
  /-- The Tensor Memory deallocation handshake (`+320`). -/
  | dealloc
  deriving DecidableEq, Fintype

namespace FBar

/-- The barrier's shared offset. -/
def off : FBar → Nat
  | .qFull st => 8 * st.val
  | .qEmpty st => 16 + 8 * st.val
  | .kvFull s => 32 + 8 * s.val
  | .kvEmpty s => 80 + 8 * s.val
  | .sFull st => 128 + 8 * st.val
  | .pReady st => 144 + 8 * st.val
  | .pReady2 st => 160 + 8 * st.val
  | .spare 0 st => 176 + 8 * st.val
  | .oFull st => 192 + 8 * st.val
  | .spare 1 st => 208 + 8 * st.val
  | .spare 2 st => 224 + 8 * st.val
  | .stats st => 240 + 8 * st.val
  | .oStaged st => 256 + 8 * st.val
  | .oFree st => 272 + 8 * st.val
  | .dealloc => 320

/-- The arrival count the barrier is initialized with. -/
def count : FBar → Nat
  | .pReady _ => 512
  | .pReady2 _ => 8
  | .spare 1 _ => 256
  | .spare 2 _ => 128
  | .stats _ => 128
  | .oStaged _ => 128
  | .oFree _ => 32
  | .dealloc => 32
  | _ => 1

/-- The parity offset of the barrier's polls: 1 for the barriers whose waiters pass the first
phase without an arrival (Q and KV empty, the statistics credit, the free output stage). -/
def pollOffset : FBar → Nat
  | .qEmpty _ | .kvEmpty _ | .stats _ | .oFree _ => 1
  | _ => 0

/-- The barrier warp 0's elected lane initializes `j`-th (`j < 36`): the one at offset `8 j`. -/
def ofInit (j : Fin 36) : FBar :=
  if _ : j.val < 2 then .qFull ⟨j.val, by omega⟩
  else if _ : j.val < 4 then .qEmpty ⟨j.val - 2, by omega⟩
  else if _ : j.val < 10 then .kvFull ⟨j.val - 4, by omega⟩
  else if _ : j.val < 16 then .kvEmpty ⟨j.val - 10, by omega⟩
  else if _ : j.val < 18 then .sFull ⟨j.val - 16, by omega⟩
  else if _ : j.val < 20 then .pReady ⟨j.val - 18, by omega⟩
  else if _ : j.val < 22 then .pReady2 ⟨j.val - 20, by omega⟩
  else if _ : j.val < 24 then .spare 0 ⟨j.val - 22, by omega⟩
  else if _ : j.val < 26 then .oFull ⟨j.val - 24, by omega⟩
  else if _ : j.val < 28 then .spare 1 ⟨j.val - 26, by omega⟩
  else if _ : j.val < 30 then .spare 2 ⟨j.val - 28, by omega⟩
  else if _ : j.val < 32 then .stats ⟨j.val - 30, by omega⟩
  else if _ : j.val < 34 then .oStaged ⟨j.val - 32, by omega⟩
  else .oFree ⟨j.val - 34, by omega⟩

theorem off_ofInit : ∀ j : Fin 36, (ofInit j).off = 8 * j.val := by decide

theorem ofInit_ne_dealloc : ∀ j : Fin 36, ofInit j ≠ .dealloc := by decide

/-- Every barrier but the handshake is initialized by warp 0. -/
theorem exists_ofInit : ∀ b : FBar, b ≠ .dealloc → ∃ j, ofInit j = b := by decide

theorem off_inj : ∀ {b b' : FBar}, b.off = b'.off → b = b' := by
  intro b b'
  revert b b'
  decide

/-- The kernel's mbarrier table. -/
def table : BarTable FBar where
  Valid _ := True
  off := off
  count := count
  off_inj _ _ h := off_inj h
  count_valid {b} _ := by
    revert b
    simp only [MBarrier.validCount, MBarrier.limit]
    decide

/-- The barrier in CTA `cta`. -/
def loc (L : Launch) (cta : Nat) (b : FBar) : Loc := ⟨.shared, cta, L.sharedBase + b.off⟩

theorem loc_inj {L : Launch} {b b' : FBar} {c c' : Nat} (he : b.loc L c = b'.loc L c') :
    b = b' ∧ c = c' :=
  BarTable.loc_inj (T := table) trivial trivial he

end FBar

end PTX.Kernels.FlashAttn4Fwd.Proof
