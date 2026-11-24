-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # The kernel's mbarrier rings

Each ring has a number of slots, and each slot a full and an empty barrier (`Bar`), at a
fixed shared offset of every CTA. The tables below give, per barrier, what the protocols and
the thread facts need: its offset, its initial arrival count, its partner (the slot's other
barrier), the parity offset of its polls, and the bytes an arrival expects or a copy moves.
Adding a ring adds a `Ring` constructor and table entries. The slot counts (`Ring.slots`) are
the only bound on slot indices. The offsets and counts form the kernel's mbarrier table
(`Bar.table`), and CTA thread 0 initializes every barrier, at the event its offset gives
(`Bar.init`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

/-- The kernel's rings: the four-stage input ring, the two accumulator buffers, and the
cluster launch control response, whose empty barrier collects the ten acknowledgements. -/
inductive Ring where
  | input
  | acc
  | clc

/-- The number of slots of each ring. -/
def Ring.slots : Ring → Nat
  | .input => 4
  | .acc => 2
  | .clc => 1

/-- A ring barrier: its ring, its slot, and whether it is the slot's full barrier. -/
structure Bar where
  ring : Ring
  slot : Nat
  full : Bool

/-- A barrier of the kernel: its slot is one of its ring's slots. -/
def Bar.Valid (b : Bar) : Prop := b.slot < b.ring.slots

/-- The barrier's shared offset. -/
def Bar.off : Bar → Nat
  | ⟨.input, s, true⟩ => 8 + 8 * s
  | ⟨.input, s, false⟩ => 40 + 8 * s
  | ⟨.acc, j, true⟩ => 72 + 8 * j
  | ⟨.acc, j, false⟩ => 88 + 8 * j
  | ⟨.clc, s, true⟩ => 104 + 8 * s
  | ⟨.clc, s, false⟩ => 128 + 8 * s

/-- The arrival count the barrier is initialized with. -/
def Bar.count : Bar → Nat
  | ⟨.input, _, true⟩ => 1
  | ⟨.input, _, false⟩ => 2
  | ⟨.acc, _, true⟩ => 1
  | ⟨.acc, _, false⟩ => 256
  | ⟨.clc, _, true⟩ => 1
  | ⟨.clc, _, false⟩ => 10

/-- The bytes an arrival on the barrier expects. -/
def Bar.arriveTx : Bar → Nat
  | ⟨.input, _, true⟩ => 98304
  | ⟨.clc, _, true⟩ => 16
  | _ => 0

/-- Whether arrivals on the barrier land in the cluster's leader CTA (otherwise in the
arriving thread's own CTA). -/
def Bar.arriveLeader : Bar → Bool
  | ⟨.input, _, _⟩ => true
  | ⟨.acc, _, _⟩ => true
  | ⟨.clc, _, true⟩ => false
  | ⟨.clc, _, false⟩ => true

/-- The asynchronous operations (copies or cancellation requests) completing on the barrier
per successful poll of its partner. -/
def Bar.issues : Bar → Nat
  | ⟨.input, _, true⟩ => 3
  | ⟨.clc, _, true⟩ => 1
  | _ => 0

/-- The bytes one asynchronous operation completing on the barrier moves. -/
def Bar.completeBytes : Bar → Nat
  | ⟨.input, _, true⟩ => 16384
  | ⟨.clc, _, true⟩ => 16
  | _ => 0

/-- The shared offset of the response buffer that an asynchronous request completing on the
barrier writes (only CLC requests have one). -/
def Bar.responseOff : Bar → Nat
  | ⟨.input, _, _⟩ => 0
  | ⟨.acc, _, _⟩ => 0
  | ⟨.clc, _, true⟩ => 144
  | ⟨.clc, _, false⟩ => 0

/-- The slot's other barrier: a thread acts on a barrier after polling its partner. -/
def Bar.partner (b : Bar) : Bar := { b with full := !b.full }

/-- The barrier whose successful polls (in the arriving thread's CTA) gate an arrival on this
barrier: on the input and accumulator rings the slot's other barrier; on the CLC ring the
response barrier itself, whose consumers acknowledge each response they observed, and whose
scheduler expects the next response once it observed the previous one. -/
def Bar.gate : Bar → Bar
  | ⟨.input, s, true⟩ => ⟨.input, s, false⟩
  | ⟨.input, s, false⟩ => ⟨.input, s, true⟩
  | ⟨.acc, j, true⟩ => ⟨.acc, j, false⟩
  | ⟨.acc, j, false⟩ => ⟨.acc, j, true⟩
  | ⟨.clc, s, true⟩ => ⟨.clc, s, true⟩
  | ⟨.clc, s, false⟩ => ⟨.clc, s, true⟩

/-- How many more gate polls than earlier arrivals an arrival needs. -/
def Bar.gateSlack : Bar → Nat
  | ⟨.input, _, _⟩ => 1
  | ⟨.acc, _, _⟩ => 1
  | ⟨.clc, _, true⟩ => 0
  | ⟨.clc, _, false⟩ => 1

/-- A thread polls an empty barrier with the parity after its own successful polls on it, and a
full barrier with that parity. -/
def Bar.pollOffset (b : Bar) : Nat := if b.full then 0 else 1

/-- The index of the barrier's initialization among CTA thread 0's events. -/
def Bar.initIndex (b : Bar) : Nat := b.off / 8 + 1

/-- The barrier in CTA `cta`. -/
def Bar.loc (L : Launch) (cta : Nat) (b : Bar) : Loc := ⟨.shared, cta, L.sharedBase + b.off⟩

theorem Bar.off_range {b : Bar} (h : b.Valid) : 8 ≤ b.off ∧ b.off < 136 ∧ b.off % 8 = 0 := by
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at h
  cases r <;> cases f <;> simp only [Ring.slots] at h <;> simp only [Bar.off] <;> omega

theorem Bar.off_inj {b b' : Bar} (h : b.Valid) (h' : b'.Valid) (he : b.off = b'.off) : b = b' := by
  obtain ⟨r, s, f⟩ := b
  obtain ⟨r', s', f'⟩ := b'
  simp only [Bar.Valid] at h h'
  cases r <;> cases f <;> cases r' <;> cases f' <;> simp only [Ring.slots] at h h' <;>
    simp only [Bar.off] at he <;> first | (exfalso; omega) | (congr 1; omega)

/-- The kernel's mbarrier table. -/
def Bar.table : BarTable Bar where
  Valid := Bar.Valid
  off := Bar.off
  count := Bar.count
  off_inj := Bar.off_inj
  count_valid {b} _ := by
    obtain ⟨r, s, f⟩ := b
    cases r <;> cases f <;> simp [Bar.count, MBarrier.validCount, MBarrier.limit]

/-- The initializer map: barrier `b` of CTA `cta` is initialized by CTA thread 0, at the event
its offset gives. -/
def Bar.init (L : Launch) (b : Bar) (cta : Nat) : EvId := (cta * L.block, b.initIndex)

theorem Bar.loc_inj {L : Launch} {b b' : Bar} {c c' : Nat} (h : b.Valid) (h' : b'.Valid)
    (he : b.loc L c = b'.loc L c') : b = b' ∧ c = c' :=
  BarTable.loc_inj (T := Bar.table) h h' he

end PTX.Kernels.Fp16Gemm8192.Proof
