-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine

@[expose] public section

/-! # The CLC poll sites of the thread states

A thread state is at its CLC poll when its role is at its response wait: the loader's, the MMA
warps', the scheduler's or a consumer's. Its poll uses the phase `cp` of that state. Every role's
poll is the same fact (`clcWait_fire`): its barrier register holds the response barrier's address
and its phase register holds `cp`, so the poll waits on the response barrier with the phase bit of
`cp`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

/-- The CLC response barrier of thread `g`'s CTA. -/
abbrev clcResp (L : Launch) (g : Nat) : Loc := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩

/-- The acknowledgement barrier of the leader CTA of thread `g`'s cluster. -/
abbrev clcAck (L : Launch) (g : Nat) : Loc := Bar.loc L (2 * (g / L.block / 2)) ⟨.clc, 0, false⟩

theorem clcResp_loc (L : Launch) (g : Nat) :
    clcResp L g = ⟨.shared, g / L.block, L.sharedBase + 104⟩ := by
  simp [clcResp, Bar.loc, Bar.off]

/-- A phase bit is the parity of the truncated register that holds it. -/
theorem truncBits_phase {cp : Nat} (h : cp < 2) :
    (truncBits 32 (BitVec.ofNat 64 cp)).toNat % 2 = cp := by
  rcases (by omega : cp = 0 ∨ cp = 1) with rfl | rfl <;> decide

/-- The parity of a truncated phase register is the parity of its value. -/
theorem truncBits_parity (cp : Nat) :
    (truncBits 32 (BitVec.ofNat 64 cp)).toNat % 2 = cp % 2 := by
  have h1 : cp % 2 ^ 64 % 2 ^ 32 = cp % 2 ^ 32 :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num))
  have hlt : cp % 2 ^ 32 < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mod_lt cp (show 2 ^ 32 > 0 by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have h2 : cp % 2 ^ 32 % 2 ^ 64 = cp % 2 ^ 32 := Nat.mod_eq_of_lt hlt
  have h3 : cp % 2 ^ 32 % 2 = cp % 2 := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 1 ≤
    32))
  unfold truncBits
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1, h2, h3]

set_option maxHeartbeats 8000000 in
/-- A poll of the response barrier at a CLC poll site, whose barrier register holds the response
barrier's address and whose phase register holds `cp`, waits on the response barrier with the phase
bit of `cp`. -/
theorem clcWait_fire {P : Params} {L : Launch} {mem0 : Mem0} {g pc cp : Nat} {t : TState}
    {q base par : Nat} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hb : t.regs base = some (b32 (L.sharedBase + 104))) (hp : t.regs par = some (b32 cp))
    (hf : Fires pc (eventTmpl Prod L g t (.mbarWait q base 0 (.reg par) true .cta)) e o) :
    ∃ ok acq sc, e = ⟨pc, .wait (clcResp L g) ((truncBits 32 (BitVec.ofNat 64 cp)).toNat %
      2) ok acq sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega) (by omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg par) = .ok (truncBits 32 (BitVec.ofNat 64 cp)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  exact ⟨ok, acq, sc, by rw [he, clcResp_loc]⟩

/-- A thread state at its CLC poll site: its role's response wait. -/
def ThreadD.AtClcWait : ThreadD → Prop
  | .inl _ => False
  | .inr (.loader l) => l.site = .clcWait
  | .inr (.mma m) => m.site = .clcWait
  | .inr (.sched s) => s.site = .clcWait
  | .inr (.cons c) => c.site = .clcWait

/-- The response a thread state holds unacknowledged, by role: from its successful response poll to
its acknowledgement (the held count of its acknowledgement view). -/
def ThreadD.clcHeld : ThreadD → Nat
  | .inl _ => 0
  | .inr (.loader l) => match l.site with
    | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1
    | _ => 0
  | .inr (.mma m) => match m.site with
    | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1
    | _ => 0
  | .inr (.sched s) => match s.site with
    | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 1
    | _ => 0
  | .inr (.cons c) => match c.site with
    | .clcLoad | .clcStatus | .clcFirst | .clcFence | .clcBar | .ack => 1
    | _ => 0

/-- The phase of a thread state's CLC poll: the `cp` of its role. -/
def ThreadD.cpOf : ThreadD → Nat
  | .inl _ => 0
  | .inr (.loader l) => l.cp
  | .inr (.mma m) => m.cp
  | .inr (.sched s) => s.cp
  | .inr (.cons c) => c.cp

namespace Consumer

/-- Whether a consumer holds its accumulator: from its accumulator-full poll to its arrival. -/
def holds (d : D) : Nat := match d.site with
  | .load _ | .loadWait _ | .accArrive => 1
  | _ => 0

/-- Whether a consumer's task is open on the CLC response: from its response poll to its
accumulator arrival (the response the task is numbered by). -/
def tileOpen (d : D) : Nat := match d.site with
  | .clcLoad | .clcStatus | .clcFirst | .clcFence | .clcBar | .ack | .accWait | .load _ | .loadWait
    _
  | .accArrive => 1
  | _ => 0

end Consumer

end PTX.Kernels.Fp16Gemm8192.Proof

end
