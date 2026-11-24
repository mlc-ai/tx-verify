-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads

@[expose] public section

/-! # What the scheduler reads

Every read of the scheduler (the scan's, the chosen request's two) at a state that holds the
reference values reads a cumulative query offset of the batch (`sched_rd`); the used-K word of the
chosen request is a word of the batch (`usedK_addr`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ns nv : Nat}

/-- **The read of a scan round reads the lane's request.** -/
theorem word_addr (hp : Pre p L m) {k' : Scan} {d : D} (hs : d.site = .word k')
    (hF : Fits p L g d ns nv) : ∃ i ≤ p.batch, (rdAddr p L g d).toNat = p.cuQBase + 4 * i := by
  simp only [Fits, hs] at hF
  obtain ⟨r, -, -, -, hR, -, -, hL, hrd⟩ := hF
  exact ⟨_, reqN_le hp (Nat.mod_lt _ (by decide)) hrd, rdAddr_eq hp hs hR hL hrd⟩

/-- **The chosen request's two reads** read its two cumulative offsets. -/
theorem q_addr (hp : Pre p L m) {d : D} (hs : d.site = .q0 ∨ d.site = .q1)
    (hF : Fits p L g d ns nv) : ∃ i ≤ p.batch, (rdAddr p L g d).toNat = p.cuQBase + 4 * i := by
  obtain ⟨R, bal, hC⟩ : ∃ R bal, ChosenVals p L g R bal d ns nv := by
    rcases hs with hs | hs <;> simp only [Fits, hs] at hF
    · exact hF
    · obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩
  obtain ⟨i, hi, hib⟩ := chosen_W hp hC
  rcases hs with hs | hs
  · refine ⟨i, by omega, ?_⟩
    simp only [rdAddr, hs, hi]
    exact addrS_toNat0 hp (by omega)
  · refine ⟨i + 1, hib, ?_⟩
    simp only [rdAddr, hs, hi]
    exact addrS_toNat4 hp hib

/-- **Every read of the scheduler reads a cumulative query offset.** -/
theorem sched_rd (hp : Pre p L m) {d : D} (hF : Fits p L g d ns nv) {e : Event}
    (hev : Ev p L g d e) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    InWord p a := by
  have key : (∃ i ≤ p.batch, (rdAddr p L g d).toNat = p.cuQBase + 4 * i) →
      ((∃ bs, e.kind = .rd (wordAcc (rdAddr p L g d).toNat) bs) ∨ ∃ f, e.kind = .ub f) →
      InWord p a := by
    rintro ⟨i, hi, ha⟩ (⟨bs', hk'⟩ | ⟨f, hk'⟩)
    · rw [hk, Kind.rd.injEq] at hk'
      rw [hk'.1, ha]
      exact ⟨rfl, .inl ⟨i, hi, rfl⟩⟩
    · rw [hk] at hk'; cases hk'
  cases hs : d.site <;> simp only [Ev, hs] at hev
  case word k' => exact key (word_addr hp hs hF) hev
  case q0 => exact key (q_addr hp (.inl hs) hF) hev
  case q1 => exact key (q_addr hp (.inr hs) hF) hev
  case store => unfold isStore at hev; rw [hk] at hev; simp at hev
  case start => obtain ⟨_, _, _, h⟩ := hev; rw [hk] at h; cases h
  case ready => obtain ⟨_, h⟩ := hev; rw [hk] at h; cases h
  case vote => obtain ⟨_, h⟩ := hev; rw [hk] at h; cases h
  case down | up | total | pre | tiles => obtain ⟨_, _, h⟩ := hev; rw [hk] at h; cases h
  all_goals rw [hk] at hev; cases hev

/-- **The used-K word of the chosen request.** -/
theorem usedK_addr (hp : Pre p L m) {d : D} {R : Nat} {bal : BitVec 64}
    (hC : ChosenVals p L g R bal d ns nv) : ∃ i < p.batch,
      (truncBits 64 (vbits (addrS p.usedKBase (chosen d))) + BitVec.ofInt 64 0).toNat =
        p.usedKBase + 4 * i := by
  have hb := batch_lt hp
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  obtain ⟨i, hi, hib⟩ := chosen_W hp hC
  refine ⟨i, by omega, ?_⟩
  rw [hi]
  have hs : toSigned 32 (r32 (W i)) = i := by
    rw [r32_W (by omega)]; exact toSigned_W (by omega)
  have h4 : toSigned 32 (i32 4) = 4 := by decide
  simp only [vbits, hs, h4]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt, Nat.reducePow]
  omega

/-- A read of the used-K word. -/
theorem usedK_rd {a : Acc} {bs bs' : List (Option Byte)} {x : BitVec 64} {kd : Kind}
    (hk : kd = .rd a bs) (hk' : kd = .rd (wordAcc x.toNat) bs')
    (hx : ∃ i < p.batch, x.toNat = p.usedKBase + 4 * i) : InWord p a := by
  rw [hk, Kind.rd.injEq] at hk'
  obtain ⟨i, hi, hx⟩ := hx
  rw [hk'.1, hx]
  exact ⟨rfl, .inr (.inl ⟨i, hi, rfl⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
