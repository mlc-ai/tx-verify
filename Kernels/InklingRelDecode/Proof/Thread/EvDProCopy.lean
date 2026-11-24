-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProStore

@[expose] public section

/-!
# Event shapes of the prologue: the K/V tensor copies

The prologue issues up to three K/V blocks. Block `j` is staged in ring slot `j` by four tile
copies of the `kv_rows` map (`ptcSite (4 j + c)`: K slab 0, V slab 0, K slab 1, V slab 1), each
by an elected lane of warps 0 and 1, all completing on `kv_ready j`. `shape_ptc` says what each
copy is:

* one tensor issue, a tile load with no cluster addressing, one CTA group, no row coordinates;
* completing on the barrier `kv_ready (i / 4)` of the thread's own CTA (`EvD.Bar.loc`);
* to the shared address `copyDst`, with the box origin `(copyX, copyY)` (signed 32-bit
  coordinates), the words the copy's destination and coordinate registers hold;
* of the map the launch publishes: `L.tensorMaps a = some ⟨s.outer, desc⟩`, `s.descriptor = desc`.

Their closed forms (`sharedBase + 32768 j + 98304 [V] + 8192 [slab 1] + 16384 (warp % 2)`, and
the origin `(head_cols · kvh + 64 (warp % 2) + 128 [V], block_table[…] · page_rows + head_rows ·
kvh)`), and that the map address `a` is the address of `kv_desc` (`Pre.paramKv`, which needs the
tensor-map register of the common code), are open (the development notes, "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The destination register of the tensor copy at `pc`. -/
def ptcDst (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor _ _ dst _ _ _ _ _ _ _ _⟩ => dst
  | _ => 0

/-- The mbarrier register of the tensor copy at `pc`. -/
def ptcMb (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor _ _ _ _ _ _ mb _ _ _ _⟩ => mb
  | _ => 0

/-- Coordinate register `k` of the tensor copy at `pc`. -/
def ptcCoord (pc k : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor _ _ _ _ _ cs _ _ _ _ _⟩ =>
    match cs[k]? with
    | some (.reg r) => r
    | _ => 0
  | _ => 0

/-- The instruction at `pc` is a guarded tile `cp.async.bulk.tensor.2d.shared::cta` with two
coordinate registers and no multicast or cache policy. -/
def isPtc (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (_, false), .cpTensor ca grp _ off _ cs _ moff mc lm pol⟩ =>
    !ca && !grp && off == 0 && moff == 0 && mc.isNone && decide (lm = .tile) && pol.isNone &&
      decide (cs = [.reg (ptcCoord pc 0), .reg (ptcCoord pc 1)])
  | _ => false

theorem isPtc_spec {pc : Nat} (h : isPtc pc = true) :
    ∃ p map, kernel.code[pc]? = some ⟨some (p, false), .cpTensor false false (ptcDst pc) 0 map
      [.reg (ptcCoord pc 0), .reg (ptcCoord pc 1)] (ptcMb pc) 0 none .tile none⟩ := by
  unfold isPtc at h
  split at h
  · rename_i p ca grp dst off map cs mb moff mc lm pol hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hca, hgrp⟩, hoff⟩, hmoff⟩, hmc⟩, hlm⟩, hpol⟩, hcs⟩ := h
    subst hca hgrp hoff hmoff hmc hlm hpol hcs
    have e1 : ptcDst pc = dst := by simp [ptcDst, hc]
    have e2 : ptcMb pc = mb := by simp [ptcMb, hc]
    rw [e1, e2]
    exact ⟨p, map, hc⟩
  · cases h

theorem ptc_isPtc : ∀ i < 12, isPtc (ptcSite i).pc = true := by decide +kernel

theorem ptc_mb : ∀ i < 12, ptcMb (ptcSite i).pc = 613 + 2 * (i / 4) := by decide +kernel

theorem ptc_live : ∀ i < 12, ptcDst (ptcSite i).pc ∈ Flow.live (ptcSite i).pc ∧
    ptcCoord (ptcSite i).pc 0 ∈ Flow.live (ptcSite i).pc ∧
    ptcCoord (ptcSite i).pc 1 ∈ Flow.live (ptcSite i).pc ∧
    ptcMb (ptcSite i).pc ∈ Flow.live (ptcSite i).pc := by decide +kernel

/-- The 32-bit word a value holds. -/
def wordOf : Value → Nat
  | .bits _ x => x.toNat
  | _ => 0

/-- The shared destination word, and the two coordinate words, of copy `i`. -/
def copyDst (L : Launch) (g : Nat) (dt : Dat) (i : Nat) : Nat :=
  wordOf (valueOf L g dt (ptcDst (ptcSite i).pc))
def copyX (L : Launch) (g : Nat) (dt : Dat) (i : Nat) : Nat :=
  wordOf (valueOf L g dt (ptcCoord (ptcSite i).pc 0))
def copyY (L : Launch) (g : Nat) (dt : Dat) (i : Nat) : Nat :=
  wordOf (valueOf L g dt (ptcCoord (ptcSite i).pc 1))

theorem truncBits_lt (w : Nat) (x : BitVec 64) (hw : w ≤ 64) : (truncBits w x).toNat < 2 ^ w := by
  unfold truncBits
  rw [BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ w by positivity)
  have h2 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
  rw [Nat.mod_eq_of_lt (by omega)]
  exact h1

theorem ptc_bits (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 12, (∃ x : BitVec 64, valueOf L g dt (ptcDst (ptcSite i).pc) = .bits 32 x ∧
        x.toNat < 2 ^ 32) ∧
      (∃ x : BitVec 64, valueOf L g dt (ptcCoord (ptcSite i).pc 0) = .bits 32 x ∧
        x.toNat < 2 ^ 32) ∧
      (∃ x : BitVec 64, valueOf L g dt (ptcCoord (ptcSite i).pc 1) = .bits 32 x ∧
        x.toNat < 2 ^ 32) := by
  intro i hi
  interval_cases i
  all_goals exact ⟨⟨_, rfl, truncBits_lt 32 _ (by omega)⟩, ⟨_, rfl, truncBits_lt 32 _ (by omega)⟩,
    ⟨_, rfl, truncBits_lt 32 _ (by omega)⟩⟩

theorem bits32_eq (x : BitVec 64) (h : x.toNat < 2 ^ 32) : Value.bits 32 x = b32 x.toNat := by
  unfold b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ptc_initBar (i : Nat) (hi : i < 12) : initBar (2 * (i / 4)) = kvReadyOf (i / 4) := by
  have h : i / 4 < 3 := by omega
  rw [initBar_arr _ h]

/-- **A K/V tensor copy of the prologue**: a tile load of the published map, one CTA group, no
cluster addressing, completing on `kv_ready (i / 4)` of the thread's CTA, to the shared address
`copyDst` with the box origin `(copyX, copyY)`. -/
theorem shape_ptc (hS : SharedOk L) {i : Nat} (hi : i < 12) (hF : Fired L g d e (some u))
    (hs : d.site = ptcSite i) :
    ∃ a s, e = ⟨evPc d.site, .tensorIssue a s⟩ ∧ s.clusterAddress = false ∧ s.group = .one ∧
      s.mbar = (kvReadyOf (i / 4)).loc L (g / L.block) ∧
      s.sharedBase = ⟨.shared, g / L.block, copyDst L g d.dt i⟩ ∧ s.rows = none ∧
      (∀ ax : Fin (s.outer + 1), s.origin ax =
        (BitVec.ofNat 32 ([copyX L g d.dt i, copyY L g d.dt i].getD ax.val 0)).toInt) ∧
      ∃ desc, L.tensorMaps a = some ⟨s.outer, desc⟩ ∧ s.descriptor = desc := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = (ptcSite i).pc := by rw [hs]
  obtain ⟨p, map, hcode⟩ := isPtc_spec (ptc_isPtc i hi)
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans hcode)
  have hop : ins.op = .cpTensor false false (ptcDst (ptcSite i).pc) 0 map
      [.reg (ptcCoord (ptcSite i).pc 0), .reg (ptcCoord (ptcSite i).pc 1)]
      (ptcMb (ptcSite i).pc) 0 none .tile none := congrArg Instr.op hins
  rw [hop] at hf
  obtain ⟨⟨xd, hxd, hxdl⟩, ⟨xx, hxx, hxxl⟩, ⟨xy, hxy, hxyl⟩⟩ := ptc_bits L g d.dt i hi
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptc_live i hi
  have hr1 : t.regs (ptcDst (ptcSite i).pc) = some (b32 xd.toNat) := by
    rw [reg_at h (by rw [hpc]; exact hl1), hxd, bits32_eq xd hxdl]
  have hr2 : t.regs (ptcCoord (ptcSite i).pc 0) = some (b32 xx.toNat) := by
    rw [reg_at h (by rw [hpc]; exact hl2), hxx, bits32_eq xx hxxl]
  have hr3 : t.regs (ptcCoord (ptcSite i).pc 1) = some (b32 xy.toNat) := by
    rw [reg_at h (by rw [hpc]; exact hl3), hxy, bits32_eq xy hxyl]
  have hr4 : t.regs (ptcMb (ptcSite i).pc) =
      some (b32 ((L.sharedBase + (kvReadyOf (i / 4)).off) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; exact hl4), ptc_mb i hi]
    have := val_init L g d.dt (2 * (i / 4)) (by omega)
    rw [this, ptc_initBar i hi]
  have hmod : (L.sharedBase + (kvReadyOf (i / 4)).off) % 2 ^ 32 =
      L.sharedBase + (kvReadyOf (i / 4)).off := by
    apply Nat.mod_eq_of_lt
    have := hS.2
    have hlt : (kvReadyOf (i / 4)).off + 8 ≤ 213340 := Bar.off_lt _
    omega
  obtain ⟨a, s, he, hca, hgrp, hmb, hsh, hrows, horig, desc, hmap, hdesc⟩ :=
    fires_cpTensor_tile hr1 hxdl hr2 hxxl hr3 hxyl hr4 (Nat.mod_lt _ (by decide)) hf
  have hcd : copyDst L g d.dt i = xd.toNat := by simp [copyDst, wordOf, hxd]
  have hcx : copyX L g d.dt i = xx.toNat := by simp [copyX, wordOf, hxx]
  have hcy : copyY L g d.dt i = xy.toNat := by simp [copyY, wordOf, hxy]
  refine ⟨a, s, ?_, hca, hgrp, ?_, ?_, hrows, ?_, desc, hmap, hdesc⟩
  · rw [he, evPc, hpc]
  · rw [hmb, hmod]; rfl
  · rw [hsh, hcd]
  · intro ax
    rw [horig ax, hcx, hcy]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
