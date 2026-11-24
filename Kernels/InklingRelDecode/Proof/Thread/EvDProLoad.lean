-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProSync

@[expose] public section

/-!
# Event shapes of the prologue: the global loads

The prologue reads the global arrays of the kernel with `ld.global`:

* `ldCu0`, `ldCu1`, `ldSk`: `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`;
* `lbSite i` (`i < 6`): the block-table words of the preloaded blocks, block `i / 2`, slab `i % 2`;
* `ldqSite k` (`k < 64`): the 16-bit elements of the rows of `Q`.

Each is a read event of a plain footprint at `loadAddr L g dt s`: the 64-bit word of the load's
address register (`gloadBase`, read from the instruction), for the thread's data `dt`. The word
loads read four bytes (`shape_ld32`), the query loads two (`shape_ldq`).

`ldCu0_addr`, `ldCu1_addr`, `ldSk_addr` give the three request words' addresses in `Spec`'s
terms, `cuBase + 4 req`, `cuBase + 4 (req + 1)`, `seqBase + 4 req`, modulo `2 ^ 64`. The block-table
and query addresses are the table's values: their closed forms (`btBase + 4 (req stride_bt + 2
(split + it num_splits) + e)`, and the element `(row, col)` each query load reads) are listed as
open in the development notes ("thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The 64-bit word the address register of the global load at site `s` holds. -/
def loadAddr (L : Launch) (g : Nat) (dt : Dat) (s : Site) : Nat :=
  match valueOf L g dt (gloadBase s.pc) with
  | .bits _ x => x.toNat
  | _ => 0

/-- The sites of the 32-bit loads: the request's three words, then the six block-table words. -/
def wordLoadSites : List Site := [.ldCu0, .ldCu1, .ldSk] ++ lbSites

theorem wordLoad_gload : ∀ s ∈ wordLoadSites, isGload s.pc 32 = true := by decide +kernel

theorem wordLoad_live : ∀ s ∈ wordLoadSites, gloadBase s.pc ∈ Flow.live s.pc := by
  decide +kernel

theorem wordLoad_sub : ∀ s ∈ wordLoadSites, s.sub = 0 := by decide +kernel

theorem ldq_gload : ∀ k < 64, isGload (ldqSite k).pc 16 = true := by decide +kernel

theorem ldq_live : ∀ k < 64, gloadBase (ldqSite k).pc ∈ Flow.live (ldqSite k).pc := by
  decide +kernel

theorem ldq_sub : ∀ k < 64, (ldqSite k).sub = 0 := by decide +kernel

theorem bits64_eq (x : BitVec 64) : Value.bits 64 x = b64 x.toNat := by
  unfold b64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- The address registers of the word loads and of the query loads hold 64-bit words. -/
theorem wordLoad_bits (L : Launch) (g : Nat) (dt : Dat) :
    ∀ s ∈ wordLoadSites, ∃ x, valueOf L g dt (gloadBase s.pc) = .bits 64 x := by
  intro s hs
  simp only [wordLoadSites, lbSites, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl⟩

theorem ldq_bits (L : Launch) (g : Nat) (dt : Dat) :
    ∀ k < 64, ∃ x, valueOf L g dt (gloadBase (ldqSite k).pc) = .bits 64 x := by
  intro k hk
  interval_cases k
  all_goals exact ⟨_, rfl⟩

/-- **A 32-bit load**: four bytes at `loadAddr`. -/
theorem shape_ld32 (hF : Fired L g d e (some u)) (hs : d.site ∈ wordLoadSites) :
    ∃ bs : List (Option Byte), bs.length = 4 ∧
      e = ⟨evPc d.site, .rd (wordAcc ⟨.global, 0, loadAddr L g d.dt d.site⟩) bs⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  obtain ⟨gd, hcode⟩ := isGload_spec (wordLoad_gload _ hs)
  have hins := Option.some.inj (hc.symm.trans hcode)
  have hop : ins.op = .mem (gload (gloadBase d.site.pc) (gloadDst d.site.pc) 32) :=
    congrArg Instr.op hins
  obtain ⟨x, hx⟩ := wordLoad_bits L g d.dt _ hs
  have hr : t.regs (gloadBase d.site.pc) = some (b64 x.toNat) := by
    rw [reg_at h (wordLoad_live _ hs), hx, bits64_eq]
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, wordLoad_sub _ hs] at h2
    exact h2
  have hxl : x.toNat < 2 ^ 64 := x.isLt
  obtain ⟨bs, hl, he⟩ := fires_ld_global hop hsub hr hxl (Or.inr rfl) hf
  have hA : loadAddr L g d.dt d.site = x.toNat := by simp [loadAddr, hx]
  exact ⟨bs, hl, by rw [he, hA]; rfl⟩

/-- **A query load**: two bytes at `loadAddr`. -/
theorem shape_ldq {k : Nat} (hk : k < 64) (hF : Fired L g d e (some u))
    (hs : d.site = ldqSite k) :
    ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨evPc d.site, .rd { loc := ⟨.global, 0, loadAddr L g d.dt d.site⟩, size := 2 } bs⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = (ldqSite k).pc := by rw [hs]
  obtain ⟨gd, hcode⟩ := isGload_spec (ldq_gload k hk)
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans hcode)
  have hop : ins.op = .mem (gload (gloadBase (ldqSite k).pc) (gloadDst (ldqSite k).pc) 16) :=
    congrArg Instr.op hins
  obtain ⟨x, hx⟩ := ldq_bits L g d.dt k hk
  have hr : t.regs (gloadBase (ldqSite k).pc) = some (b64 x.toNat) := by
    rw [reg_at h (by rw [hpc]; exact ldq_live k hk), hx, bits64_eq]
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, hs, ldq_sub k hk] at h2
    exact h2
  have hxl : x.toNat < 2 ^ 64 := x.isLt
  obtain ⟨bs, hl, he⟩ := fires_ld_global hop hsub hr hxl (Or.inl rfl) hf
  have hA : loadAddr L g d.dt d.site = x.toNat := by
    simp [loadAddr, hpc, hx]
  exact ⟨bs, hl, by rw [he, hA, evPc, hpc]⟩

/-! ### The three request words' addresses -/

theorem wMulWideU32_ofNat (a b : Nat) :
    wMulWideU32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 ((a % 2 ^ 32) * (b % 2 ^ 32)) := by
  unfold wMulWideU32
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]
  simp only [truncBits_ofNat _ _ (by omega : 32 ≤ 64), BitVec.toNat_ofNat]
  congr 1
  have h1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by
    have := Nat.mod_lt a (show 0 < 2 ^ 32 by decide); omega)
  have h2 : b % 2 ^ 32 % 2 ^ 64 = b % 2 ^ 32 := Nat.mod_eq_of_lt (by
    have := Nat.mod_lt b (show 0 < 2 ^ 32 by decide); omega)
  rw [h1, h2]

theorem wAdd64_ofNat (a b : Nat) :
    wAdd64 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 ((a + b) % 2 ^ 64) := by
  unfold wAdd64
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The register `%rd110 = ctaid.z * 4`. -/
theorem rd110_eq (L : Launch) (g : Nat) (dt : Dat) :
    v_rd110 L g dt = BitVec.ofNat 64 ((cta L g .z % 2 ^ 32) * 4) := by
  have l : BitVec.ofInt 64 4 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  simp only [v_rd110, v_r19, wCta_eq, l, wMulWideU32_ofNat, Nat.mod_mod]
  norm_num

/-- A 64-bit word read back as a 64-bit number. -/
theorem truncBits64_eq (x : BitVec 64) : truncBits 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- **The address of `cu_seqlens_q[req]`** is `cuBase + 4 req` modulo `2 ^ 64`, where the word
`x9` is the parameter `cu_seqlens_q`. -/
theorem ldCu0_addr (L : Launch) (g : Nat) (dt : Dat) :
    loadAddr L g dt .ldCu0 = (dt.pro.x9.toNat + (cta L g .z % 2 ^ 32) * 4) % 2 ^ 64 := by
  have h : valueOf L g dt (gloadBase Site.ldCu0.pc) = .bits 64 (v_rd107 L g dt) := rfl
  have h2 : v_rd107 L g dt = BitVec.ofNat 64 ((dt.pro.x9.toNat + (cta L g .z % 2 ^ 32) * 4) %
      2 ^ 64) := by
    simp only [v_rd107, v_rd74, rd110_eq, truncBits64_eq, wAdd64_ofNat]
  simp only [loadAddr, h, h2, BitVec.toNat_ofNat, Nat.mod_mod]

/-- **The address of `cu_seqlens_q[req + 1]`**. -/
theorem ldCu1_addr (L : Launch) (g : Nat) (dt : Dat) :
    loadAddr L g dt .ldCu1 = (dt.pro.x9.toNat + (cta L g .z % 2 ^ 32) * 4 + 4) % 2 ^ 64 := by
  have h : valueOf L g dt (gloadBase Site.ldCu1.pc) = .bits 64 (v_rd108 L g dt) := rfl
  have h2 : v_rd108 L g dt = BitVec.ofNat 64 ((dt.pro.x9.toNat + (cta L g .z % 2 ^ 32) * 4 + 4) %
      2 ^ 64) := by
    have l : BitVec.ofInt 64 4 = BitVec.ofNat 64 4 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    have h1 : v_rd107 L g dt = BitVec.ofNat 64 ((dt.pro.x9.toNat + (cta L g .z % 2 ^ 32) * 4) %
        2 ^ 64) := by
      simp only [v_rd107, v_rd74, rd110_eq, truncBits64_eq, wAdd64_ofNat]
    simp only [v_rd108, h1, l, wAdd64_ofNat]
    congr 1
    omega
  simp only [loadAddr, h, h2, BitVec.toNat_ofNat, Nat.mod_mod]

/-- **The address of `seq_lens[req]`**, where `x8` is the parameter `seq_lens`. -/
theorem ldSk_addr (L : Launch) (g : Nat) (dt : Dat) :
    loadAddr L g dt .ldSk = (dt.pro.x8.toNat + (cta L g .z % 2 ^ 32) * 4) % 2 ^ 64 := by
  have h : valueOf L g dt (gloadBase Site.ldSk.pc) = .bits 64 (v_rd109 L g dt) := rfl
  have h2 : v_rd109 L g dt = BitVec.ofNat 64 ((dt.pro.x8.toNat + (cta L g .z % 2 ^ 32) * 4) %
      2 ^ 64) := by
    simp only [v_rd109, v_rd73, rd110_eq, truncBits64_eq, wAdd64_ofNat]
  simp only [loadAddr, h, h2, BitVec.toNat_ofNat, Nat.mod_mod]

variable {P : Params} {mem0 : Mem0}

/-- The three request words are read from `cuBase + 4 req`, `cuBase + 4 (req + 1)` and
`seqBase + 4 req` of the thread's request `req = ctaid.z` (modulo `2 ^ 64`: `Pre` gives no bound
on the input pointers, so a layer above needs the no-wrap-around fact to equate these with
`Params.reads`). -/
theorem cu_addrs (hpre : Pre P L mem0) (hg : g < L.threads) {dt : Dat}
    (ha : ArgsOk L g dt.pro) :
    loadAddr L g dt .ldCu0 = (P.cuBase + 4 * cta L g .z) % 2 ^ 64 ∧
    loadAddr L g dt .ldCu1 = (P.cuBase + 4 * (cta L g .z + 1)) % 2 ^ 64 ∧
    loadAddr L g dt .ldSk = (P.seqBase + 4 * cta L g .z) % 2 ^ 64 := by
  have hz := (cta_lt hpre hg).2.2
  have hb := hpre.bRange
  have h9 : dt.pro.x9 = BitVec.ofNat 64 P.cuBase :=
    Option.some.inj (ha.p9.symm.trans hpre.paramCu)
  have h8 : dt.pro.x8 = BitVec.ofNat 64 P.seqBase :=
    Option.some.inj (ha.p8.symm.trans hpre.paramSeq)
  have e9 : dt.pro.x9.toNat = P.cuBase % 2 ^ 64 := by rw [h9, BitVec.toNat_ofNat]
  have e8 : dt.pro.x8.toNat = P.seqBase % 2 ^ 64 := by rw [h8, BitVec.toNat_ofNat]
  have hz' : cta L g .z % 2 ^ 32 = cta L g .z := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [ldCu0_addr, e9, hz']
    omega
  · rw [ldCu1_addr, e9, hz']
    omega
  · rw [ldSk_addr, e8, hz']
    omega

/-- **The three request-word loads, in the specification's terms**: four bytes at
`cuBase + 4 req`, `cuBase + 4 (req + 1)`, `seqBase + 4 req`. -/
theorem shape_cu (hpre : Pre P L mem0) (hg : g < L.threads) (hF : Fired L g d e (some u))
    (hs : d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk) :
    ∃ bs : List (Option Byte), bs.length = 4 ∧
      e = ⟨evPc d.site, .rd (wordAcc ⟨.global, 0,
        if d.site = .ldCu0 then (P.cuBase + 4 * cta L g .z) % 2 ^ 64
        else if d.site = .ldCu1 then (P.cuBase + 4 * (cta L g .z + 1)) % 2 ^ 64
        else (P.seqBase + 4 * cta L g .z) % 2 ^ 64⟩) bs⟩ := by
  have hm : d.site ∈ wordLoadSites := by
    rcases hs with hs | hs | hs <;> rw [hs] <;> simp [wordLoadSites]
  obtain ⟨bs, hl, he⟩ := shape_ld32 hF hm
  obtain ⟨t, -, hi, -⟩ := hF
  obtain ⟨h0, h1, h2⟩ := cu_addrs hpre hg hi.args
  refine ⟨bs, hl, ?_⟩
  rw [he]
  rcases hs with hs | hs | hs
  · simp only [hs, ite_true]
    rw [h0]
  · simp only [hs, reduceCtorEq, ite_false, ite_true]
    rw [h1]
  · simp only [hs, reduceCtorEq, ite_false]
    rw [h2]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
