-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Sites
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Isa.Tmpl
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # `tc_gemm`: the template of each site

With the registers its site's facts give, the instruction of each site performs: the allocation
request, continuing on lane 0 into the store of the address, the two mbarrier initializations,
the proxy fence, the arrival expecting 4352 bytes, the two bulk copies, the CTA barriers, the read
of the address, the polls of `bar0` and `bar1`, the MMA and its commit, the Tensor Core fences,
the load of the row and its wait, the element stores of the row (undefined behaviour for a word
that is not four bytes), the deallocation and the exit. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

/-- The load at program counter 23: the address of the Tensor Memory columns, read from `tslot`. -/
@[reducible] def loadSlotAcc : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
    addr := ⟨.reg 11 32, 0⟩, dsts := [some 14] }

/-- The stores at program counters 52 and 53: four registers of the row at byte offset `off`. -/
@[reducible] def storeQuadAcc (off : Int) (srcs : List Opnd) : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, elem := .int .b 32, vec := 4,
    addr := ⟨.reg 47 64, off⟩, srcs }

/-- The load of the slot as an instruction. -/
@[reducible] def loadSlot : Op := .mem loadSlotAcc

/-- The store of four registers of the row as an instruction. -/
@[reducible] def storeQuad (off : Int) (srcs : List Opnd) : Op := .mem (storeQuadAcc off srcs)

/-- The first four elements of the row. -/
@[reducible] def storeLo : Op := storeQuad 0 [.reg 22, .reg 23, .reg 24, .reg 25]

/-- The last four elements of the row. -/
@[reducible] def storeHi : Op := storeQuad 16 [.reg 26, .reg 27, .reg 28, .reg 29]

theorem eventTmpl_loadSlot (A : List Assumption) (L : Launch) (g : Nat) (t : TState) :
    eventTmpl A L g t loadSlot = loadTmpl A L g t .shared false 32 [14] 11 0 :=
  memTmpl_load (a := loadSlotAcc) (sp := .shared) (base := 11) (w := 32) (by rfl) (by rfl)
    (by rfl) (by rfl) (by simp)

theorem eventTmpl_storeQuad (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (off : Int)
    (srcs : List Opnd) (h : srcs.length = 4) :
    eventTmpl A L g t (storeQuad off srcs) = storeTmpl L g t .global 32 47 off srcs := by
  have hr : (storeQuadAcc off srcs).rule = some .threadAccess := by
    simp [MemAccess.rule, memTypeOk,
      DType.width, h]
  exact memTmpl_store (A := A) (a := storeQuadAcc off srcs) (sp := .global) (base := 47) (w := 64)
    hr (by rfl) (by rfl) (by rfl) (by simp)

/-- Reduce a lookup of the value table. -/
macro "tc_values" : tactic =>
  `(tactic| simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- The facts of the registers `live`, valued at `d`. -/
abbrev factsOn (L : Launch) (A B D g : Nat) (d : ThreadD) (live : List Nat) :
    List (Nat × Value) :=
  Flow.factsFrom live (valueOf L A B D g d)

/-- The kernel's three parameters. -/
def ps (A B D : Nat) : List (String × Nat) :=
  [("tc_gemm_param_0", A), ("tc_gemm_param_1", B), ("tc_gemm_param_2", D)]

theorem params (hpre : Pre L A B D a b mem0) : explicitParams L (ps A B D) = L :=
  explicitParams_eq (by
    intro p v hm
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hpre.param0, hpre.param1, hpre.param2])

/-- A live register of a state holds its table value. -/
theorem reg_at {d : ThreadD} {t : TState} {r : Nat} (h : Holds t.regs (facts L A B D g d))
    (hl : r ∈ liveAt d.site) : t.regs r = some (valueOf L A B D g d r) :=
  holds_mem h (Flow.mem_factsFrom hl)

/-- The value of a live register from the facts `h`. -/
macro "tc_reg " h:term:max : term => `(by rw [reg_at $h (by table_decide)]; tc_values)

section
variable (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {t : TState}
include hpre hg

/-- The allocation request of warp 0; lane 0 stays at the instruction for the address store. -/
theorem tmpl_alloc (hw : g / 32 = 0) (h11 : t.regs 11 = some (b32 (L.sharedBase + 4368)))
    (hs : t.sub = 0) :
    eventTmpl [] L g t (.tcAlloc .one 11 0 (.imm 32)) =
      .tc (.resource .one (some (tslot L.sharedBase)) (.alloc 32))
        (if g = 0 then { t with sub := 1 } else PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hb := hpre.block
  have hc := cta_zero hpre (lt_block hpre hg)
  show tcTmpl L g t (.tcAlloc .one 11 0 (.imm 32)) = _
  rw [tc_alloc (by rw [hb]) h11 (by omega) (by omega) hs]
  have hl : laneOf L g = g := by simp only [laneOf, hb]; omega
  simp [hl, hc, tslot]

/-- Lane 0's store of the address. -/
theorem tmpl_allocSt (h11 : t.regs 11 = some (b32 (L.sharedBase + 4368))) (hs : t.sub = 1) :
    eventTmpl [] L g t (.tcAlloc .one 11 0 (.imm 32)) =
      .tcAllocStore (tslot L.sharedBase) { t with pc := t.pc + 1, sub := 0 } := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hb := hpre.block
  have hc := cta_zero hpre (lt_block hpre hg)
  show tcTmpl L g t (.tcAlloc .one 11 0 (.imm 32)) = _
  rw [tc_allocWrite (by rw [hb]) h11 (by omega) (by omega) hs]
  simp [hc, tslot]

theorem tmpl_init0 (h9 : t.regs 9 = some (b32 (L.sharedBase + 4352))) :
    eventTmpl [] L g t (.mbarInit 9 0 (.imm 1)) = .mbInit (bar0 L.sharedBase) 1 (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  show widenMbarScope [] t.pc (tmaTmpl L g t (.mbarInit 9 0 (.imm ((1 : Nat) : Int)))) = _
  rw
    [tma_mbarInit h9 (by omega) (by omega) (by decide) (by decide), cta_zero hpre (lt_block hpre
    hg)]
  rfl

theorem tmpl_init1 (h10 : t.regs 10 = some (b32 (L.sharedBase + 4360))) :
    eventTmpl [] L g t (.mbarInit 10 0 (.imm 1)) = .mbInit (bar1 L.sharedBase) 1 (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  show widenMbarScope [] t.pc (tmaTmpl L g t (.mbarInit 10 0 (.imm ((1 : Nat) : Int)))) = _
  rw
    [tma_mbarInit h10 (by omega) (by omega) (by decide) (by decide), cta_zero hpre (lt_block hpre
    hg)]
  rfl

theorem tmpl_arrive (h9 : t.regs 9 = some (b32 (L.sharedBase + 4352))) :
    eventTmpl [] L g t (.mbarArrive 9 0 (.imm 4352)) =
      .arrive (bar0 L.sharedBase) 4352 (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  show widenMbarScope [] t.pc (tmaTmpl L g t (.mbarArrive 9 0 (.imm ((4352 : Nat) : Int)))) = _
  rw [tma_arrive h9 (by omega) (by omega) (by decide), cta_zero hpre (lt_block hpre hg)]
  rfl

theorem tmpl_bulkA (h12 : t.regs 12 = some (b32 L.sharedBase)) (h39 : t.regs 39 = some (b64 A))
    (h9 : t.regs 9 = some (b32 (L.sharedBase + 4352))) :
    eventTmpl [] L g t (.cpBulk (BulkCopy.mk .globalToCta 12 0 39 0 (.imm 4096) (some (9, 0)) none
      none none none none none)) =
      .copy (bulkSpec { loc := gA A, size := 4096 } { loc := sA L.sharedBase, size := 4096 }
        (.mbarrier (bar0 L.sharedBase)) .whole none) (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hrA := hpre.rangeA
  show widenMbarScope [] t.pc (tmaTmpl L g t (.cpBulk (BulkCopy.mk .globalToCta 12 0 39 0
    (.imm ((4096 : Nat) : Int)) (some (9, 0)) none none none none none none))) = _
  rw [tma_cpBulk h12 (by omega) h39 (by omega) h9 (by omega) (by omega) (by decide) (by decide)
    (by decide) (by omega) hpre.alignA, cta_zero hpre (lt_block hpre hg)]
  all_goals first
    | (simp only [bulkRangeOk, bulkSpaceEnd]; omega)
    | rfl

theorem tmpl_bulkB (h13 : t.regs 13 = some (b32 (L.sharedBase + 4096)))
    (h40 : t.regs 40 = some (b64 B)) (h9 : t.regs 9 = some (b32 (L.sharedBase + 4352))) :
    eventTmpl [] L g t (.cpBulk (BulkCopy.mk .globalToCta 13 0 40 0 (.imm 256) (some (9, 0)) none
      none none none none none)) =
      .copy (bulkSpec { loc := gB B, size := 256 } { loc := sB L.sharedBase, size := 256 }
        (.mbarrier (bar0 L.sharedBase)) .whole none) (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hrB := hpre.rangeB
  show widenMbarScope [] t.pc (tmaTmpl L g t (.cpBulk (BulkCopy.mk .globalToCta 13 0 40 0
    (.imm ((256 : Nat) : Int)) (some (9, 0)) none none none none none none))) = _
  rw [tma_cpBulk h13 (by omega) h40 (by omega) h9 (by omega) (by omega) (by decide) (by decide)
    (by decide) (by omega) hpre.alignB, cta_zero hpre (lt_block hpre hg)]
  all_goals first
    | (simp only [bulkRangeOk, bulkSpaceEnd]; omega)
    | rfl

theorem tmpl_load (h11 : t.regs 11 = some (b32 (L.sharedBase + 4368))) (hs : t.sub = 0) :
    eventTmpl [] L g t loadSlot =
      .read { loc := tslot L.sharedBase, size := 4 } (afterLoad t [14]) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  rw [eventTmpl_loadSlot, loadTmpl_shared hs h11 (by omega) (by decide) (by omega),
    cta_zero hpre (lt_block hpre hg)]
  rfl

theorem tmpl_wait0 (h9 : t.regs 9 = some (b32 (L.sharedBase + 4352))) :
    eventTmpl [] L g t (.mbarWait 3 9 0 (.imm 0)) =
      .wait (bar0 L.sharedBase) 0 (fun ok => PTX.next (setReg t 3 (.pred ok))) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  show widenMbarScope [] t.pc (tmaTmpl L g t (.mbarWait 3 9 0 (.imm 0))) = _
  rw [tma_tryWait h9 (by omega) (by omega), cta_zero hpre (lt_block hpre hg)]
  rfl

theorem tmpl_wait1 (h10 : t.regs 10 = some (b32 (L.sharedBase + 4360))) :
    eventTmpl [] L g t (.mbarWait 5 10 0 (.imm 0)) =
      .wait (bar1 L.sharedBase) 0 (fun ok => PTX.next (setReg t 5 (.pred ok))) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  show widenMbarScope [] t.pc (tmaTmpl L g t (.mbarWait 5 10 0 (.imm 0))) = _
  rw [tma_tryWait h10 (by omega) (by omega), cta_zero hpre (lt_block hpre hg)]
  rfl

omit hpre hg in
/-- The descriptor of `A` as the kernel computes it. -/
theorem decode_descA (hS : L.sharedBase + 4372 ≤ 2 ^ 18) (hA : L.sharedBase % 128 = 0) :
    TcShared.decode (L.sharedBase / 16 + 524288 + 70437463654400) = some (descA L.sharedBase) := by
  rw [sharedDecode_canon (s := L.sharedBase / 16) (by omega) rfl]
  simp only [descA, Option.some.injEq, TcShared.Descriptor.mk.injEq, and_true]
  omega

omit hpre hg in
theorem decode_descB (hS : L.sharedBase + 4372 ≤ 2 ^ 18) (hA : L.sharedBase % 128 = 0) :
    TcShared.decode ((L.sharedBase + 4096) / 16 + 524288 + 70437463654400) =
      some (descB L.sharedBase) := by
  rw [sharedDecode_canon (s := (L.sharedBase + 4096) / 16) (by omega) rfl]
  simp only [descB, Option.some.injEq, TcShared.Descriptor.mk.injEq, and_true]
  omega

theorem tmpl_mma {c : Nat} (hc : c < 2 ^ 16) (h14 : t.regs 14 = some (b32 c))
    (h42 : t.regs 42 = some (b64 (L.sharedBase / 16 + 524288 + 70437463654400)))
    (h44 : t.regs 44 = some (b64 ((L.sharedBase + 4096) / 16 + 524288 + 70437463654400)))
    (h19 : t.regs 19 = some (b32 134349984)) (h30 : t.regs 30 = some (b32 0))
    (h4 : t.regs 4 = some (.pred false)) :
    eventTmpl [] L g t (.tcMma (.dense .one false .i8 14 (.smem (.reg 42)) (.reg 44) (.reg 19)
      [.reg 30, .reg 30, .reg 30, .reg 30] (.reg 4))) =
      .tc (.mma c (mmaSpec L.sharedBase) false mmaMask) (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hcs := clusterSize_eq hpre
  have h24 : readBits L g t 32 (.reg 30) = .ok (BitVec.ofNat 64 0) :=
    readBits_b32 h30 (by decide)
  have hs : TcMma.makeOperands L (g / L.block) mmaDesc (descA L.sharedBase)
      (descB L.sharedBase) = some (mmaSpec L.sharedBase) := by
    have hcg : L.ctaGroup 0 .one = some [0] := by
      have hr := Launch.oneDim_rankOfCta hpre.oneDimLaunch.1 0
      have hsz := Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1 0
      have hco := Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1 0
      simp [Launch.ctaGroup_one, Launch.peerCta, Launch.clusterStart, hcs, hr, hsz, hco,
        hpre.grid]
    have hz : g / L.block = 0 := cta_zero hpre (lt_block hpre hg)
    rw [hz]
    simp [TcMma.makeOperands, mmaDesc, mmaSpec, hcg]
  show tcTmpl L g t (.tcMma (.dense .one false .i8 14 (.smem (.reg 42)) (.reg 44) (.reg 19)
    [.reg 30, .reg 30, .reg 30, .reg 30] (.reg 4))) = _
  rw [tc_mma (ms := List.replicate 4 (BitVec.ofNat 64 0)) hg h14 (by omega) h42 (by omega) h44
    (by omega) h19 (by decide) (by simp [List.mapM_cons, h24]; rfl) rfl h4
    (decode_descA hS hA) (decode_descB hS hA) rfl hs]
  rfl

theorem tmpl_commit (h10 : t.regs 10 = some (b32 (L.sharedBase + 4360))) :
    eventTmpl [] L g t (.tcCommit .one 10 0 none) =
      .tc (.commit (commitSpec L.sharedBase)) (PTX.next t) := by
  have hS := hpre.sharedRange
  have hA := hpre.sharedAlign
  have hcs := clusterSize_eq hpre
  have hone := Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch
  have hs : TcCommit.resolve L .one (g / L.block) ⟨.shared, g / L.block, L.sharedBase + 4360⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) = some (commitSpec L.sharedBase) := by
    have hz : g / L.block = 0 := cta_zero hpre (lt_block hpre hg)
    have hr := Launch.oneDim_rankOfCta hpre.oneDimLaunch.1 0
    have hsz := Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1 0
    have hco := Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1 0
    rw [hz]
    simp [TcCommit.resolve, commitSpec, TcCommit.unicast, bar1, Launch.clusterStart, hcs, hr, hsz,
      hco, hpre.grid, hone]
  show tcCommitTmpl L g t (.tcCommit .one 10 0 none) = _
  rw [tc_commit h10 (by omega) (by omega) hg hs]

theorem tmpl_ld {c : Nat} (hc : c < 2 ^ 16) (h21 : t.regs 21 = some (b32 (taddr g c))) :
    eventTmpl [] L g t (.tcLd [22, 23, 24, 25, 26, 27, 28, 29] 21) =
      .tcLd (taddr g c) 8 .s32x32b
        (fun vals => setRegs (PTX.next t) [22, 23, 24, 25, 26, 27, 28, 29] vals) := by
  have hb := hpre.block
  have hg' := lt_block hpre hg
  show tcTmpl L g t (.tcLd [22, 23, 24, 25, 26, 27, 28, 29] 21) = _
  rw [tc_ld (by intro s h; cases h) (by rw [hb]) h21 (by unfold taddr; omega) (by decide)
    (by unfold taddr laneBase; rw [hb]; omega)]
  rfl

omit hg in
theorem tmpl_dealloc {c : Nat} (hc : c < 2 ^ 16) (h14 : t.regs 14 = some (b32 c)) :
    eventTmpl [] L g t (.tcDealloc .one (.reg 14) (.imm 32)) =
      .tc (.resource .one none (.dealloc c 32)) (PTX.next t) := by
  show tcTmpl L g t (.tcDealloc .one (.reg 14) (.imm 32)) = _
  rw [tc_dealloc (by rw [hpre.block]) h14 (by omega)]

omit hg in
theorem tmpl_waitLd : eventTmpl [] L g t .tcWaitLd = .tc .waitLd (PTX.next t) := by
  show tcTmpl L g t .tcWaitLd = _
  rw [tc_waitLd (by rw [hpre.block])]

end

section
variable {t : TState}

theorem tmpl_fenceProxy :
    eventTmpl [] L g t (.fence (.proxy (.async (some (.shared .cta))))) =
      .fenceProxy (.async (some (.shared .cta))) none (PTX.next t) := rfl
theorem tmpl_bar : eventTmpl [] L g t (.barSync (.imm 0) true) = .bar 0 (PTX.next t) := rfl
theorem tmpl_fenceAfter : eventTmpl [] L g t .tcFenceAfter = .tc .fenceAfter (PTX.next t) := rfl
theorem tmpl_fenceBefore : eventTmpl [] L g t .tcFenceBefore = .tc .fenceBefore (PTX.next t) := rfl
theorem tmpl_exit : eventTmpl [] L g t .ret = .exit := rfl

/-- A global address register plus an offset. -/
theorem effAddr_global_off {r x off : Nat} (h : t.regs r = some (b64 x)) (hx : x + off < 2 ^ 64) :
    effAddr L g t .global r off = .ok ⟨.global, 0, x + off⟩ := by
  have h64 : x + off < 18446744073709551616 := by simpa using hx
  have hx' : x < 2 ^ 64 := by omega
  simp only [effAddr, readBits, readReg, h, b64, bind, Except.bind, pure, Except.pure,
    truncBits_ofNat hx' (by decide)]
  rw [show BitVec.ofInt 64 (off : Int) = BitVec.ofNat 64 off by
    apply BitVec.eq_of_toNat_eq; simp, nf_add, toNat_ofNat_lt hx]

/-- Element `t.sub` of a 32-bit vector store of four registers to a 16-byte aligned global
address. -/
theorem storeTmpl_vec {base off x r : Nat} {srcs : List Opnd} {v : Value}
    (hb : t.regs base = some (b64 x)) (hx : x + off < 2 ^ 64) (hal : (x + off) % 16 = 0)
    (hlen : srcs.length = 4) (hs : srcs[t.sub]? = some (.reg r)) (hv : t.regs r = some v) :
    storeTmpl L g t .global 32 base off srcs =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' =>
        .write { loc := ⟨.global, 0, x + off + 4 * t.sub⟩, size := 4, elem := t.sub } v'.toBytes
          (afterStore t srcs) := by
  unfold storeTmpl
  rw [effAddr_global_off hb hx]
  simp only [bind, Except.bind, hlen]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp only [hs, readValue, readReg, hv, pure, Except.pure]
  cases storeValue 32 v <;> rfl

end

/-- The template of store `j` of the row. -/
theorem tmpl_st (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {t : TState} {j : Nat}
    {vals : List Value} (hj : j < 8) (hs : t.sub = j % 4)
    (h47 : t.regs 47 = some (b64 (D + 32 * g)))
    (hw : ∀ i < 8, (j < 4 → i < 4) → (4 ≤ j → 4 ≤ i) → t.regs (22 + i) = some (word vals i)) :
    eventTmpl [] L g t (if j < 4 then storeLo else storeHi) =
      match storeValue 32 (word vals j) with
      | .error f => .ub f
      | .ok v' =>
        .write (stAcc D g j) v'.toBytes
          (afterStore t (if j < 4 then [.reg 22, .reg 23, .reg 24, .reg 25]
            else [.reg 26, .reg 27, .reg 28, .reg 29])) := by
  have hrD := hpre.rangeD
  have haD := hpre.alignD
  have hg' := lt_block hpre hg
  by_cases h4 : j < 4
  · simp only [h4, ↓reduceIte]
    rw [storeLo, eventTmpl_storeQuad _ _ _ _ _ _ rfl]
    show storeTmpl L g t .global 32 47 ((0 : Nat) : Int) _ = _
    rw [storeTmpl_vec h47 (by omega) (by omega) rfl (r := 22 + j)
      (by rw [hs]; interval_cases j <;> rfl) (hw j hj (fun _ => h4) (fun h => absurd h (by omega)))]
    cases storeValue 32 (word vals j) <;>
      simp only [stAcc, hs, Nat.mod_eq_of_lt h4, Nat.add_zero]
  · simp only [h4, ↓reduceIte]
    rw [storeHi, eventTmpl_storeQuad _ _ _ _ _ _ rfl]
    show storeTmpl L g t .global 32 47 ((16 : Nat) : Int) _ = _
    rw [storeTmpl_vec h47 (by omega) (by omega) rfl (r := 22 + j)
      (by rw [hs]; interval_cases j <;> rfl) (hw j hj (fun h => absurd h h4) (fun _ => by omega))]
    have : D + 32 * g + 16 + 4 * (j % 4) = D + 32 * g + 4 * j := by omega
    cases storeValue 32 (word vals j) <;> simp only [stAcc, hs, this]

end

end PTX.Kernels.TcGemm.Proof
