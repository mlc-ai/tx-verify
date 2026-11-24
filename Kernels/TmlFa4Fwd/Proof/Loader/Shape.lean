-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.Step.ShapeRegs
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # The loader warps' events by state

The event a state of the loader fires (`Ev`), for every site: the `setmaxnreg`; the scheduler's
events as in the output warp (`Epilogue.Ev` of the scan state); the reads of global memory (the
request's offsets and used length, the page index); the local stores of a page round and of a
pointer round's row address, with the bytes of the stored word; the local loads of the pointer
rounds and of the packets' row addresses (element `k` of the two-word load at sub-step `k`); the
shuffles of a row's address words from lane `i mod 8` of the group; the `cp.async` copies (the
row's global address to its swizzled shared destination, with some source size: the size is a
`selp` on the row being inside the used length); the commit; the copy arrival on the slot's full
barrier; the polls with their parity; the elections; the expect-tx arrivals; the tensor copies
with their barrier; the exit. Addresses and values are the table's words at the state (`rv`).
A read of global memory, a store, a copy, an election and a tensor copy may instead be undefined
behaviour, which their templates admit.

Each family of sites is proved by `site_shape` (`load_shape`), with the role's address facts:
the local addresses are `L.localBase` plus a constant (`Pre.localMemory`: `L.localBase` is a
multiple of 32, so every local access is aligned), and the mbarrier addresses are the shared base
plus multiples of 8 (`Pre.shared`: the shared base is a multiple of 1024), whatever the ring
slot's word. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi add32 shl andi shru addrS laneW headsW
  chosen vbits)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (sbW)

noncomputable section
set_option maxRecDepth 100000

/-- The output warp's site of a scheduler site. -/
def Site.toE : Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .start

/-- A request read's address register and offset: the request's offsets and its used length. -/
def reqRegs : Site → Nat × Int
  | .q1 => (7515, 4)
  | .uk => (7516, 0)
  | _ => (7515, 0)

/-- The word the table gives register `r` at state `d`. -/
def rv (p : Params) (L : Launch) (g w : Nat) (d : D) (r : Nat) : BitVec 64 :=
  vbits (valueOf p L g w (fun _ => .pred false) d r)

/-- Element `j` of `n` bytes of a local access at the address word `x` plus `off`. -/
def lacc (g : Nat) (x : BitVec 64) (off : Int) (n j : Nat) : Acc :=
  { loc := (⟨.local, g, wrapAddr 64 x off⟩ : Loc).at (n * j), size := n, elem := j }

/-! ### The operand registers of the sites -/

def pgLdA : Per → Nat | .prime => 7531 | .warm => 7650 | .steady => 7765
def pgStA : Per → Nat | .prime => 7533 | .warm => 7652 | .steady => 7767
def pgStV : Per → Nat | .prime => 7173 | .warm => 7176 | .steady => 7183
def rwStA : Per → Nat | .prime => 7534 | .warm => 7653 | .steady => 7768
def rwStV : Per → Nat | .prime => 1847 | .warm => 1975 | .steady => 2137

/-- A poll's address and parity registers. -/
def waitRegs : Site → Nat × Nat
  | .slot per v => [(1848, 1849), (1925, 1926), (1976, 7180), (2063, 2064), (2138, 7180),
      (2140, 2141)].getD (pk per v) (0, 0)
  | .tw t => [(1889, 1890), (1897, 1898), (1907, 1908), (1917, 1918), (2039, 7177),
      (2052, 7178), (2121, 7177)].getD t.val (0, 0)
  | .dw k => [(2288, 7180), (2289, 2290), (2291, 2292)].getD k.val (0, 0)
  | .dq => (2305, 7192)
  | _ => (0, 0)

/-- A packet's copy arrival: the address register and offset of the slot's full barrier. -/
def arrRegs (k : Nat) : Nat × Int :=
  [(2535, 32), (2535, 40), (1122, 32), (1141, 32), (1151, 32), (1171, 32)].getD k (0, 0)

/-- An expect-tx arrival: the barrier's address register and offset, the byte count register. -/
def taRegs : Site → Nat × Int × Nat
  | .ta t => [(2535, 0, 1892), (1114, 0, 1900), (2535, 8, 1910), (2535, 328, 1920),
      (1140, 0, 2041), (2535, 328, 2054), (1142, 0, 2123)].getD t.val (0, 0, 0)
  | .da => (2535, 8, 2307)
  | _ => (0, 0, 0)

/-- A TMA group's barrier: its address register and offset. -/
def tcBar (t : Fin 7) : Nat × Int :=
  [(2535, 0), (1114, 0), (2535, 8), (2535, 328), (1140, 0), (2535, 328), (1142, 0)].getD t.val
    (0, 0)

/-- A row copy's destination: the register of the swizzled row base (even and odd rows have one
each) and the offset of the row pair and the copy (the first block's V packet is 32768 bytes past
its K packet). -/
def cpDst (k : Nat) (i : Fin 16) (c : Fin 2) : Nat × Int :=
  (([[1083, 1084], [1083, 1084], [2003, 2006], [2082, 2085], [2161, 2164], [2203, 2206]].getD k
    []).getD (i.val % 2) 0,
   ((2048 * (i.val / 2) + 16384 * c.val + if k = 1 then 32768 else 0 : Nat) : Int))

/-- The second copy of a row reads 128 bytes past the first. -/
def cpOff (c : Fin 2) : Int := if c.val = 0 then 0 else 128

/-- A packet's address-load base (`%rd4` or `%rd5`) and the offset of half `h`. -/
def lwBase (k : Nat) : Nat := if k = 2 ∨ k = 4 then 7293 else 7292
def lwOff (h : Fin 2) : Int := if h.val = 0 then 0 else 8

/-- The register a row's shuffle sends: the low (`hi = false`) or high word of the half's
address. -/
def xSrc (k : Nat) (i : Fin 16) (hi : Bool) : Nat :=
  (pkRegs k).ld.getD (2 * (i.val / 8) + if hi then 1 else 0) 0

theorem cpOff_0 : cpOff 0 = 0 := rfl
theorem cpOff_1 : cpOff 1 = 128 := rfl
theorem lwOff_0 : lwOff 0 = 0 := rfl
theorem lwOff_1 : lwOff 1 = 8 := rfl

/-! ### The table -/

/-- **The event-shape table of the loader.** -/
def Ev (p : Params) (L : Launch) (g w : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .setmax => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ =>
      Epilogue.Ev p L g { d.v.sc with site := d.site.toE } e
  | .q0 | .q1 | .uk =>
      (∃ bs, e.kind = .rd (wordAcc (rv p L g w d (reqRegs d.site).1 +
        BitVec.ofInt 64 (reqRegs d.site).2).toNat) bs) ∨ ∃ f, e.kind = .ub f
  | .pgLd per _ =>
      (∃ bs, e.kind = .rd (wordAcc (rv p L g w d (pgLdA per) + BitVec.ofInt 64 0).toNat) bs) ∨
        ∃ f, e.kind = .ub f
  | .pgSt per _ =>
      (∃ v', storeValue 32 (.bits 32 (rv p L g w d (pgStV per))) = .ok v' ∧
        e.kind = .wr (lacc g (rv p L g w d (pgStA per)) 0 4 0) v'.toBytes) ∨ ∃ f, e.kind = .ub f
  | .rwSt per _ =>
      (∃ v', storeValue 32 (.bits 32 (rv p L g w d (rwStV per))) = .ok v' ∧
        e.kind = .wr (lacc g (rv p L g w d (rwStA per)) 0 4 0) v'.toBytes) ∨ ∃ f, e.kind = .ub f
  | .slot _ _ | .tw _ | .dw _ | .dq =>
      ∃ ok, e.kind = .wait (smLoc L g (rv p L g w d (waitRegs d.site).1) 0)
        ((truncBits 32 (rv p L g w d (waitRegs d.site).2)).toNat % 2) ok true .cta
  | .ptP per v _ => ∃ bs, e.kind = .rd (lacc g (rv p L g w d (ptRegs (pk per v)).b) 0 4 0) bs
  | .ptR per v _ => ∃ bs, e.kind = .rd (lacc g (rv p L g w d (ptRegs (pk per v)).c) 0 4 0) bs
  | .ptS per v _ =>
      (∃ v', storeValue 64 (.bits 64 (rv p L g w d (ptRegs (pk per v)).ad)) = .ok v' ∧
        e.kind = .wr (lacc g (rv p L g w d (ptRegs (pk per v)).u) 0 8 0) v'.toBytes) ∨
        ∃ f, e.kind = .ub f
  | .lw per v h =>
      ∃ bs, e.kind = .rd (lacc g (rv p L g w d (lwBase (pk per v))) (lwOff h) 4 d.k.val) bs
  | .xl per v i => ∃ recv ok,
      e.kind = .shfl .idx (.bits 32 (rv p L g w d (xSrc (pk per v) i false))) (i.val % 8) 6175
        recv ok
  | .xh per v i => ∃ recv ok,
      e.kind = .shfl .idx (.bits 32 (rv p L g w d (xSrc (pk per v) i true))) (i.val % 8) 6175
        recv ok
  | .cp per v i c =>
      (∃ n, e.kind = .copy ⟨{ loc := ⟨.global, 0, (rv p L g w d ((pkRegs (pk per v)).ad.getD i.val
          0) + BitVec.ofInt 64 (cpOff c)).toNat⟩, size := n },
        { loc := smLoc L g (rv p L g w d (cpDst (pk per v) i c).1) (cpDst (pk per v) i c).2,
          size := 16 }, .asyncGroup, .whole, none, true, none⟩) ∨ ∃ f, e.kind = .ub f
  | .commit _ _ => e.kind = .asyncCommit
  | .arrive per v =>
      e.kind = .asyncArrive (smLoc L g (rv p L g w d (arrRegs (pk per v)).1)
        (arrRegs (pk per v)).2) true
  | .te _ _ | .de =>
      (∃ inst ld, e.pc = d.site.pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .ta _ | .da =>
      e.kind = .arrive (smLoc L g (rv p L g w d (taRegs d.site).1) (taRegs d.site).2.1)
        (truncBits 32 (rv p L g w d (taRegs d.site).2.2)).toNat 1 true .cta
  | .tc t _ =>
      (∃ a s, e.kind = .tensorIssue a s ∧ s.mbar = smLoc L g (rv p L g w d (tcBar t).1)
        (tcBar t).2) ∨ ∃ f, e.kind = .ub f
  | .exit => e.kind = .exit

/-! ### Address facts -/

theorem truncBits64 (x : BitVec 64) : truncBits 64 x = x := by
  apply BitVec.eq_of_toNat_eq; simp [truncBits, x.isLt]

theorem add64_ofNat (a b : Nat) :
    add64 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  simp only [add64, r64, truncBits64, BitVec.ofNat_add]

theorem wrap_ofNat0 (n : Nat) : wrapAddr 64 (BitVec.ofNat 64 n) 0 = n % 2 ^ 64 := by
  simp [wrapAddr, truncBits]

theorem wrap_ofNat8 (n : Nat) : wrapAddr 64 (BitVec.ofNat 64 n) 8 = (n + 8) % 2 ^ 64 := by
  simp only [wrapAddr, truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem wideU4_fin (j : Fin 2) :
    wideU4 (i32 ((j.val : Nat) : Int)) = BitVec.ofNat 64 (4 * j.val) := by
  fin_cases j <;> decide

theorem shl64_fin2 (j : Fin 2) :
    shl64 (m64 ((j.val : Nat) : Int)) 2 = BitVec.ofNat 64 (4 * j.val) := by
  fin_cases j <;> decide

theorem shl64_fin3 (j : Fin 2) :
    shl64 (m64 ((j.val : Nat) : Int)) 3 = BitVec.ofNat 64 (8 * j.val) := by
  fin_cases j <;> decide

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := (BitVec.ofNat_add a b).symm

theorem wideU4_0 : wideU4 (i32 0) = BitVec.ofNat 64 0 := by decide
theorem wideU4_1 : wideU4 (i32 1) = BitVec.ofNat 64 4 := by decide
theorem shl64_0_2 : shl64 (m64 0) 2 = BitVec.ofNat 64 0 := by decide
theorem shl64_1_2 : shl64 (m64 1) 2 = BitVec.ofNat 64 4 := by decide
theorem shl64_0_3 : shl64 (m64 0) 3 = BitVec.ofNat 64 0 := by decide
theorem shl64_1_3 : shl64 (m64 1) 3 = BitVec.ofNat 64 8 := by decide

theorem shl64_o0_2 : shl64 (BitVec.ofInt 64 0) 2 = BitVec.ofNat 64 0 := by decide
theorem shl64_o1_2 : shl64 (BitVec.ofInt 64 1) 2 = BitVec.ofNat 64 4 := by decide
theorem shl64_o0_3 : shl64 (BitVec.ofInt 64 0) 3 = BitVec.ofNat 64 0 := by decide
theorem shl64_o1_3 : shl64 (BitVec.ofInt 64 1) 3 = BitVec.ofNat 64 8 := by decide

theorem lb_mod4 {L : Launch} (h : L.localBase % 32 = 0) (c : Nat) :
    (L.localBase + c) % 2 ^ 64 % 4 = c % 4 := by omega

theorem lb_mod8 {L : Launch} (h : L.localBase % 32 = 0) (c : Nat) :
    (L.localBase + c) % 2 ^ 64 % 8 = c % 8 := by omega

theorem shl3_eq (x : BitVec 64) : shl x 3 = truncBits 32 (r32 x <<< 3) := by
  have h : (i32 3).toNat = 3 := by decide
  show (if (i32 3).toNat ≥ 32 then 0 else truncBits 32 (r32 x <<< (i32 3).toNat)) = _
  rw [h]; rfl

theorem lb_mod4' {L : Launch} (h : L.localBase % 32 = 0) : L.localBase % 2 ^ 64 % 4 = 0 := by
  omega

theorem lb_mod8' {L : Launch} (h : L.localBase % 32 = 0) : L.localBase % 2 ^ 64 % 8 = 0 := by
  omega

/-- A multiple of 8 built from the shared base (a multiple of 1024), shifts by 3 and offsets
that are multiples of 8, modulo `2 ^ 32`. -/
macro "load_m8" : tactic => `(tactic| (
  have h1 := (‹Pre _ _ _›).shared.1
  simp only [emptyAt, shl3_eq, addi, add32, r32, i32, sbW, truncBits, BitVec.toNat_ofNat,
     BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega))

set_option hygiene false in
/-- The shape obligations of the sites of `s` that the theorem's `hs` admits. -/
macro "load_shape" : tactic => `(tactic| (
  have hlb := (‹Pre _ _ _›).localMemory.1
  site_shape s skip_by (simp at hs)
    unfolding [Ev, rv, lacc, reqRegs, b32, b64, waitRegs, arrRegs, taRegs, tcBar, cpDst, cpOff_0,
       cpOff_1, lwBase, lwOff_0, lwOff_1, xSrc, pkRegs, ptRegs, pgLdA, pgStA, pgStV, rwStA, rwStV,
       pk, Epilogue.vbits, Site.toE, Epilogue.Ev, Epilogue.rdAddr, valueOf, values, valuesScan,
       valuesSelect, valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime, valuesRows,
       valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady,
       valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain, valuesRole,
       valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds, lookupLit,
       truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3,
       lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd,
       Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some, Option.getD_none,
       List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one, Nat.cast_zero,
       Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1, shl64_0_2, shl64_1_2,
       shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3, shl64_o1_3, Nat.reduceMod,
       Nat.reduceEqDiff, ↓reduceIte, or_self, or_false, false_or, BitVec.add_zero]
    reg_vals [b32, b64, valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesReq,
       valuesSetup, valuesPgPrime, valuesPrime, valuesRows, valuesRing, valuesPt, valuesWarm,
       valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady, valuesPgSteady, valuesSteadyK,
       valuesSteadyV, valuesTma, valuesDrain, valuesRole, valuesStart, Epilogue.partials,
       Epilogue.loopRegs, Epilogue.lanePreds, lookupLit, truncBits64, add64_ofNat, wrap_ofNat0,
       wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb,
       lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero,
       Option.getD_some, Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero,
       Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0,
       wideU4_1, shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
       shl64_o1_3]
    addr_by (first
      | rw [‹Pre _ _ _›.block]
      | (apply PTX.Flow.mbarLoc_reg
         · site_read [b32, b64, rv, Epilogue.vbits, valueOf, values, valuesScan, valuesSelect,
            valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime, valuesRows,
            valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady,
            valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain, valuesRole,
            valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds, lookupLit,
            truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3,
            lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd,
            Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some, Option.getD_none,
            List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one, Nat.cast_zero,
            Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1, shl64_0_2, shl64_1_2,
            shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3, shl64_o1_3, Nat.reduceMod,
            Nat.reduceEqDiff, ↓reduceIte, or_self, or_false, false_or, BitVec.add_zero]
         · refine PTX.Flow.trunc_add_mod8 ?_ (by decide)
           try simp only [b32, b64, rv, Epilogue.vbits, valueOf, values, valuesScan, valuesSelect,
              valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime, valuesRows,
              valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV,
              valuesSteady, valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain,
              valuesRole, valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds,
              lookupLit, truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2,
              shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc,
              Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some,
              Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one,
              Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1,
              shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
              shl64_o1_3]
           load_m8))))

set_option hygiene false in
/-- The shape obligation of one site by the inversion lemma `lem`, for the classes where
`site_shape`'s own lemma does not fit: a `cp.async` whose source size is a `selp` on the row being
inside the used length (`shape_cpAsyncN`), a tensor copy whose barrier the table states
(`shape_cpTensorAt`). The side goals as in `site_shape`; the shape goals by `shape_close`. -/
macro "load_with " lem:term : tactic => `(tactic| (
  have hlb := (‹Pre _ _ _›).localMemory.1
  intro t ins e o hat hi hc hf
  have hF : Holds t.regs (PTX.Flow.factsFrom _ _) := hat.2.2.2.2
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  apply ($lem hf)
  all_goals try first
    | (site_read [b32, b64, valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesReq,
       valuesSetup, valuesPgPrime, valuesPrime, valuesRows, valuesRing, valuesPt, valuesWarm,
       valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady, valuesPgSteady, valuesSteadyK,
       valuesSteadyV, valuesTma, valuesDrain, valuesRole, valuesStart, Epilogue.partials,
       Epilogue.loopRegs, Epilogue.lanePreds, lookupLit, truncBits64, add64_ofNat, wrap_ofNat0,
       wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb,
       lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero,
       Option.getD_some, Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero,
       Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0,
       wideU4_1, shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
       shl64_o1_3]
       done)
    | (site_acc [b32, b64, valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesReq,
       valuesSetup, valuesPgPrime, valuesPrime, valuesRows, valuesRing, valuesPt, valuesWarm,
       valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady, valuesPgSteady, valuesSteadyK,
       valuesSteadyV, valuesTma, valuesDrain, valuesRole, valuesStart, Epilogue.partials,
       Epilogue.loopRegs, Epilogue.lanePreds, lookupLit, truncBits64, add64_ofNat, wrap_ofNat0,
       wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb,
       lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero,
       Option.getD_some, Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero,
       Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0,
       wideU4_1, shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
       shl64_o1_3]
       done)
    | (apply PTX.Flow.mbarLoc_reg
       · site_read [b32, b64, rv, Epilogue.vbits, b32, b64, valueOf, values, valuesScan,
          valuesSelect, valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime,
          valuesRows, valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV,
          valuesSteady, valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain,
          valuesRole, valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds,
          lookupLit, truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2,
          shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc,
          Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some,
          Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one,
          Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1,
          shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
          shl64_o1_3]
       · refine PTX.Flow.trunc_add_mod8 ?_ (by decide)
         try simp only [b32, b64, rv, Epilogue.vbits, b32, b64, valueOf, values, valuesScan,
            valuesSelect, valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime,
            valuesRows, valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV,
            valuesSteady, valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain,
            valuesRole, valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds,
            lookupLit, truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2,
            shl64_fin3, lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc,
            Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some,
            Option.getD_none, List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one,
            Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1,
            shl64_0_2, shl64_1_2, shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3,
            shl64_o1_3]
         load_m8)
  all_goals try (
    intros
    simp only [Ev, rv, lacc, reqRegs, b32, b64, waitRegs, arrRegs, taRegs, tcBar, cpDst, cpOff_0,
       cpOff_1, lwBase, lwOff_0, lwOff_1, xSrc, pkRegs, ptRegs, pgLdA, pgStA, pgStV, rwStA, rwStV,
       pk, Epilogue.vbits, Site.toE, Epilogue.Ev, Epilogue.rdAddr, valueOf, values, valuesScan,
       valuesSelect, valuesSelect2, valuesReq, valuesSetup, valuesPgPrime, valuesPrime, valuesRows,
       valuesRing, valuesPt, valuesWarm, valuesPgWarm, valuesWarmK, valuesWarmV, valuesSteady,
       valuesPgSteady, valuesSteadyK, valuesSteadyV, valuesTma, valuesDrain, valuesRole,
       valuesStart, Epilogue.partials, Epilogue.loopRegs, Epilogue.lanePreds, lookupLit,
       truncBits64, add64_ofNat, wrap_ofNat0, wrap_ofNat8, wideU4_fin, shl64_fin2, shl64_fin3,
       lb_mod4 hlb, lb_mod8 hlb, lb_mod4' hlb, lb_mod8' hlb, Nat.add_assoc, Nat.reduceAdd,
       Nat.reduceMul, Nat.add_zero, Nat.mul_zero, Option.getD_some, Option.getD_none,
       List.getD_cons_succ, List.getD_cons_zero, Fin.val_zero, Fin.val_one, Nat.cast_zero,
       Nat.cast_one, Nat.cast_ofNat, ofNat_add_ofNat, wideU4_0, wideU4_1, shl64_0_2, shl64_1_2,
       shl64_0_3, shl64_1_3, shl64_o0_2, shl64_o1_2, shl64_o0_3, shl64_o1_3, Nat.reduceMod,
       Nat.reduceEqDiff, ↓reduceIte, or_self, or_false, false_or, BitVec.add_zero])
  all_goals try shape_close))

/-- A `cp.async` site (`load_with shape_cpAsyncN`). -/
macro "load_cp" : tactic => `(tactic| load_with PTX.Flow.shape_cpAsyncN)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
