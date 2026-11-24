-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.State

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc divOk fdiv Scan laneW paramW
  batchOf skipFirst reqOf tlOf prefixD headsW lanePreds partials chosen loopOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori ceil128 sbW sbi w32 neg32 wideS)

noncomputable section

/-- The parameters the role loads, by their names in the code. -/
def ps (p : Params) : List (String × Nat) :=
  ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_12", p.scaleLog2Bits) :: Epilogue.ps p

/-- The CTA index as `%ctaid.x` reads it, under the launch with the role's parameters explicit
(the launch the role's segments run on, `Base.params`). -/
abbrev ctaR (p : Params) (L : Launch) (g : Nat) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 (((explicitParams L (ps p)).ctaidOf
    (g / (explicitParams L (ps p)).block)).get .x))

/-- The registers of the row: `%r567` (the thread's statistics word), `%r569` and `%r573` (the
row's Tensor Memory address in the two accumulators), `%r570`, `%r571` (its output staging
rows). -/
abbrev statW (L : Launch) (g : Nat) : BitVec 64 := add32 (sbW L) (shl (rowW L g) 2)
abbrev quarter (L : Launch) (g : Nat) : BitVec 64 := shru (rowW L g) 5
abbrev tm0 (L : Launch) (g : Nat) : BitVec 64 := ori (shl (quarter L g) 21) 256
abbrev tm1 (L : Launch) (g : Nat) : BitVec 64 := ori (shl (quarter L g) 21) 384
abbrev stg0 (L : Launch) (g : Nat) : BitVec 64 :=
  add32 (sbW L) (r32 (shl (quarter L g) 12) ||| r32 (andi (shl (tidW L g) 7) 3968))
abbrev stg1 (L : Launch) (g : Nat) : BitVec 64 := addi (stg0 L g) 3072

/-- The chosen request's coordinates as the correction warps compute them: the output warp's
`Epilogue.coords` on the CTA index the role reads itself (`%r558`). -/
def coords (p : Params) (L : Launch) (g : Nat) (d : Epilogue.D) : Epilogue.Coords :=
  let heads := headsW p
  let k := paramW 800
  let r1207 := sub32 d.cur (mul32 d.tot heads)
  let r2357 := sub32 (ctaR p L g) (add32 r1207 d.pv)
  let r2358 := shl d.nt 8
  let r2366 := sel (scmp .gt .s (shrs r2358 3) k) (sel (scmp .gt .s (shrs r2358 4) k)
    (sel (scmp .gt .s (shrs r2358 5) k) (sel (scmp .gt .s (shrs r2358 6) k) (i32 1) (i32 2))
      (i32 4)) (i32 8)) (i32 16)
  let r2367 := min32 r2366 heads
  let r2368 := mul32 r2367 d.nt
  let r2373 := fdiv r2357 r2368
  let r2375 := sub32 r2357 (mul32 r2373 r2368)
  let r2376 := mul32 r2373 r2367
  let r2379 := sel (scmp .gt .s (add32 r2376 r2367) heads) (sub32 heads r2376) r2367
  let r2384 := fdiv r2375 r2379
  ⟨addi (shl (add32 d.nt (not32 r2384)) 8) 1073741824,
   sub32 (add32 r2375 r2376) (mul32 r2384 r2379), r2357, r2368, r2375, r2379⟩

/-- The registers of a loop round of pass `late` (the output warp's `loopRegs` on the role's
CTA index). -/
def loopRegsR (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : Epilogue.D) (r a m x : Nat) :
    List (Nat × Value) :=
  [(r, .bits 32 (addi (ctaR p L g) 1)), (r + 2, .bits 32 (reqOf L g d.grp)), (a, .bits 32 d.acc),
   (m, .bits 32 (min32 (addi d.grp 31) (batchOf p late))), (x, addrS p.cuQBase (reqOf L g d.grp))]

/-- The chosen request's row offset `%r6216` (the output warp's coordinates without the shift
and offset) and its head (`%r4888`). -/
def rowOff (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : BitVec 64 :=
  let co := coords p L g c
  add32 c.nt (not32 (fdiv co.n2 co.d2))

/-- The 64-bit head (`cvt.s64.s32 %rd2317`). -/
abbrev headW (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : BitVec 64 :=
  truncBits 64 (cvtIntBits false .s 64 .s 32 (truncBits 32 (coords p L g c).head))

/-- The number of K/V blocks of the tile (`%r576`). -/
def blocks (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
  min32 (ceil128 v.ukw)
    (ceil128 (addi (sub32 (add32 (shl (rowOff p L g v.sc) 8) v.ukw) (sub32 v.sc.c1 v.sc.c0)) 256))

/-- The registers of the launch the role keeps throughout. -/
def valuesStart (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062, b32 (g % L.block / 32)), (1069, b32 (L.sharedBase + 192)),
   (2390, b32 (L.sharedBase + 208)), (2535, b32 L.sharedBase),
   (6495, b32 (L.sharedBase + 144)), (6497, b32 (L.sharedBase + 224)), (7500, b64 p.lseBase),
   (7501, b64 p.lseStride), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
   (7506, b64 p.cuQBase)]

/-- The registers of the row and of the scheduler that keep one value wherever they are live. -/
def valuesRole (p : Params) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1612, .bits 32 (tidW L g)), (1613, .bits 32 (rowW L g)), (1614, sbi L 96),
   (1615, sbi L 104), (1616, .bits 32 (laneW L g)), (685, .pred (skipFirst p L g)),
   (1618, .bits 32 (ctaR p L g)), (7142, .bits 32 (headsW p)), (7143, .bits 32 (headsW p)),
   (7153, .bits 32 (paramW p.batch)), (7131, sbi L 232)]

/-- The registers of a scan round. -/
def valuesScan (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : Scan → List (Nat × Value)
  | .first =>
    [(8988, addrU p.cuQBase (laneW L g)), (7267, .bits 32 c.w), (7270, .bits 32 c.tl),
     (7277, b32 p.batch), (5868, w32 (i32 1))] ++ partials L g c 5878 3 7271
  | .loop =>
    loopRegsR p L g false c 1619 7268 7273 8990 ++
    [(697, .pred (scmpi .eq .b (laneW L g) 31)), (7269, .bits 32 c.w), (7270, .bits 32 c.tl),
     (7277, b32 p.batch)] ++ lanePreds L g 703 ++ partials L g c 5899 3 7271
  | .second =>
    [(9531, addrU p.cuQBase (laneW L g)), (7279, .bits 32 c.w), (7282, .bits 32 c.tl)] ++
      lanePreds L g 748 ++ partials L g c 7091 3 7283
  | .loop2 =>
    loopRegsR p L g true c 1658 7280 7285 9533 ++
    [(756, .pred (scmpi .eq .b (laneW L g) 31)), (7281, .bits 32 c.w), (7282, .bits 32 c.tl)] ++
      lanePreds L g 762 ++ partials L g c 7112 3 7283

/-- The registers of the choice of a request, in the first pass. -/
def valuesSelect (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  let r126 := sub32 c.cur (mul32 c.tot (headsW p))
  [(710, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p) r126) (ctaR p L g))),
   (1623, .bits 32 r126), (7273, .bits 32 c.gx), (7270, .bits 32 c.tl),
   (7271, .bits 32 (prefixD L g c)), (1624, .bits 32 (popc c.bal)),
   (5914, .bits 32 (addi (popc c.bal) (-1))), (7277, .bits 32 (chosen c)),
   (7275, .bits 32 c.pv), (7152, .bits 32 (paramW p.batch)), (7158, .bits 32 (paramW 800))]

/-- The registers of the second pass's ballot. -/
def valuesSelect2 (p : Params) (L : Launch) (g : Nat) (c : Epilogue.D) : List (Nat × Value) :=
  [(769, .pred (scmp .le .s (mad32 (prefixD L g c) (headsW p)
      (sub32 c.cur (mul32 c.tot (headsW p)))) (ctaR p L g))),
   (7282, .bits 32 c.tl), (7283, .bits 32 (prefixD L g c)), (1662, .bits 32 (popc c.bal)),
   (7128, .bits 32 (addi (popc c.bal) (-1))), (7287, w32 (i32 0))]

/-- The registers of the tile, from its choice to the end of the final stage: the named
barriers, the row's addresses, the request and the counts. -/
def valuesTile (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  let c := v.sc
  [(1625, .bits 32 (nb0W L g)), (1626, .bits 32 (nb1W L g)), (1627, .bits 32 (statW L g)),
   (1628, sbi L 200), (1629, .bits 32 (tm0 L g)), (1630, .bits 32 (stg0 L g)),
   (1631, .bits 32 (stg1 L g)), (1632, .bits 32 (andi (tidW L g) 1)),
   (1633, .bits 32 (tm1 L g)), (7276, .bits 32 (rowOff p L g c)), (7277, .bits 32 (chosen c)),
   (8991, wideS (chosen c)), (8992, addrS p.cuQBase (chosen c)),
   (8993, addrS p.usedKBase (chosen c)), (9605, .bits 64 (headW p L g c)),
   (1634, .bits 32 c.c0), (1635, .bits 32 (sub32 c.c1 c.c0)),
   (1636, .bits 32 (blocks p L g v)), (5967, .bits 32 (shl (rowOff p L g c) 8)),
   (5978, w32 (i32 1)), (7287, w32 (i32 1))]

/-- The rescale rounds' registers: the chunk addresses (`%r577` … `%r590`), the counter. -/
def valuesRound (v : V) (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(1637, .bits 32 (addi (tm0 L g) 16)), (1638, .bits 32 (addi (tm0 L g) 32)),
   (1639, .bits 32 (addi (tm0 L g) 48)), (1640, .bits 32 (addi (tm0 L g) 64)),
   (1641, .bits 32 (addi (tm0 L g) 80)), (1642, .bits 32 (addi (tm0 L g) 96)),
   (1643, .bits 32 (addi (tm0 L g) 112)), (1644, .bits 32 (addi (tm0 L g) 144)),
   (1645, .bits 32 (addi (tm0 L g) 160)), (1646, .bits 32 (addi (tm0 L g) 176)),
   (1647, .bits 32 (addi (tm0 L g) 192)), (1648, .bits 32 (addi (tm0 L g) 208)),
   (1649, .bits 32 (addi (tm0 L g) 224)), (1650, .bits 32 (addi (tm0 L g) 240)),
   (7278, w32 v.trip), (6236, w32 (i32 1)), (6494, w32 (i32 1))]

/-- The first data register of rescale chunk `c` of stage `st` (its 16 loaded elements, then
its 16 products). -/
def rBase (st : Fin 2) (c : Fin 8) : Nat := 5980 + 258 * st.val + 32 * c.val

/-- The stage's scale register (`%r591`, `%r592`) and the pair of it (`%rd1715`, `%rd1846`). -/
def rScaleReg (st : Fin 2) : Nat := 1651 + st.val
def rPairReg (st : Fin 2) : Nat := 9003 + 131 * st.val

/-- The loaded elements of a rescale chunk. -/
def rLoaded (st : Fin 2) (c : Fin 8) (xs : Nat → ℝ) : List (Nat × Value) :=
  (List.range 16).map fun i => (rBase st c + i, fv (xs i))

/-- The products of a rescale chunk, in the registers its store reads: register
`rBase + 16 + 2 i` holds element `14 - 2 i` times the scale and the next register element
`15 - 2 i`. -/
def rProducts (st : Fin 2) (c : Fin 8) (xs : Nat → ℝ) (s : Sc) : List (Nat × Value) :=
  (List.range 8).flatMap fun i =>
    [(rBase st c + 16 + 2 * i, fv (s.mul (xs (14 - 2 * i)))),
     (rBase st c + 17 + 2 * i, fv (s.mul (xs (15 - 2 * i))))]

/-- The registers of a rescale stage at its sites. -/
def valuesRescale (st : Fin 2) (v : V) : List (Nat × Value) :=
  [(rScaleReg st, (sOf v st).val), (rPairReg st, (sOf v st).pair),
   (731 + 2 * st.val,
    .pred (Assumption.erealCompare .lt ((sOf v st).real : EReal) (1 : ℝ)))]

/-- The final stage's registers: the reciprocal row sum and its pair, the output staging
addresses (`%r5440` … `%r5451`, then per chunk), the parities. -/
def fRecip (x : ℝ) : ℝ := if x ≠ 0 then x⁻¹ else 1

/-- A word of final stage `st`. -/
def fStage : Fin 2 → BitVec 64 → BitVec 64 → BitVec 64 | 0, a, _ => a | 1, _, b => b

/-- The final stage's address offsets, bases and barrier operands. -/
abbrev finalControlRegs (L : Launch) (g : Nat) : List (Nat × Value) :=
  let a0 := addi (stg0 L g) 68608
  let sw (x : BitVec 64) : BitVec 64 := xor32 (andi (shru x 3) 112) x
  [(6500, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16)))),
   (6502, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32)))),
   (6504, .bits 32 (sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64)))),
   (6508, .bits 32 (sw a0)), (6511, .bits 32 (sw (stg1 L g))),
   (6498, w32 (i32 1)), (6496, w32 (i32 0)), (6499, sbi L 152)]

/-- The pattern of `-∞`. -/
abbrev ninf32 : Value := .bits 32 (BitVec.ofNat 64 4286578688)

/-- A row maximum as the code holds it. -/
abbrev mxVal (x : Mx) : Value := Assumption.erealValue .f32 x.1

/-- The final stage's shared registers. -/
def valuesFinal (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(7134, .bits 32 (paramW p.scaleLog2Bits))] ++ finalControlRegs L g ++
  [(6512, fv v.rs0), (6513, mxVal v.rm0), (1653, fv v.rs1),
   (1654, mxVal v.rm1),
   (6515, fv (fRecip v.rs0)), (9259, fp (fRecip v.rs0) (fRecip v.rs0)),
   (6795, fv (fRecip v.rs1)), (9391, fp (fRecip v.rs1) (fRecip v.rs1)),
   (739, .pred (Assumption.erealCompare .ne (v.rs0 : EReal) (0 : ℝ))),
   (740, .pred (Assumption.erealCompare .ne (v.rs1 : EReal) (0 : ℝ)))]

/-- The first loaded register of final chunk `j` of stage `st`. -/
def fBaseN (st : Fin 2) (j : Nat) : Nat :=
  280 * st.val + [6516, 6535, 6554, 6573, 6591, 6608, 6625, 6642, 6659, 6676, 6693, 6710, 6727,
    6744, 6761, 6778].getD j 0
abbrev fBase (st : Fin 2) (j : Fin 16) : Nat := fBaseN st j.val

/-- The first pack register of final chunk `j` (four packs, then four products). -/
def fPack (st : Fin 2) (j : Fin 16) : Nat := 9260 + 132 * st.val + 8 * j.val

/-- The data registers of final chunk `j`: the eight elements, their four packs (high
elements first), the four products by the reciprocal `r` (low elements first), and the eight
unpacked products in the registers the two stores read. -/
def fChunk (st : Fin 2) (j : Fin 16) (ys : Nat → ℝ) (r : ℝ) : List (Nat × Value) :=
  let b := fBase st j
  let q := fPack st j
  let u := if j.val < 4 then b + 13 else b + 12
  (List.range 8).map (fun i => (b + i, fv (ys i))) ++
  [(q, fp (ys 6) (ys 7)), (q + 1, fp (ys 4) (ys 5)), (q + 2, fp (ys 2) (ys 3)),
   (q + 3, fp (ys 0) (ys 1)),
   (q + 4, fp (ys 0 * r) (ys 1 * r)), (q + 5, fp (ys 2 * r) (ys 3 * r)),
   (q + 6, fp (ys 4 * r) (ys 5 * r)), (q + 7, fp (ys 6 * r) (ys 7 * r)),
   (b + 8, fv (ys 2 * r)), (b + 9, fv (ys 3 * r)), (b + 10, fv (ys 0 * r)),
   (b + 11, fv (ys 1 * r)),
   (u, fv (ys 6 * r)), (u + 1, fv (ys 7 * r)), (u + 2, fv (ys 4 * r)), (u + 3, fv (ys 5 * r))]

/-- The output staging address registers of a final stage: the four store-0 bases
`a`, `a + d2`, `a + d4`, `a + d4 + d2` and the store-1 bases (each plus `d1`), and the load
address registers `tm0 + 128 st + 8 j` (`j ≥ 1`). -/
def fAddrs (L : Launch) (g : Nat) (st : Fin 2) : List (Nat × Value) :=
  let a := fStage st (xor32 (andi (shru (stg1 L g) 3) 112) (stg1 L g))
    (xor32 (andi (shru (addi (stg0 L g) 68608) 3) 112) (addi (stg0 L g) 68608))
  let tm (j : Nat) : BitVec 64 :=
    fStage st (addi (tm0 L g) (8 * j)) (addi (tm0 L g) (128 + 8 * j))
  let d1 := sel (scmpi .eq .b (andi (tidW L g) 1) 0) (i32 16) (i32 (-16))
  let d2 := sel (scmpi .eq .b (andi (tidW L g) 2) 0) (i32 32) (i32 (-32))
  let d4 := sel (scmpi .eq .b (andi (tidW L g) 4) 0) (i32 64) (i32 (-64))
  let a1 := add32 a d2
  let a2 := add32 a d4
  let a3 := add32 a2 d2
  [(fBase st 0 + 12, .bits 32 (add32 a d1)), (fBase st 1 - 2, .bits 32 (tm 1)),
   (fBase st 1 - 1, .bits 32 a1), (fBase st 1 + 12, .bits 32 (add32 a1 d1)),
   (fBase st 2 - 2, .bits 32 (tm 2)), (fBase st 2 - 1, .bits 32 a2),
   (fBase st 2 + 12, .bits 32 (add32 a2 d1)), (fBase st 3 - 2, .bits 32 (tm 3)),
   (fBase st 3 - 1, .bits 32 a3), (fBase st 3 + 12, .bits 32 (add32 a3 d1))] ++
  (List.range 12).map fun i => (fBaseN st (i + 4) - 1, .bits 32 (tm (i + 4)))

/-- The real number of the softmax scale (`param_12`, an `f32` pattern of a finite number by
`Pre.scales`). -/
def scaleR (p : Params) : ℝ := ((f32Value p.scaleLog2Bits).getD 0 : ℚ)

/-- The real number of the `f32` constant `0f3F317218` (the code's `ln 2`), as the constant's
rule reads it. -/
abbrev ln2F : ℝ := 1453635 / 2097152

/-- The LSE of a row from its sum and maximum: `(scale · max + log₂ sum) · ln 2`, in the extended
reals (`⊥` when the maximum is). -/
abbrev lseOf (p : Params) (rs : ℝ) (rm : Mx) : EReal :=
  ((scaleR p : EReal) * rm.1 + (Real.logb 2 rs : ℝ)) * (ln2F : ℝ)

/-- The LSE store address of the row (`%rd203`): the LSE base plus four times the row's index
`head · stride + q0 + (q-offset | row)`. -/
def lseAddr (p : Params) (L : Launch) (g : Nat) (v : V) : BitVec 64 :=
      (truncBits 64
        (truncBits 64
            (truncBits 64
              (truncBits 64 (BitVec.ofNat 64 p.lseBase) +
                truncBits 64
                  (if 2 ≥ 64 then 0
                  else
                    truncBits 64
                      (truncBits 64
                          (truncBits 64
                            (truncBits 64 (headW p L g v.sc) *
                                truncBits 64 (BitVec.ofNat 64 p.lseStride) +
                              truncBits 64
                                (truncBits 64
                                  (cvtIntBits false IType.s 64 IType.s 32
                                    (truncBits 32 v.sc.c0))))) <<<
                        2)))) +
          truncBits 64
            (if 2 ≥ 64 then 0
            else
              truncBits 64
                (truncBits 64
                    (truncBits 64
                        (truncBits 64
                          (cvtIntBits false IType.s 64 IType.s 32
                            (truncBits 32
                              (Epilogue.shl (rowOff p L g v.sc) 8)))) |||
                      truncBits 64 (truncBits 64 (truncBits 32 (rowW L g)))) <<<
                  2))))

/-- An LSE register: the LSE when the row sum is not zero, else `-inf` (the code's `selp` on the
row sum's comparison with 0, `%p737`, `%p740`). -/
abbrev lseSel (p : Params) (rs : ℝ) (rm : Mx) : Value :=
  if Assumption.erealCompare .ne (rs : EReal) (0 : ℝ) = true then
    Assumption.erealValue .f32 (lseOf p rs rm)
  else ninf32

/-- The LSE's registers: the store address, the two values (`%rd203`, `%r595`, `%r596`) and the
row limit `%r6017`. -/
def valuesLse (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  [(7491, .bits 64 (lseAddr p L g v)), (1655, lseSel p v.rs0 v.rm0),
   (7077, .bits 32 (sub32 (sub32 v.sc.c1 v.sc.c0) (shl (rowOff p L g v.sc) 8))),
   (1656, lseSel p v.rs1 v.rm1)]

/-- The registers at state `d`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let v := d.v
  match d.site with
  | .setmax | .bar1 | .arr _ => [(7277, b32 p.batch), (5868, w32 (i32 1))]
  | .word k | .down k | .up k _ | .total k => valuesScan p L g v.sc k
  | .vote false | .pre false | .tiles false => valuesSelect p L g v.sc
  | .vote true | .pre true | .tiles true => valuesSelect2 p L g v.sc
  | .q0 | .q1 | .uk | .nb _ | .free => valuesTile p L g v
  | .rbar st | .rscale st | .rvote st | .rwait st | .rarr st _ =>
    valuesRescale st v ++ valuesRound v L g ++ valuesTile p L g v
  | .rld st c | .rldw st c | .rst st c =>
    rLoaded st c v.xs ++ rProducts st c v.xs (sOf v st) ++ valuesRescale st v ++
      valuesRound v L g ++ valuesTile p L g v
  | .farr0 | .fbar _ | .fsum _ | .fmax _ | .farr _ | .fw _ _ | .fence _ | .fdone _ _ =>
    valuesFinal p L g v ++ fAddrs L g 0 ++ fAddrs L g 1 ++ valuesTile p L g v
  | .fld st j | .fwl st j | .fst st j _ =>
    fChunk st j v.ys (fRecip (rsOf v st)) ++ valuesFinal p L g v ++ fAddrs L g st ++
      valuesTile p L g v
  | .lse _ => valuesLse p L g v ++ valuesFinal p L g v ++ valuesTile p L g v
  | .wend false | .barEnd false | .exit false => [(7287, w32 (i32 1))]
  | .wend true | .barEnd true | .exit true => [(7287, w32 (i32 0))]

/-- The value of register `r` at state `d`. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesRole p L g).lookup r).getD
    (((valuesStart p L g).lookup r).getD (.pred false)))

/-- The registers live at a state: at the implicit wait of a rescale load, those after the
load. -/
def livePc (d : D) : Nat :=
  match d.site with
  | .rldw _ _ => d.site.pc + 1
  | _ => d.site.pc

abbrev facts (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live (livePc d)) (valueOf p L g d)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
