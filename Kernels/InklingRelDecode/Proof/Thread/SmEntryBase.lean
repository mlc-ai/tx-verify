-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec
public import Kernels.InklingRelDecode.Proof.Thread.Sm

@[expose] public section

/-! # The softmax region's entry numbers: what the prologue produces

`Sm.Ent` is the record of numbers the softmax region reads from the registers the prologue leaves
at pc 573 (`Sm.lean`). This file writes down the `Ent` the prologue produces, field by field,
`entOf`, and proves the register-level facts the entry link needs: the value of each of the 29
registers live at pc 574 in the prologue's table (`ProA.valueOf`) is the value the softmax
region's table (`Sm.valueOf`) gives it at the first state.

| `Ent` field | register | value the prologue leaves | source |
| --- | --- | --- | --- |
| `tm` | `%r2` | the Tensor Memory base the common code loaded | `dt.pro.tm` |
| `split` | `%r17` | `ctaid.x` | `ProBSpec.cta_coords` |
| `qlen` | `%r20` | `q_len` | `exit_spec` |
| `past` | `%r21` | `seqlen_k - q_len` | `exit_spec` |
| `nbias` | `%r22` | `n_bias` | `exit_spec` |
| `r23` | `%r23` | `past / 128` | `exit_spec` |
| `r24` | `%r24` | `⌈seqlen_k / 128⌉ * 128` | `exit_spec` |
| `r25`, `r26` | `%r25`, `%r26` | `num_iters` | `exit_spec` |
| `kvh` | `%r29` | `6 * ctaid.y` | `r29_eq` |
| `qs` | `%r149` | `cu_seqlens_q[req]` | `WordsMatch` |
| `scb`, `sc` | `%r64` | the bits of `softmax_scale` and its value | `Pre.paramScale` |
| `strRel` | `%r66` | `stride_rel_t` (a `u32` parameter) | `ArgsOk.p17` |
| `splits` | `%r71` | `num_splits` | `dt.pro.w71` |
| `ntok` | `%r72` | `num_tokens` | `ArgsOk.p25` |
| `rel`, `rd75`, `rd76` | `%rd71`, `%rd75`, `%rd76` | `Rel`/`OPart`/`LsePart` pointers | `ArgsOk` |

`%p3` (`tid < 32`) is a register of the common code, not of the prologue (`Pro.rest 3`); the
entry link takes its value as a premise, as the worker's `Worker.Inv` does. -/

namespace PTX.Kernels.InklingRelDecode.Proof.SmEntry
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- **The `Ent` the prologue produces**, for the thread `g` of a launch with parameters `P` whose
data at the end of the prologue is `dt`. The request is `r = ctaid.z` and the split `s =
ctaid.x`.

* From `ProB.exit_spec`: `qlen = q_len`, `past`, `nbias = n_bias`, `r23 = past / 128`,
  `r24 = blocks * 128`, `r25 = r26 = num_iters`.
* From the CTA: `split = ctaid.x`, `kvh = 6 * ctaid.y` (`%r29 = kv_head * 6`).
* From the loaded words: `qs = cu_seqlens_q[req]` (`WordsMatch.cu0`).
* From `Pre`: `sc = softmax_scale`, `splits = num_splits`.
* The words of the registers themselves (the parameters the prologue read: `scb`, `strRel`,
  `ntok`, `rel`, `rd75`, `rd76`, and the base `tm` the common code loaded). A 32-bit parameter
  is the low 32 bits of its parameter word; `entOf_params` states which `Spec` numbers they are. -/
def entOf (P : Params) (L : Launch) (g : Nat) (dt : ProA.Dat) : Sm.Ent where
  tm := dt.pro.tm
  split := ProA.cta L g .x
  qlen := P.qLen (ProA.cta L g .z)
  past := P.past (ProA.cta L g .z)
  nbias := P.nBias (ProA.cta L g .z)
  r23 := P.past (ProA.cta L g .z) / 128
  r24 := P.blocks (ProA.cta L g .z) * 128
  r25 := P.numIters (ProA.cta L g .z) (ProA.cta L g .x)
  r26 := P.numIters (ProA.cta L g .z) (ProA.cta L g .x)
  kvh := ProA.cta L g .y * 6
  qs := P.qStart (ProA.cta L g .z)
  scb := dt.pro.x15.toNat % 2 ^ 32
  sc := P.scale
  strRel := dt.pro.x17.toNat % 2 ^ 32
  splits := P.splits
  ntok := dt.pro.x25.toNat % 2 ^ 32
  rel := dt.pro.x6.toNat
  rd75 := dt.pro.x10.toNat
  rd76 := dt.pro.x11.toNat

/-- The first state of the softmax region: at `setmaxnreg.inc` (pc 574), loop counter 0, the
running maximum `-inf` (`0xFF800000`) and sum 0 the first preload expects, no bias word loaded. -/
def d0 (e : Sm.Ent) : Sm.D where
  site := .setMaxReg
  e := e
  i := 0
  m := b32 4286578688
  l := b32 0
  cw := 0
  cv := 0
  w := fun _ => Sm.z16
  v := fun _ => Sm.z16

/-! ### The softmax region's table at the first state -/

section SmSide
variable (L : Launch) (g : Nat) (e : Sm.Ent)

theorem sm_3 : Sm.valueOf L g (d0 e) 3 = .pred (decide (g % L.block < 32)) := rfl
theorem sm_177 : Sm.valueOf L g (d0 e) 177 = .pred (decide (g % L.block % 128 = 0)) := rfl
theorem sm_199 : Sm.valueOf L g (d0 e) 199 = Sm.z16 := rfl
theorem sm_462 : Sm.valueOf L g (d0 e) 462 = b32 (g % L.block) := rfl
theorem sm_463 : Sm.valueOf L g (d0 e) 463 = b32 e.tm := rfl
theorem sm_464 : Sm.valueOf L g (d0 e) 464 = b32 (g % L.block / 32) := rfl
theorem sm_478 : Sm.valueOf L g (d0 e) 478 = b32 e.split := rfl
theorem sm_481 : Sm.valueOf L g (d0 e) 481 = b32 e.qlen := rfl
theorem sm_482 : Sm.valueOf L g (d0 e) 482 = b32 e.past := rfl
theorem sm_483 : Sm.valueOf L g (d0 e) 483 = b32 e.nbias := rfl
theorem sm_484 : Sm.valueOf L g (d0 e) 484 = b32 e.r23 := rfl
theorem sm_485 : Sm.valueOf L g (d0 e) 485 = b32 e.r24 := rfl
theorem sm_486 : Sm.valueOf L g (d0 e) 486 = b32 e.r25 := rfl
theorem sm_487 : Sm.valueOf L g (d0 e) 487 = b32 e.r26 := rfl
theorem sm_490 : Sm.valueOf L g (d0 e) 490 = b32 e.kvh := rfl
theorem sm_491 : Sm.valueOf L g (d0 e) 491 = b32 ((e.tm + 256) % 2 ^ 32) := rfl
theorem sm_525 : Sm.valueOf L g (d0 e) 525 = b32 e.scb := rfl
theorem sm_527 : Sm.valueOf L g (d0 e) 527 = b32 e.strRel := rfl
theorem sm_532 : Sm.valueOf L g (d0 e) 532 = b32 e.splits := rfl
theorem sm_533 : Sm.valueOf L g (d0 e) 533 = b32 e.ntok := rfl
theorem sm_610 : Sm.valueOf L g (d0 e) 610 = b32 e.qs := rfl
theorem sm_623 : Sm.valueOf L g (d0 e) 623 = b32 ((L.sharedBase + 213312) % 2 ^ 32) := rfl
theorem sm_624 : Sm.valueOf L g (d0 e) 624 = b32 ((L.sharedBase + 213328) % 2 ^ 32) := rfl
theorem sm_666 : Sm.valueOf L g (d0 e) 666 = b32 (L.sharedBase % 2 ^ 32) := rfl
theorem sm_792 : Sm.valueOf L g (d0 e) 792 = b32 ((L.sharedBase + 212992) % 2 ^ 32) := rfl
theorem sm_1912 : Sm.valueOf L g (d0 e) 1912 = b32 (Sm.key (e.split + 0 * e.splits)) := rfl
theorem sm_2019 : Sm.valueOf L g (d0 e) 2019 = b64 e.rel := rfl
theorem sm_2023 : Sm.valueOf L g (d0 e) 2023 = b64 e.rd75 := rfl
theorem sm_2024 : Sm.valueOf L g (d0 e) 2024 = b64 e.rd76 := rfl

end SmSide

/-! ### The prologue's table, one register at a time -/

theorem trunc64 (x : BitVec 64) : truncBits 64 x = BitVec.ofNat 64 x.toNat := by
  simp [truncBits, Nat.mod_eq_of_lt x.isLt]

theorem truncBits_idem (w : Nat) (x : BitVec 64) (hw : w ≤ 64) :
    truncBits w (truncBits w x) = truncBits w x := by
  simp only [truncBits, BitVec.toNat_ofNat]
  have : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  rw [Nat.mod_mod_of_dvd _ this, Nat.mod_mod]

theorem wShl32_trunc (a s : BitVec 64) : truncBits 32 (ProA.wShl32 a s) = ProA.wShl32 a s := by
  unfold ProA.wShl32
  split_ifs
  · simp [truncBits]
  · exact truncBits_idem 32 _ (by omega)

theorem wMulLo32_ofNat (a b : Nat) :
    ProA.wMulLo32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (a % 2 ^ 32 * (b % 2 ^ 32) % 2 ^ 32) := by
  simp only [ProA.wMulLo32, ProA.truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hx : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hy : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hxy : a % 2 ^ 32 * (b % 2 ^ 32) < 2 ^ 64 :=
    calc a % 2 ^ 32 * (b % 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 64 := by norm_num
  have e1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have e2 : b % 2 ^ 32 % 2 ^ 64 = b % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have e3 : a % 2 ^ 32 * (b % 2 ^ 32) % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 * (b % 2 ^ 32) % 2 ^ 32 :=
    Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, Nat.mod_eq_of_lt hxy, e3]

theorem r205_eq (L : Launch) (g : Nat) (dt : ProA.Dat) :
    ProA.v_r205 L g dt = BitVec.ofNat 64 (L.sharedBase % 2 ^ 32) := by
  simp only [ProA.v_r205, ProA.wSmem, ProA.truncBits_ofNat _ _ (by omega : 32 ≤ 64), Nat.add_zero]

/-- `%p177` is `tid & 127 == 0`, which for a thread of the default partition is `tid % 128 = 0`. -/
theorem p177_eq (L : Launch) (g : Nat) (dt : ProA.Dat) (h : g % L.block < 128) :
    ProA.pEqB32 (ProA.v_r27 L g dt) (BitVec.ofInt 64 0) = decide (g % L.block % 128 = 0) := by
  have l : BitVec.ofInt 64 127 = BitVec.ofNat 64 127 := by rw [nf_ofInt]; rfl
  have l0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := by rw [nf_ofInt]; rfl
  simp only [ProA.v_r27, ProA.v_r1, l, l0, ProA.wAnd32_ofNat, ProA.pEqB32, PTX.compare,
    ProA.truncBits_ofNat _ _ (by omega : 32 ≤ 64)]
  have e : ProA.tidOf L g % 2 ^ 32 &&& 127 % 2 ^ 32 = ProA.tidOf L g := by
    have h1 : ProA.tidOf L g % 2 ^ 32 = ProA.tidOf L g :=
      Nat.mod_eq_of_lt (by unfold ProA.tidOf; omega)
    have h2 : (127 : Nat) % 2 ^ 32 = 2 ^ 7 - 1 := by norm_num
    rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by unfold ProA.tidOf; omega)]
  simp only [Option.getD_some, e]
  simp only [BitVec.toNat_ofNat, decide_eq_decide]
  unfold ProA.tidOf
  omega

section ProASide
variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {dt : ProA.Dat}

theorem cta_x_lt (hpre : Pre P L mem0) (hg : g < L.threads) : ProA.cta L g .x < 2 ^ 32 := by
  have := (ProA.cta_lt hpre hg).1
  have := hpre.splitsRange
  omega

/-- **Register by register.** Every register live at pc 574 has the value in the softmax region's
table at the first state `d0 (entOf P L g dt)` that the prologue's table gives it.

Premises: `Pre`, a thread of the launch, `ArgsOk` (the inherited registers hold the launch's
parameters), `dt.pro.w71 = num_splits`, `WordsMatch` (the three loaded words are the request's) and
the value of `%p3`, a register of the common code (`Pro.rest 3`). -/
theorem live_eq (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hs : dt.pro.w71 = P.splits) (hm : ProA.WordsMatch P (ProA.cta L g .z) dt)
    (hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))) (hw : dt.w = b32 dt.pro.tm) :
    ∀ r ∈ Flow.live Flow.setMaxReg_1,
      Sm.valueOf L g (d0 (entOf P L g dt)) r = ProA.valueOf L g dt r := by
  obtain ⟨v481, v482, v483, v484, v485, v486, v487, -, v623, v624⟩ :=
    ProA.exit_values hpre hg ha hs hm
  have hx := cta_x_lt hpre hg
  have hy : ProA.cta L g .y < 2 := (ProA.cta_lt hpre hg).2.1
  have ht : g % L.block < 128 := ha.tid
  have l6 : BitVec.ofInt 64 6 = BitVec.ofNat 64 6 := by rw [nf_ofInt]; rfl
  have l256 : BitVec.ofInt 64 256 = BitVec.ofNat 64 256 := by rw [nf_ofInt]; rfl
  have l212992 : BitVec.ofInt 64 212992 = BitVec.ofNat 64 212992 := by rw [nf_ofInt]; rfl
  intro r hr
  rw [ProA.exitRegs] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sm_3]; exact hp3.symm
  · rw [sm_177]
    show _ = Value.pred (ProA.pEqB32 _ _)
    rw [p177_eq L g dt ht]
  · rw [sm_199]; rfl
  · rw [sm_462]; rfl
  · rw [sm_463]; exact hw.symm
  · rw [sm_464]; rfl
  · rw [sm_478]
    show _ = Value.bits 32 (ProA.wCta L g .x)
    rw [ProA.wCta_eq, Nat.mod_eq_of_lt hx]; rfl
  · rw [sm_481, v481]; rfl
  · rw [sm_482, v482]; rfl
  · rw [sm_483, v483]; rfl
  · rw [sm_484, v484]; rfl
  · rw [sm_485, v485]; rfl
  · rw [sm_486, v486]; rfl
  · rw [sm_487, v487]; rfl
  · rw [sm_490]
    show _ = Value.bits 32 (ProA.wMulLo32 (ProA.wCta L g .y) _)
    rw [ProA.wCta_eq, l6, wMulLo32_ofNat]
    have : ProA.cta L g .y % 2 ^ 32 % 2 ^ 32 * (6 % 2 ^ 32) % 2 ^ 32 = ProA.cta L g .y * 6 := by
      omega
    rw [this]; rfl
  · rw [sm_491, ProA.valueOf_491, ProA.r30Of_good (L := L) (g := g) hw]
    show _ = Value.bits 32 (ProA.wAdd32 (BitVec.ofNat 64 dt.pro.tm) _)
    rw [l256, ProA.wAdd32_ofNat]; rfl
  · rw [sm_525]; rfl
  · rw [sm_527]; rfl
  · rw [sm_532]
    show _ = Value.bits 32 (BitVec.ofNat 64 dt.pro.w71)
    rw [hs]; rfl
  · rw [sm_533]; rfl
  · rw [sm_610]
    show _ = Value.bits 32 (BitVec.ofNat 64 dt.cu0)
    rw [hm.cu0]; rfl
  · rw [sm_623, v623]
  · rw [sm_624, v624]
  · rw [sm_666]
    show _ = Value.bits 32 (ProA.v_r205 L g dt)
    rw [r205_eq]; rfl
  · rw [sm_792]
    show _ = Value.bits 32 (ProA.wAdd32 (ProA.v_r205 L g dt) _)
    rw [l212992, r205_eq, ProA.wAdd32_ofNat]
    have : (L.sharedBase % 2 ^ 32 + 212992) % 2 ^ 32 = (L.sharedBase + 212992) % 2 ^ 32 := by omega
    rw [this]; rfl
  · rw [sm_1912]
    show _ = Value.bits 32 (ProA.v_r1451 L g dt)
    have h1 := ProA.r1451_eq L g dt
    have h2 : ProA.v_r1451 L g dt = truncBits 32 (ProA.v_r1451 L g dt) :=
      (wShl32_trunc _ _).symm
    rw [h2, h1, Nat.mod_eq_of_lt hx]
    simp only [Sm.key, entOf, b32, Nat.zero_mul, Nat.add_zero]
  · rw [sm_2019]
    show _ = Value.bits 64 (truncBits 64 dt.pro.x6)
    rw [trunc64]; rfl
  · rw [sm_2023]
    show _ = Value.bits 64 (truncBits 64 dt.pro.x10)
    rw [trunc64]; rfl
  · rw [sm_2024]
    show _ = Value.bits 64 (truncBits 64 dt.pro.x11)
    rw [trunc64]; rfl

/-- The parameter words the prologue read are the launch's: the scale's bits, the `u32` stride and
count, and the three pointers (`Pre.paramScale`, `paramStrideRel`, `paramNTok`, `paramRel`,
`paramO`, `paramLse`). -/
theorem entOf_params (hpre : Pre P L mem0) (ha : ProA.ArgsOk L g dt.pro) :
    (∃ bits < 2 ^ 32, (entOf P L g dt).scb = bits ∧
      (f32Value bits).map (fun x : ℚ => (x : ℝ)) = some P.scale) ∧
    (entOf P L g dt).strRel = P.strideRel % 2 ^ 32 ∧
    (entOf P L g dt).ntok = P.nTok % 2 ^ 32 ∧
    (entOf P L g dt).rel = P.relBase % 2 ^ 64 ∧
    (entOf P L g dt).rd75 = P.oBase % 2 ^ 64 ∧
    (entOf P L g dt).rd76 = P.lseBase % 2 ^ 64 := by
  have key : ∀ {x : BitVec 64} {n : Nat}, some x = some (BitVec.ofNat 64 n) →
      x.toNat = n % 2 ^ 64 := by
    intro x n h
    rw [Option.some.inj h]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨bits, hb, hp, hf⟩ := hpre.paramScale
    refine ⟨bits, hb, ?_, hf⟩
    have := key (ha.p15.symm.trans hp)
    show dt.pro.x15.toNat % 2 ^ 32 = bits
    rw [this]
    omega
  · show dt.pro.x17.toNat % 2 ^ 32 = _
    rw [key (ha.p17.symm.trans hpre.paramStrideRel)]
    omega
  · show dt.pro.x25.toNat % 2 ^ 32 = _
    rw [key (ha.p25.symm.trans hpre.paramNTok)]
    omega
  · exact key (ha.p6.symm.trans hpre.paramRel)
  · exact key (ha.p10.symm.trans hpre.paramO)
  · exact key (ha.p11.symm.trans hpre.paramLse)

theorem iters_lt (P : Params) (r s : Nat) (hpos : 0 < P.splits) :
    P.numIters r s < P.blocks r + 1 := by
  unfold Params.numIters
  rw [Nat.div_lt_iff_lt_mul hpos]
  have : P.blocks r ≤ P.blocks r * P.splits := Nat.le_mul_of_pos_right _ hpos
  have e : (P.blocks r + 1) * P.splits = P.blocks r * P.splits + P.splits := by ring
  omega

theorem iters_mul_le (P : Params) (r s : Nat) :
    P.numIters r s * P.splits ≤ P.blocks r - s + (P.splits - 1) :=
  Nat.div_mul_le_self _ _

/-- The numbers of `entOf` are in the ranges `Sm.Ent.Ok` asks for.

Premises beyond those of `live_eq`: the Tensor Memory base is a 32-bit word (`htm`), and the
launch has a token (`0 < P.nTok`), which gives `num_splits < 2 ^ 21` through `Pre.outRange`; the
last range of `Ent.Ok` (`blk`: every block number of the loop is below `2 ^ 31`) needs it. `Pre`
alone does not give `blk` when `num_tokens = 0` and `num_splits` is near `2 ^ 31`. -/
theorem entOk (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hm : ProA.WordsMatch P (ProA.cta L g .z) dt) (htm : dt.pro.tm + 512 ≤ 2 ^ 16)
    (hn : 0 < P.nTok) : (entOf P L g dt).Ok := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hb := ProA.bnd_of_pre hpre hz hm
  have hq := hpre.qLenLe _ hz
  have hqs := hpre.qLenSeq _ hz
  have hsr := hpre.seqRange _ hz
  have hspl := hpre.splitsRange
  have hpos := hpre.splitsPos
  have hout := hpre.outRange
  have hit := iters_lt P (ProA.cta L g .z) (ProA.cta L g .x) hpos
  have hmul := iters_mul_le P (ProA.cta L g .z) (ProA.cta L g .x)
  have hbl : P.blocks (ProA.cta L g .z) < 2 ^ 24 := by
    unfold Params.blocks; omega
  have hsn : P.splits ≤ P.splits * P.nTok := Nat.le_mul_of_pos_right _ hn
  have hh : P.splits * P.nTok ≤ P.splits * P.nTok * heads * headDim := by
    simp only [heads, headDim]; omega
  have hsm : P.splits < 2 ^ 21 := by
    simp only [heads, headDim] at hout; omega
  have hqL : P.qLen (ProA.cta L g .z) ≤ 10 := hq
  have hqS : P.qLen (ProA.cta L g .z) ≤ P.seqK (ProA.cta L g .z) := hqs
  have hcu : P.qStart (ProA.cta L g .z) < 2 ^ 31 := by
    obtain ⟨c0, c1, -, -⟩ := hb
    rw [← hm.cu0]; omega
  have hr25 : P.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 31 := by omega
  have hqz : P.qStart (ProA.cta L g .z) ≤ P.nTok :=
    (qStart_mono hpre (r := ProA.cta L g .z) (r' := P.b) (by omega) (Nat.le_refl _)).trans
      hpre.cuEnd
  have hnt := hpre.nTokRange
  refine ⟨by show dt.pro.tm < 2 ^ 32; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, htm, ?_, ?_, ?_⟩
  · show ProA.cta L g .x < 2 ^ 32
    exact cta_x_lt hpre hg
  · show P.qLen (ProA.cta L g .z) < 2 ^ 31
    omega
  · show P.past (ProA.cta L g .z) < 2 ^ 32
    unfold Params.past; omega
  · show P.nBias (ProA.cta L g .z) < 2 ^ 31
    unfold Params.nBias Params.past; omega
  · show P.blocks (ProA.cta L g .z) * 128 < 2 ^ 32
    omega
  · show P.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 32
    omega
  · show P.numIters (ProA.cta L g .z) (ProA.cta L g .x) =
      if P.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 31 then
        P.numIters (ProA.cta L g .z) (ProA.cta L g .x) else 0
    simp only [hr25, ↓reduceIte]
  · show ProA.cta L g .y * 6 < 2 ^ 32
    simp only [kvHeads] at hy; omega
  · show P.qStart (ProA.cta L g .z) < 2 ^ 32
    omega
  · show dt.pro.x17.toNat % 2 ^ 32 < 2 ^ 32
    exact Nat.mod_lt _ (by norm_num)
  · show P.splits < 2 ^ 32
    omega
  · exact dt.pro.x6.isLt
  · obtain ⟨⟨bits, hb32, hbits, hf⟩, -⟩ := entOf_params hpre ha
    show valFloat .f32 (b32 (entOf P L g dt).scb) = .ok P.scale
    rw [hbits]
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hf
    rw [valFloat_b32 (by omega) hq, ← hqe]
  · exact hpre.scalePos
  · show ProA.cta L g .x + P.numIters (ProA.cta L g .z) (ProA.cta L g .x) * P.splits +
      P.splits < 2 ^ 31
    simp only [Params.blocks] at hmul
    simp only [Params.blocks] at hbl
    omega
  · exact Nat.mod_lt _ (by norm_num)
  · exact dt.pro.x10.isLt
  · exact dt.pro.x11.isLt
  · show ProA.cta L g .x < P.splits
    exact hx
  · show P.qStart (ProA.cta L g .z) ≤ (entOf P L g dt).ntok
    rw [(entOf_params hpre ha).2.2.1]
    omega
  · show ProA.cta L g .y * 6 ≤ 6
    simp only [kvHeads] at hy; omega
  · show (P.splits * (entOf P L g dt).ntok + 11) * 12 * 128 ≤ 2 ^ 31
    rw [(entOf_params hpre ha).2.2.1, Nat.mod_eq_of_lt (by omega)]
    have := hpre.outRangeSlack
    simp only [heads, headDim] at this
    exact this
  · have := hpre.relAlign
    rw [(entOf_params hpre ha).2.2.2.1]
    omega
  · have := hpre.oAlign
    rw [(entOf_params hpre ha).2.2.2.2.1]
    omega
  · have := hpre.lseAlign
    rw [(entOf_params hpre ha).2.2.2.2.2]
    omega
  · intro i hi
    show (ProA.cta L g .x + i * P.splits) * 128 + 256 < 2 ^ 31
    have hi' : i < P.numIters (ProA.cta L g .z) (ProA.cta L g .x) := hi
    unfold Params.numIters at hi'
    have h := (Nat.le_div_iff_mul_le hpos).1 (Nat.succ_le_of_lt hi')
    rw [Nat.succ_mul] at h
    simp only [Params.blocks] at h
    omega
  · show P.past (ProA.cta L g .z) + 64 + 64 < 2 ^ 31
    unfold Params.past; omega
  · show P.past (ProA.cta L g .z) / 128 < 2 ^ 31
    unfold Params.past; omega

/-- The first state's facts are the prologue's exit facts: the same 29 registers with the same
values. -/
theorem factsAt_eq (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hs : dt.pro.w71 = P.splits) (hm : ProA.WordsMatch P (ProA.cta L g .z) dt)
    (hp3 : dt.pro.rest 3 = .pred (decide (g % L.block < 32))) (hw : dt.w = b32 dt.pro.tm) :
    Sm.factsAt L g Flow.setMaxReg_1 (d0 (entOf P L g dt)) = ProA.exitFacts L g dt := by
  unfold Sm.factsAt ProA.exitFacts ProA.factsAt Flow.factsFrom
  refine List.map_congr_left fun r hr => ?_
  rw [live_eq hpre hg ha hs hm hp3 hw r hr]

/-- **The first state satisfies the softmax region's invariant.** -/
theorem inv_d0 (hpre : Pre P L mem0) (hg : g < L.threads) (ha : ProA.ArgsOk L g dt.pro)
    (hm : ProA.WordsMatch P (ProA.cta L g .z) dt) (htm : dt.pro.tm + 512 ≤ 2 ^ 16)
    (hn : 0 < P.nTok) : Sm.Inv L g (d0 (entOf P L g dt)) where
  tid := ha.tid
  ok := entOk hpre hg ha hm htm hn
  i := Nat.zero_le _
  cwPre := fun k h => by cases h
  cwNxt := fun k h => by cases h
  loop := ⟨fun _ h => Sm.Site.noConfusion h, fun h => Sm.Site.noConfusion h⟩
  wb := fun _ => rfl
  vb := fun _ => rfl
  start := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  late := fun h => by cases h
  lead := fun h => Sm.Site.noConfusion h
  lb := rfl
  four := ⟨by
      show Assumption.readEReal .f32 (b32 0) = some (.ok ((0 : ℝ) : EReal))
      exact readEReal_of_valFloat valFloat_z0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  bw := Or.inl rfl
  wf := fun _ => Or.inr rfl
  vf := fun _ => Or.inr rfl
  re := fun _ => ⟨by
      show Assumption.readEReal .f32 (b32 0) = some (.ok ((0 : ℝ) : EReal))
      exact readEReal_of_valFloat valFloat_z0, Or.inr rfl, Or.inr rfl, fun _ => rfl,
    by simp [d0]⟩

end ProASide

end
end PTX.Kernels.InklingRelDecode.Proof.SmEntry
