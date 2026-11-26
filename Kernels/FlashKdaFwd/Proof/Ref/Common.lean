-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Spec
public import Kernels.FlashKdaFwd.Proof.Thread.Base
public import Lemmas.Cluster.Unit
public import Lemmas.Flow.Arith32Norm
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # Index facts of a thread, under the launch part of the precondition

The generated thread machine (`Proof/Thread/`) transliterates the code: its register file holds
the terms the instructions compute from the launch (`sreg ((L.tidOf g).get .x)`,
`paramBits L 15`, `sreg L.sharedBase`, …) and it derives nothing. The reference layer
(`Proof/Ref/`) states what these terms *are* for the launch that `Pre` describes. This file is
the part every phase of the program needs:

* the position of a thread: its index in its thread block (`tid g = g % 192`), its warp
  (`warp g`, 32 threads each, six per block), its lane in the warp (`lane g`), its thread block
  (`cta g = g / 192`; "CTA" is NVIDIA's word for a thread block), and the sequence and the head
  that this block works on (`seqOf`, `headOf`: the grid is `(sequences, heads, 1)`, so block `c`
  has `%ctaid.x = c % sequences` and `%ctaid.y = c / sequences`);
* the words the special registers read, as words of these numbers (`W n` is the 64-bit word of
  the number `n`, the normal form of `Lemmas/Flow/Arith32Word.lean`): `tidWord`, `ctaidX`,
  `ctaidY`, `clusterRank`, `sharedWord`;
* the scalar parameters in the form the machine uses (`paramBits L i`): `paramBits_15`;
* the comparisons of the thread index that decide the role of a thread, as decided
  propositions: `tid_lt128`, `tid_lt160`, `tid_and224`.

Role classes: the *compute* threads are `tid g < 128` (warps 0 to 3), the *load* warp is
`128 ≤ tid g < 160` (warp 4), the *store* warp is `160 ≤ tid g` (warp 5).

Every lemma takes the precondition `Pre P L mem0` and reads only its launch fields (`block`,
`ntid`, `grid`, `nclusters`, `clusterPlaces`, `sharedBase`, `sharedRange`, the parameters and
the ranges); none reads the memory. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

/-! ### Positions -/

/-- The index of thread `g` in its thread block (`%tid.x`). -/
def tid (g : Nat) : Nat := g % 192
/-- The warp of thread `g` in its thread block: 0 to 3 compute, 4 loads, 5 stores. -/
def warp (g : Nat) : Nat := g % 192 / 32
/-- The lane of thread `g` in its warp. -/
def lane (g : Nat) : Nat := g % 192 % 32
/-- The thread block ("CTA") of thread `g`. -/
def cta (g : Nat) : Nat := g / 192
/-- The sequence the thread block of `g` works on (`%ctaid.x`). -/
def seqOf (P : Params) (g : Nat) : Nat := g / 192 % P.sequences
/-- The head the thread block of `g` works on (`%ctaid.y`). -/
def headOf (P : Params) (g : Nat) : Nat := g / 192 / P.sequences

theorem tid_lt (g : Nat) : tid g < 192 := Nat.mod_lt _ (by decide)
theorem warp_lt (g : Nat) : warp g < 6 := by unfold warp; omega
theorem lane_lt (g : Nat) : lane g < 32 := Nat.mod_lt _ (by decide)
theorem tid_eq (g : Nat) : tid g = 32 * warp g + lane g := by unfold tid warp lane; omega

/-- The role classes by warp: compute threads are the warps 0 to 3. -/
theorem warp_lt4_iff (g : Nat) : warp g < 4 ↔ tid g < 128 := by unfold warp tid; omega
theorem warp_eq4_iff (g : Nat) : warp g = 4 ↔ 128 ≤ tid g ∧ tid g < 160 := by
  unfold warp tid; omega
theorem warp_eq5_iff (g : Nat) : warp g = 5 ↔ 160 ≤ tid g := by
  have := tid_lt g
  unfold warp tid at *; omega
theorem warp_eq0_iff (g : Nat) : warp g = 0 ↔ tid g < 32 := by unfold warp tid; omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A launched thread is in a thread block of the grid. -/
theorem cta_lt (hpre : Pre P L mem0) (hg : g < L.threads) : cta g < P.sequences * P.heads := by
  unfold Launch.threads at hg
  rw [hpre.block, hpre.grid] at hg
  unfold cta
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hg)

theorem seqOf_lt (hpre : Pre P L mem0) (g : Nat) : seqOf P g < P.sequences :=
  Nat.mod_lt _ hpre.sequencesPos

theorem headOf_lt (hpre : Pre P L mem0) (hg : g < L.threads) : headOf P g < P.heads := by
  have h := cta_lt hpre hg
  unfold headOf
  unfold cta at h
  exact Nat.div_lt_of_lt_mul h

/-- The thread block of `g` is block `seq + sequences * head` of the grid. -/
theorem cta_eq (P : Params) (g : Nat) : cta g = seqOf P g + P.sequences * headOf P g := by
  unfold cta seqOf headOf
  exact (Nat.mod_add_div _ _).symm

/-- The plane `H * seq + head` of the state arrays (`mad.lo.s32` at instruction 328). -/
theorem plane_lt (hpre : Pre P L mem0) (hg : g < L.threads) :
    P.heads * seqOf P g + headOf P g < P.sequences * P.heads := by
  have h1 := seqOf_lt hpre g
  have h2 := headOf_lt hpre hg
  calc P.heads * seqOf P g + headOf P g < P.heads * seqOf P g + P.heads := by omega
    _ = P.heads * (seqOf P g + 1) := by ring
    _ ≤ P.heads * P.sequences := Nat.mul_le_mul_left _ h1
    _ = P.sequences * P.heads := Nat.mul_comm _ _

/-! ### What the launch gives each thread -/

theorem block_div (hpre : Pre P L mem0) : g / L.block = cta g := by rw [hpre.block]; rfl

theorem block_mod (hpre : Pre P L mem0) : g % L.block = tid g := by rw [hpre.block]; rfl

/-- `%tid.x` is the thread's index in its block. -/
theorem tid_x (hpre : Pre P L mem0) : (L.tidOf g).get .x = tid g := by
  simp [Launch.tidOf, Dim3.coord, Dim3.get, hpre.ntid, hpre.block, tid]

/-- The lane of Core (`laneOf`), which elections and shuffles use. -/
theorem laneOf_eq (hpre : Pre P L mem0) : laneOf L g = lane g := by
  simp [laneOf, hpre.block, lane]

/-- Every cluster of the launch is one thread block. -/
theorem unitClusters (hpre : Pre P L mem0) : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
  intro k
  rw [hpre.clusterPlaces]
  rfl

theorem cta_lt_nclusters (hpre : Pre P L mem0) (hg : g < L.threads) :
    g / L.block < L.nclusters := by
  rw [hpre.nclusters, hpre.grid, block_div hpre]
  exact cta_lt hpre hg

/-- `%cluster_ctarank` is 0: a thread block is its own cluster. -/
theorem rank_zero (hpre : Pre P L mem0) (hg : g < L.threads) : L.rankOfCta (g / L.block) = 0 :=
  Launch.rankOfCta_unit (unitClusters hpre) (cta_lt_nclusters hpre hg)

/-- `%ctaid.x` is the sequence. -/
theorem ctaid_x (hpre : Pre P L mem0) (hg : g < L.threads) :
    (L.ctaidOf (g / L.block)).get .x = seqOf P g := by
  have hc := Launch.clusterOfCta_unit (unitClusters hpre) (cta_lt_nclusters hpre hg)
  have hr := rank_zero hpre hg
  rw [hpre.block] at hc hr
  simp [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, hc, hr, hpre.clusterPlaces,
    gridPlace, Dim3.coord, Dim3.get, hpre.block, seqOf]

/-- `%ctaid.y` is the head. -/
theorem ctaid_y (hpre : Pre P L mem0) (hg : g < L.threads) :
    (L.ctaidOf (g / L.block)).get .y = headOf P g := by
  have hc := Launch.clusterOfCta_unit (unitClusters hpre) (cta_lt_nclusters hpre hg)
  have hr := rank_zero hpre hg
  have hh := headOf_lt hpre hg
  rw [hpre.block] at hc hr
  simp only [headOf] at hh
  simp [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, hc, hr, hpre.clusterPlaces,
    gridPlace, Dim3.coord, Dim3.get, hpre.block, headOf, Nat.mod_eq_of_lt hh]

/-! ### The words of the register file -/

/-- A special register's word is the word of its number. -/
theorem sreg_W {n : Nat} (h : n < 2 ^ 32) : sreg n = W n := by
  show truncBits 32 (BitVec.ofNat 64 n) = W n
  exact r32_W h

/-- The word of `%tid.x` (register `%r1`, written at instruction 13). -/
theorem tidWord (hpre : Pre P L mem0) : sreg ((L.tidOf g).get .x) = W (tid g) := by
  rw [tid_x hpre]
  exact sreg_W (by have := tid_lt g; omega)

/-- The word of the warp index `%tid.x >> 5` (register `%r2`, instruction 14). -/
theorem warpWord : shru (W (tid g)) 5 = W (warp g) := by
  have := tid_lt g
  rw [shru_int (by omega) (by decide) (by decide)]
  rfl

/-- The word of `%ctaid.x` (register `%r3`, instruction 111). -/
theorem ctaidX (hpre : Pre P L mem0) (hg : g < L.threads) :
    sreg ((L.ctaidOf (g / L.block)).get .x) = W (seqOf P g) := by
  rw [ctaid_x hpre hg]
  exact sreg_W (by have := seqOf_lt hpre g; have := hpre.sequencesLt; omega)

/-- The word of `%ctaid.y` (register `%r4`, instruction 112). -/
theorem ctaidY (hpre : Pre P L mem0) (hg : g < L.threads) :
    sreg ((L.ctaidOf (g / L.block)).get .y) = W (headOf P g) := by
  rw [ctaid_y hpre hg]
  exact sreg_W (by have := headOf_lt hpre hg; have := hpre.headsLt; omega)

/-- The word of `%cluster_ctarank` (register `%r46`, instruction 86). -/
theorem clusterRank (hpre : Pre P L mem0) (hg : g < L.threads) :
    sreg (L.rankOfCta (g / L.block)) = W 0 := by
  rw [rank_zero hpre hg]
  rfl

/-- The shared window the kernel uses ends below `2 ^ 18`. -/
theorem shared_lt (hpre : Pre P L mem0) : P.sharedBase + 98392 ≤ 2 ^ 18 := hpre.sharedRange

/-- The word of `shared_mem`, the base address of the block's shared memory. -/
theorem sharedWord (hpre : Pre P L mem0) : sreg L.sharedBase = W P.sharedBase := by
  rw [hpre.sharedBase]
  exact sreg_W (by have := shared_lt hpre; omega)

/-- A shared address `shared_mem + off` computed by `add.s32` (offsets below `2 ^ 17`). -/
theorem sharedAddr (hpre : Pre P L mem0) {off : Nat} (ho : off ≤ 98392) :
    addi (W P.sharedBase) (off : Int) = W (P.sharedBase + off) := by
  have := shared_lt hpre
  exact addi_W (by omega) (by omega)

/-- The scalar parameter 15 (`cu_seqlens`, loaded at instruction 11) in the machine's form. -/
theorem paramBits_15 (hpre : Pre P L mem0) : paramBits L 15 = W P.offsetsBase := by
  rw [paramBits, paramName_15, hpre.paramOffsets]
  rfl

/-- The address of the offsets array is a 64-bit number. -/
theorem offsets_lt (hpre : Pre P L mem0) : P.offsetsBase + 8 * (P.sequences + 1) ≤ 2 ^ 64 :=
  hpre.offsetsRange

/-- The word of the pointer `cu_seqlens` (register `%rd1`: `cvta.to.global.u64` of the
parameter, instructions 11 and 12). -/
theorem offsetsWord (hpre : Pre P L mem0) : r64 (r64 (paramBits L 15)) = W P.offsetsBase := by
  rw [paramBits_15 hpre]
  apply BitVec.eq_of_toNat_eq
  simp [r64, truncBits, W]

/-! ### The comparisons that decide the role -/

/-- `setp.lt.u32 %p4, %r1, 128` (instruction 15): the thread is a compute thread. -/
theorem tid_lt128 : scmpi .lt .u (W (tid g)) 128 = decide (tid g < 128) := by
  have := tid_lt g
  rw [scmpi_lt_u_W (by omega) (by decide) (by decide)]
  rfl

/-- `setp.lt.u32 %p5, %r1, 160` (instruction 16): the thread is not in the store warp. -/
theorem tid_lt160 : scmpi .lt .u (W (tid g)) 160 = decide (tid g < 160) := by
  have := tid_lt g
  rw [scmpi_lt_u_W (by omega) (by decide) (by decide)]
  rfl

/-- The numbers below 192 with `n &&& 224 = 128` are those of warp 4. -/
theorem and224 : ∀ n < 192, (n &&& 224 = 128) = (n / 32 = 4) := by decide +kernel

/-- `and.b32 %r188, %r1, 224` and `setp.ne.b32 %p25, %r188, 128` (instructions 316 and 317):
the thread is outside the load warp. -/
theorem tid_and224 : scmpi .ne .b (andi (W (tid g)) 224) 128 = decide (warp g ≠ 4) := by
  have hlt := tid_lt g
  have h1 : andi (W (tid g)) 224 = W (tid g &&& 224) := by
    apply BitVec.eq_of_toNat_eq
    have h2 : tid g &&& 224 < 2 ^ 64 := lt_of_le_of_lt Nat.and_le_left (by omega)
    have h4 : tid g % 4294967296 = tid g := Nat.mod_eq_of_lt (by omega)
    have h5 : tid g % 18446744073709551616 = tid g := Nat.mod_eq_of_lt (by omega)
    simp [andi, r32, i32, truncBits, W, h4, h5]
  have h3 : tid g &&& 224 < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_left (by omega)
  rw [h1, scmpi_ne_b_W h3 (by decide) (by decide)]
  have h := and224 (tid g) hlt
  have hiff : (tid g &&& 224 ≠ Int.toNat 128) ↔ warp g ≠ 4 := by
    show ¬ (tid g &&& 224 = 128) ↔ ¬ (tid g / 32 = 4)
    rw [h]
  exact decide_eq_decide.mpr hiff

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
