-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Assumptions
public import Kernels.FlashAttn4Fwd.Flow.Sites
public import Kernels.FlashAttn4Fwd.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.ParamObject

@[expose] public section

/-! # What every role of a thread shares

The assumptions every site machine of the kernel evaluates under (`asms`), a thread's place in
the launch (`ctaOf`, `warpOf`, `rankOf`, `clusterOf`) and the launch data the prologue reads
from the kernel's parameters: `seqlen_k` (`skOf`, the first word of `param_1`), the two divmod
objects (`param_11` for the query blocks, `param_12` for the heads: divisor, multiplier and the
two shift bytes) and the item count (`totOf`, `param_13`). They are functions of the launch, so
that every value table depends on the launch and the thread only; `Pre` relates them to the
parameters of the specification (`skOf_eq`, `totOf_eq`, `divmod_eq`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The assumptions every site machine evaluates under. A new kernel assumption (approximate
`ex2`/`rcp`, the peer-mbarrier bit) is added here, once, for every role. -/
abbrev asms : List Assumption := Assumptions.all

/-- No assumption has a local rule for an operation that is no floating or approximate form: the
core rule applies. -/
theorem asms_localRule_none {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hf : Assumption.FloatForm.ofOp op = none := by simp [Assumption.FloatForm.ofOp])
    (ha : Assumption.ApproxForm.ofOp op = none := by simp [Assumption.ApproxForm.ofOp]) :
    ∀ a ∈ asms, a.localRule L g t op = none := by
  intro a ha'
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none fun f h => by rw [hf] at h; cases h
  · rfl
  · exact Assumption.approxExact_localRule_none fun f h => by rw [ha] at h; cases h
  all_goals rfl

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-! ### A thread's place in the launch -/

/-- The thread's CTA. -/
def ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- The thread's warp within its CTA. -/
def warpOf (L : Launch) (g : Nat) : Nat := g % L.block / 32

/-- The thread's rank within its cluster (`%cluster_ctarank`). -/
def rankOf (L : Launch) (g : Nat) : Nat := L.rankOfCta (ctaOf L g)

/-- The thread's cluster (`%clusterid.x`): the first work item of its CTA pair. -/
def clusterOf (L : Launch) (g : Nat) : Nat := L.clusterOfCta (ctaOf L g)

theorem sreg_cluster (hpre : Pre P L mem0) {g : Nat} :
    sregValue L g ⟨.clusterid, some .x⟩ = some (clusterOf L g) := by
  simp [sregValue, ctaOf, clusterOf, Launch.oneDim_clusteridOf hpre.oneDimLaunch.1, Dim3.get]

/-! ### Launch data read from the parameters -/

/-- `seqlen_k`: the first word of `param_1`, the K tensor object. -/
def skOf (L : Launch) : Nat := paramNat L (param "1") 0 4

/-- Word `k` (`k < 2`) of the divmod object `param_i` (divisor, multiplier). -/
def divWord (L : Launch) (i : String) (k : Nat) : Nat := paramNat L (param i) (4 * k) 4

/-- Shift byte `k` (`k < 2`) of the divmod object `param_i`. -/
def divShift (L : Launch) (i : String) (k : Nat) : Nat := paramNat L (param i) (8 + k) 1

/-- `total_blocks_cluster` (`param_13`): the work items of the grid. -/
def totOf (L : Launch) : Nat := ((L.params (param "13")).getD 0).toNat

/-! ### What the precondition says about them -/

theorem warpOf_lt (hpre : Pre P L mem0) (g : Nat) : warpOf L g < 16 := by
  have := Nat.mod_lt g (show 0 < L.block by rw [hpre.block]; decide)
  unfold warpOf
  rw [hpre.block] at this ⊢
  omega

theorem rankOf_eq (hpre : Pre P L mem0) (g : Nat) : rankOf L g = ctaOf L g % 2 := by
  simp [rankOf, ctaOf, Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]

theorem clusterOf_eq (hpre : Pre P L mem0) (g : Nat) : clusterOf L g = ctaOf L g / 2 := by
  simp [clusterOf, ctaOf, Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]

theorem cta_lt {g : Nat} (hg : g < L.threads) : ctaOf L g < L.grid := by
  unfold ctaOf Launch.threads at *
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)

/-- Four parameter bytes holding the little-endian bytes of `x` form `x` modulo `2 ^ 32`. -/
theorem paramNat_four {name : String} {off x : Nat}
    (h : ∀ k < 4, L.paramBytes name (off + k) = some (leByte x k)) :
    paramNat L name off 4 = x % 2 ^ 32 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [paramNat, h0, h1, show off + 1 + 1 = off + 2 by omega,
    h2, show off + 2 + 1 = off + 3 by omega, h3, Option.getD_some, leByte, BitVec.toNat_ofNat]
  omega

theorem skOf_eq (hpre : Pre P L mem0) : skOf L = P.sk := by
  rw [skOf, paramNat_four (x := P.sk) (fun k hk => by simpa using hpre.paramSeqK k hk)]
  exact Nat.mod_eq_of_lt (by have := hpre.skRange; omega)

/-- The launch supplies the bytes of `param_1` the kernel reads. -/
theorem supplied_sk (hpre : Pre P L mem0) : ParamSupplied L (param "1") 0 4 :=
  fun k hk => ⟨_, hpre.paramSeqK (0 + k) (by omega)⟩

/-- The launch supplies the ten bytes of `param_11` the kernel reads. -/
theorem supplied_block (hpre : Pre P L mem0) {off n : Nat} (h : off + n ≤ 10) :
    ParamSupplied L (param "11") off n :=
  fun k hk => ⟨_, hpre.paramBlockDivmod (off + k) (by omega)⟩

/-- The launch supplies the ten bytes of `param_12` the kernel reads. -/
theorem supplied_head (hpre : Pre P L mem0) {off n : Nat} (h : off + n ≤ 10) :
    ParamSupplied L (param "12") off n :=
  fun k hk => ⟨_, hpre.paramHeadDivmod (off + k) (by omega)⟩

theorem clusterOf_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) :
    clusterOf L g < P.clusters := by
  have h := cta_lt hg
  rw [clusterOf_eq hpre, hpre.grid] at *
  omega

theorem clusters_le (hpre : Pre P L mem0) : P.clusters ≤ 2 ^ 31 := by
  have := hpre.scheduleRange
  omega

theorem totOf_eq (hpre : Pre P L mem0) : totOf L = P.items % 2 ^ 64 := by
  simp [totOf, hpre.paramItems, BitVec.toNat_ofNat]

theorem totOf_lt (hpre : Pre P L mem0) : totOf L < 2 ^ 31 := by
  rw [totOf_eq hpre]
  have := hpre.scheduleRange
  have := hpre.clustersPos
  omega

theorem params_tot (hpre : Pre P L mem0) :
    L.params (param "13") = some (BitVec.ofNat 64 (totOf L)) := by
  rw [hpre.paramItems, totOf_eq hpre]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

end

/-- Rewrite the special-register values a segment evaluates (`%tid`, `%ntid`, `%ctaid`,
`%clusterid`, `%nclusterid`) to their one-dimensional forms under `Pre` (`Launch.oneDim_*`). -/
syntax "launch_norm" term:max : tactic
macro_rules
  | `(tactic| launch_norm $hpre) => `(tactic|
      simp only [Launch.oneDim_tidOf ($hpre).oneDimLaunch.1, ($hpre).oneDimLaunch.1.1,
        Launch.oneDim_ctaidOf ($hpre).oneDimLaunch.1,
        Launch.oneDim_clusteridOf ($hpre).oneDimLaunch.1,
        Launch.oneDim_nclusteridOf ($hpre).oneDimLaunch.1, Dim3.get])

end PTX.Kernels.FlashAttn4Fwd.Proof
