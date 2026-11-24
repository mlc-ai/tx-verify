-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The parameters the warp loads, by their names in the code. -/
def ps (p : Params) : List (String × Nat) :=
  [("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_17", p.heads),
   ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_19", p.batch),
   ("kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
      ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
      ptrbf16gmemalign16o1i64div8_0_param_22", 800)]

theorem param17 : param 17 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
    ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
    ptrbf16gmemalign16o1i64div8_0_param_17" := by
  have h : toString (17 : Nat) = "17" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (17 / 10 : Nat) = 1 by decide, show (17 % 10 : Nat) = 7 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 7) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_seven.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

theorem param19 : param 19 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
    ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
    ptrbf16gmemalign16o1i64div8_0_param_19" := by
  have h : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

theorem param22 : param 22 =
    "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_ob\
    ject_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensor\
    ptrbf16gmemalign16o1i64div8_0_param_22" := by
  have h : toString (22 : Nat) = "22" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (22 / 10 : Nat) = 2 by decide, show (22 % 10 : Nat) = 2 by decide,
      Nat.repr_of_lt (n := 2) (by decide), Nat.digitChar_eq_two.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

theorem params {p : Params} {L : Launch} {m : Mem0} (hp : Pre p L m) :
    explicitParams L (ps p) = L :=
  explicitParams_eq fun n v h => by
    simp only [ps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← param17]; exact (hp.values (17, p.heads) (by simp [Params.scalarWords])).2
    · rw [← param19]; exact (hp.values (19, p.batch) (by simp [Params.scalarWords])).2
    · rw [← param22]; exact (hp.values (22, 800) (by simp [Params.scalarWords])).2

/-- The role's segments. -/
macro "ep_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- The CTA index plus one does not overflow: the scan's back edge after the last group is not
taken. -/
theorem cta_succ_le (hp : Pre p L m) (hg : g < L.threads) :
    scmp .le .s (addi (ctaW L g) 1) (ctaW L g) = false := by
  have hb := hp.block
  have hgr := hp.grid
  have hc : g / L.block < 2 ^ 31 - 1 := by
    simp only [Launch.threads] at hg
    rw [hb] at hg ⊢
    have : g / 512 < L.grid := by omega
    omega
  simp only [scmp, addi, r32, i32, ctaW, truncBits, PTX.compare, toSigned, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt]
  generalize g / L.block = c at hc ⊢
  have h1 : (1 % ((2 ^ 64 : ℕ) : ℤ)).toNat = 1 := by norm_num
  rw [h1]
  have hc' : c < 2 ^ 31 := by omega
  simp only [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show c + 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c + 1 < 2 ^ 32 by omega),
    show (1 : Nat) % 2 ^ 32 = 1 from rfl, show (1 : Nat) % 2 ^ 64 = 1 from rfl,
    show 2 ^ (32 - 1) = 2 ^ 31 from rfl, show c < 2 ^ 31 from hc', show c + 1 < 2 ^ 31 by omega,
    ite_true]
  simp

macro_rules | `(tactic| sym_decide) => `(tactic| exact cta_succ_le ‹_› ‹_›)

/-- No assumption of the kernel gives an integer instruction a rule of its own. -/
theorem asms_int_none {L : Launch} {g pc : Nat} (i : IntInstr) :
    NoRuleAt Assumptions.all L g pc (.int i) := by
  intro t _ a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

macro_rules | `(tactic| sym_local_none) => `(tactic| exact asms_int_none _)

/-- No assumption takes a segment at a program counter outside the software `exp2` sites. -/
theorem segFree {pc : Nat} (h : pc ∉ Assumptions.swExp2Sites) :
    Assumption.SegFreePc Assumptions.all pc := by
  intro a ha L g t ht
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (simp only [Assumptions.swExp2, ht]
       exact ite_eq_right (fun hm => h (List.elem_iff.mp hm.1)))

macro_rules | `(tactic| sym_seg_free) => `(tactic| exact segFree (by decide))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
