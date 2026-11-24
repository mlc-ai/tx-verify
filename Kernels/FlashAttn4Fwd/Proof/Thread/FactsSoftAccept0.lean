-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAcceptBase

@[expose] public section

/-! # The first tile's row maximum accepts single-precision words (runs 1-3)

Each read run of the first tile's row maximum is accepted when the words are single-precision
numbers (`rCond_of_rTy`): the shapes of the registers it reads first (`tys_*`) hold, and its
shape check succeeds. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The shapes of the registers `readsMax0_1341` reads first. -/
def tys_1341 : List (Nat × RTy) :=
  [(1008, .bits (BitVec.ofNat 64 4294967295)), (4106, .f32x2), (4105, .f32x2), (4104, .f32x2),
   (4103, .f32x2), (3945, .f32x2), (3946, .f32x2), (3947, .f32x2), (3948, .f32x2),
   (3949, .f32x2), (3950, .f32x2), (3951, .f32x2), (3952, .f32x2), (3953, .f32x2),
   (3954, .f32x2), (3955, .f32x2), (3956, .f32x2)]

theorem accept_1341 {L : Launch} {g : Nat} {d : D}
    (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    rCond (valueEx (valueOf L g d) (exMax0_1341 L d)) readsMax0_1341 := by
  refine rCond_of_rTy (T := tyOf tys_1341) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tys_1341, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some, exMax0_1341]
  all_goals first
    | exact has_join (hf _ (by norm_num)) (hf _ (by norm_num))
    | rfl

/-- The shapes of the registers `readsMax0_1455` reads first. -/
def tys_1455 : List (Nat × RTy) :=
  [(1011, .bits (BitVec.ofNat 64 4294967295)), (3957, .f32x2), (3958, .f32x2), (3959, .f32x2),
   (3960, .f32x2), (3961, .f32x2), (3962, .f32x2), (3963, .f32x2), (3964, .f32x2),
   (3965, .f32x2), (3966, .f32x2), (3967, .f32x2), (3968, .f32x2), (3969, .f32x2),
   (3970, .f32x2), (3971, .f32x2), (3972, .f32x2)]

theorem accept_1455 {L : Launch} {g : Nat} {d : D}
    (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    rCond (valueEx (valueOf L g d) (exMax0_1455 L d)) readsMax0_1455 := by
  refine rCond_of_rTy (T := tyOf tys_1455) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tys_1455, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some, exMax0_1455]
  all_goals first
    | exact has_join (hf _ (by norm_num)) (hf _ (by norm_num))
    | rfl

/-- The shapes of the registers `readsMax0_1569` reads first. -/
def tys_1569 : List (Nat × RTy) :=
  [(1013, .bits (BitVec.ofNat 64 4294967295)), (3973, .f32x2), (3974, .f32x2), (3975, .f32x2),
   (3976, .f32x2), (3977, .f32x2), (3978, .f32x2), (3979, .f32x2), (3980, .f32x2),
   (3981, .f32x2), (3982, .f32x2), (3983, .f32x2), (3984, .f32x2), (3985, .f32x2),
   (3986, .f32x2), (3987, .f32x2), (3988, .f32x2)]

theorem accept_1569 {L : Launch} {g : Nat} {d : D}
    (hf : ∀ k < 128, RTy.Has .f32 (d.w k)) :
    rCond (valueEx (valueOf L g d) (exMax0_1569 L d)) readsMax0_1569 := by
  refine rCond_of_rTy (T := tyOf tys_1569) (all_tyOf fun p hp => ?_) (by decide +kernel)
  simp only [tys_1569, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [valueEx, valueOf, ctrlValues, PTX.Flow.lookupLit,
    Option.getD_some, exMax0_1569]
  all_goals first
    | exact has_join (hf _ (by norm_num)) (hf _ (by norm_num))
    | rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
