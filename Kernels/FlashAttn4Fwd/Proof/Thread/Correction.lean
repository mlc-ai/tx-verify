-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Flow.Widen
public import Lemmas.Flow.MulPairCore
public import Lemmas.Flow.RcpCore
public import Lemmas.Flow.Recip
public import Lemmas.Flow.Polls
public import Lemmas.Arith.FastDivmod

@[expose] public section

/-! # The correction warps as abstract states

Warps 8 to 11 of both CTAs (all lanes; warp `8 + k` serves rows `32 k … 32 k + 31` of both
stages, its thread's row is `ρ = tid % 128`) run lines 4519-5707 of the PTX. After the
register reduction and the start barrier (`bar.sync 2, 416`) a thread gives the leader CTA's
P-ready barriers of both stages (`+144`, `+152`) their first O-free arrival, then for each work
item `i` of its cluster:

* stage 0 and stage 1 synchronize generation 0 of their named barriers (`k + 3`, `k + 7`) with
  the softmax warps, and stage 0 credits its statistics barrier (`+240`);
* `n - 1` loop trips `t`: per stage, a barrier generation, the load of `α` (`+332 + 512 st`), a
  `vote.sync.ballot` of `α < 1` over the warp, and only when some lane voted, the rescale of
  the 128 output columns `256 + 128 st …` in eight chunks of sixteen (`tcgen05.ld`, products
  with `α`, `tcgen05.st`, `tcgen05.wait::st`); then the O-free arrival on the leader and the
  statistics credit of the other stage;
* per stage the last generation: the load of `l`, its credit, the waits for the final
  accumulator (`+192 + 8 st`) and the free staging buffer (`+272 + 8 st`), eight chunks of
  loads, products with `1 / l'`, half-precision packs and two swizzled `st.shared.v4` each, the
  proxy fence, the O-free arrival on the leader and the staged arrival (`+256 + 8 st`).

After its items the thread waits for the last staging buffer to drain (`+280`), arrives on the
end barrier (`bar.arrive 2, 416`) and leaves.

An abstract state is the next event with the item `i`, the loop trip `t`, the last word read
from the statistics slot (`aw`) with a real reading (`a`: `α`, or `1 / l'` after the final
credit) and the sixteen values of the chunk loaded last (`o`). The values are raw
(`tcgen05.ld` and `ld.shared` may return any value). The machine follows every word: the
comparison `α < 1` (`ltOne`), the reciprocal of `l` (`recipV`), the products of a chunk
(`prodV`) and their half-precision words (`fw`) are the evaluator's outcomes on the words read,
the exact reals of the ideal arithmetic (`idealArith`) or exact reciprocal (`approx`) on finite
words and the Core rule's results where those decline (a NaN or an infinity). Only a step that
faults (a word of the wrong width, a read the rules reject) stops the machine (`next` gives
`none`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### Shape of the thread -/

/-- The shared-memory base address. -/
abbrev sb (L : Launch) : Nat := L.sharedBase
/-- The thread's index in the block. -/
abbrev tidOf (L : Launch) (g : Nat) : Nat := g % L.block
/-- The warp's index in the correction group (`w % 4`, `w - 8` for warps 8 to 11). -/
abbrev kOf (L : Launch) (g : Nat) : Nat := tidOf L g / 32 % 4
/-- The thread's lane. -/
abbrev lnOf (L : Launch) (g : Nat) : Nat := tidOf L g % 32
/-- The thread's row of the stage's 128-row tile (`tid & 127`). -/
abbrev rowOf (L : Launch) (g : Nat) : Nat := tidOf L g % 128
/-- The number of clusters (`%nclusterid.x`). -/
def nClusters (L : Launch) : Nat := L.grid / L.clusterSize.val
/-- The number of key-value trips of an item: `ceil (sk / 128)`. -/
def trips (L : Launch) : Nat := (skOf L + 127) / 128
/-- The number of work items of the thread's cluster. -/
def items (L : Launch) (g : Nat) : Nat :=
  StaticSchedule.count (nClusters L) (totOf L) (clusterOf L g)
/-- Work item `i` of the thread's cluster. -/
def work (L : Launch) (g : Nat) (i : Nat) : Nat := clusterOf L g + i * nClusters L

/-- A Tensor Memory address of the warp's lanes at column `col`. -/
abbrev tmem (L : Launch) (g : Nat) (col : Nat) : Nat := 2097152 * kOf L g + col

/-- The staging address of chunk `c` (sixteen bytes) of the thread's row in stage `st`'s
128-byte-swizzled staging tile, without the `+16384` of the second half. Irreducible: the
evaluation of a segment treats it as a number (unfolding its `xor` would recurse on the bits of
a symbolic row). -/
@[irreducible] def stage (L : Launch) (g : Nat) (st c : Nat) : Nat :=
  sb L + 3072 + 32768 * st + 4096 * kOf L g + 128 * lnOf L g + 16 * (lnOf L g % 8 ^^^ c)

/-- The `mapa` of a barrier at offset `off` of the cluster's leader CTA. -/
def leadPtr (L : Launch) (g : Nat) (off : Nat) : Value :=
  .ptr 32 false (.shared (ctaOf L g) (2 * (ctaOf L g / 2))) (BitVec.ofNat 64 (sb L + off))

/-- The 32-bit word of the negative of `x`. -/
abbrev neg32 (x : Nat) : Nat := (2 ^ 32 - x % 2 ^ 32) % 2 ^ 32

/-! ### Outcomes on the words read -/

/-- The `0f` constants `0f3F800000` (`1`) and `0f00000000` (`0`) as values. -/
abbrev one32 : Value := .bits 32 (BitVec.ofNat 64 1065353216)
abbrev zero32 : Value := .bits 32 (BitVec.ofNat 64 0)

/-- The vote's comparison `setp.lt.f32 p, α, 0f3F800000` on the word `v` read as `α`. -/
def ltOneE (v : Value) : Exec Bool := setpE (.ord .lt) false v one32

/-- Its Boolean (`false` where it faults). -/
def ltOne (v : Value) : Bool :=
  match ltOneE v with
  | .ok b => b
  | .error _ => false

/-- The reciprocal of the word `v` read as `l`: `setp.ne.f32 p, l, 0f00000000`,
`selp.f32 s, l, 0f3F800000, p`, `rcp.approx.ftz.f32 r, s`. -/
def recipE (v : Value) : Exec Value := do
  let p ← setpE (.ord .ne) false v zero32
  rcpE true (if p then v else one32)

/-- Its value (`b32 0` where it faults). -/
def recipV (v : Value) : Value := okVal (b32 0) (recipE v)

/-- Every value of the reciprocal has four bytes. -/
theorem recipE_four (v : Value) : Four (recipE v) := by
  intro r hr
  obtain ⟨p, -, hr⟩ := exec_bind_ok hr
  exact rcpE_four true _ r hr

theorem recipV_bytes (v : Value) : (recipV v).bytes = 4 := okVal_bytes (recipE_four v)

/-- On a number `x` the comparison is `x < 1`. -/
theorem ltOneE_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    ltOneE v = .ok (decide (x < 1)) := by
  rw [ltOneE, setpE_fin (Or.inl rfl) hx valFloat_one]
  simp only [Assumption.erealCompare, EReal.coe_lt_coe_iff]

theorem ltOne_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    ltOne v = decide (x < 1) := by
  simp [ltOne, ltOneE_fin hx]

/-- On a number `x` the reciprocal is the exact `1 / x'` (`x' = x`, or `1` if `x = 0`). -/
theorem recipE_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    recipE v = .ok (fl (1 / (if x = 0 then 1 else x))) := by
  have hs : setpE (.ord .ne) false v zero32 = .ok (decide (x ≠ 0)) := by
    rw [setpE_fin (Or.inl rfl) hx valFloat_zero, erealCompare_ne_coe_zero]
  by_cases h0 : x = 0
  · simp only [recipE, hs, h0, ne_eq, not_true_eq_false, decide_false, bind, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    rw [rcpE_fin valFloat_one one_ne_zero]; rfl
  · simp only [recipE, hs, h0, ne_eq, not_false_eq_true, decide_true, bind, Except.bind,
      ↓reduceIte]
    rw [rcpE_fin hx h0]; rfl

theorem recipV_fin {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) :
    recipV v = fl (1 / (if x = 0 then 1 else x)) :=
  okVal_of_ok (recipE_fin hx)

/-- The packed product of pair `q` of the chunk `o` with the pair `c`
(`mov.b64 w, {o[2q], o[2q+1]}`, `mul.rn.f32x2 p, w, c`). -/
def prodV (o : List Value) (c : Value) (q : Nat) : Value :=
  mulOutV .rn false (joinValue (o.getD (2 * q) (b32 0)) (o.getD (2 * q + 1) (b32 0))) c

/-- The sixteen values of a chunk and a pair the code multiplies them with: every pack and
every multiplication succeeds. -/
def chunkOk (o : List Value) (c : Value) : Bool :=
  (List.range 8).all fun q =>
    (o.getD (2 * q) (b32 0)).bytes == 4 && (o.getD (2 * q + 1) (b32 0)).bytes == 4 &&
      (floatE (mul2I .rn false)
        [joinValue (o.getD (2 * q) (b32 0)) (o.getD (2 * q + 1) (b32 0)), c]).toBool

/-- A final chunk: its products, and every conversion of a product to halves, succeed. -/
def finOk (o : List Value) (c : Value) : Bool :=
  chunkOk o c && (List.range 8).all fun q =>
    (cvtPairE (splitValue 64 (prodV o c q)).2 (splitValue 64 (prodV o c q)).1).toBool

/-! ### Sites -/

/-- The three generations of a stage's named barrier in an item: the first, a loop trip's,
the last. -/
inductive Gen where
  | first | loop | last
  deriving DecidableEq

inductive Site where
  /-- The register reduction and the start barrier (`bar.sync 2, 416`). -/
  | setMaxReg | bar0
  /-- The first O-free arrival on the leader's P-ready barrier of stage `st`. -/
  | free (st : Fin 2)
  /-- Stage `st`'s named barrier (`k + 3 + 4 st`), generation `gen` of the item. -/
  | sync (st : Fin 2) (gen : Gen)
  /-- The credits of the statistics barriers (`+240` for even `a`, `+248` for odd `a`):
  after the first generation (`0`), in a trip (`1`, `2`), after the loop (`3`), after the
  loads of `l` (`4`, `5`). -/
  | credit (a : Fin 6)
  /-- A trip of stage `st`: the load of `α`, the vote, the chunks of the rescale, its wait. -/
  | ldA (st : Fin 2) | vote (st : Fin 2)
  | rld (st : Fin 2) (j : Fin 8) | rldW (st : Fin 2) (j : Fin 8) | rst (st : Fin 2) (j : Fin 8)
  | rwait (st : Fin 2)
  /-- The O-free arrival on the leader (after a trip, or after the final stores). -/
  | oFree (st : Fin 2) (fin : Bool)
  /-- The final part of stage `st`: the load of `l`, the waits for the accumulator and the
  staging buffer, the chunks (a load, two four-element stores), the fence, the staged
  arrival. -/
  | ldL (st : Fin 2) | oWait (st : Fin 2) | fWait (st : Fin 2)
  | fld (st : Fin 2) (j : Fin 8) | fldW (st : Fin 2) (j : Fin 8)
  | fst (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4)
  | fence (st : Fin 2) | staged (st : Fin 2)
  /-- The drain of the last staging buffer, the end barrier, the exit. -/
  | tailWait | barEnd | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_5 | .bar0 => Flow.bar_3
  | .free 0 => Flow.mbarArrive_14 | .free 1 => Flow.mbarArrive_15
  | .sync 0 .first => Flow.bar_4 | .sync 1 .first => Flow.bar_5
  | .sync 0 .loop => Flow.bar_6 | .sync 1 .loop => Flow.bar_7
  | .sync 0 .last => Flow.bar_8 | .sync 1 .last => Flow.bar_9
  | .credit 0 => Flow.mbarArrive_16 | .credit 1 => Flow.mbarArrive_18
  | .credit 2 => Flow.mbarArrive_20 | .credit 3 => Flow.mbarArrive_21
  | .credit 4 => Flow.mbarArrive_22 | .credit 5 => Flow.mbarArrive_25
  | .ldA 0 => Flow.load_1 | .ldA 1 => Flow.load_2
  | .vote 0 => Flow.vote_0 | .vote 1 => Flow.vote_1
  | .rld st j => Flow.tmemLoad.getD (8 + 8 * st.val + j.val) 0
  | .rldW st j => Flow.tmemLoad.getD (8 + 8 * st.val + j.val) 0
  | .rst st j => Flow.tmemStore.getD (8 + 8 * st.val + j.val) 0
  | .rwait 0 => Flow.tmemWait_4 | .rwait 1 => Flow.tmemWait_5
  | .oFree 0 false => Flow.mbarArrive_17 | .oFree 1 false => Flow.mbarArrive_19
  | .oFree 0 true => Flow.mbarArrive_23 | .oFree 1 true => Flow.mbarArrive_26
  | .ldL 0 => Flow.load_3 | .ldL 1 => Flow.load_4
  | .oWait 0 => Flow.mbarWait_36 | .oWait 1 => Flow.mbarWait_38
  | .fWait 0 => Flow.mbarWait_37 | .fWait 1 => Flow.mbarWait_39
  | .fld st j => Flow.tmemLoad.getD (24 + 8 * st.val + j.val) 0
  | .fldW st j => Flow.tmemLoad.getD (24 + 8 * st.val + j.val) 0
  | .fst st j h _ => Flow.store.getD (2 + 16 * st.val + 2 * j.val + h.val) 0
  | .fence 0 => Flow.fenceProxy_0 | .fence 1 => Flow.fenceProxy_1
  | .staged 0 => Flow.mbarArrive_24 | .staged 1 => Flow.mbarArrive_27
  | .tailWait => Flow.mbarWait_40 | .barEnd => Flow.barArrive_4 | .exit => Flow.exit_0

/-- The sub-step of the instruction the thread is at: the element of a four-element store,
or `1` for the implicit `tcgen05.wait::ld` after a load (ASM-TCLD-DATAFLOW). -/
def Site.sub : Site → Nat
  | .fst _ _ _ el => el.val
  | .rldW _ _ | .fldW _ _ => 1
  | _ => 0

/-- A correction state. -/
structure D where
  site : Site
  /-- The work item (the number of items finished at the start and at the tail). -/
  i : Nat := 0
  /-- The loop trip of the item. -/
  t : Nat := 0
  /-- The word last read from the statistics slot (`α` or `l`). -/
  aw : Value := b32 0
  /-- Its reading: `α` in a trip; `1 / l'` (`l' = l`, or `1` if `l = 0`) at the final part. -/
  a : ℝ := 0
  /-- The values of the chunk loaded last. -/
  o : List Value := []

/-! ### Values -/

/-- The pair the rescale multiplies with: `α` twice. -/
def rcPair (d : D) : Value := joinValue d.aw d.aw

/-- The pair the final normalization multiplies with: the reciprocal of `l` twice. -/
def fcPair (d : D) : Value := joinValue (recipV d.aw) (recipV d.aw)

/-- Half `h` of the product of pair `q` of the rescaled chunk. -/
def rs (d : D) (q h : Nat) : Value :=
  if h = 0 then (splitValue 64 (prodV d.o (rcPair d) q)).1
  else (splitValue 64 (prodV d.o (rcPair d) q)).2

/-- The half-precision word of pair `q` of the normalized chunk (low product in the low half). -/
def fw (d : D) (q : Nat) : Value := cvtOfPair (prodV d.o (fcPair d) q)

/-- The destination registers of the rescale load `c = 8 st + j` (`rldRegs`) and of the final
load (`fldRegs`). -/
def rldRegs : Nat → List Nat
  | 0 => [2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743,
     2744, 2745, 2746, 2747, 2748, 2749, 2750]
  | 1 => [2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775,
     2776, 2777, 2778, 2779, 2780, 2781, 2782]
  | 2 => [2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807,
     2808, 2809, 2810, 2811, 2812, 2813, 2814]
  | 3 => [2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839,
     2840, 2841, 2842, 2843, 2844, 2845, 2846]
  | 4 => [2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871,
     2872, 2873, 2874, 2875, 2876, 2877, 2878]
  | 5 => [2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903,
     2904, 2905, 2906, 2907, 2908, 2909, 2910]
  | 6 => [2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935,
     2936, 2937, 2938, 2939, 2940, 2941, 2942]
  | 7 => [2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967,
     2968, 2969, 2970, 2971, 2972, 2973, 2974]
  | 8 => [2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001,
     3002, 3003, 3004, 3005, 3006, 3007, 3008]
  | 9 => [3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033,
     3034, 3035, 3036, 3037, 3038, 3039, 3040]
  | 10 => [3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065,
     3066, 3067, 3068, 3069, 3070, 3071, 3072]
  | 11 => [3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097,
     3098, 3099, 3100, 3101, 3102, 3103, 3104]
  | 12 => [3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129,
     3130, 3131, 3132, 3133, 3134, 3135, 3136]
  | 13 => [3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161,
     3162, 3163, 3164, 3165, 3166, 3167, 3168]
  | 14 => [3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193,
     3194, 3195, 3196, 3197, 3198, 3199, 3200]
  | 15 => [3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225,
     3226, 3227, 3228, 3229, 3230, 3231, 3232]
  | _ => []

def fldRegs : Nat → List Nat
  | 0 => [3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265,
     3266, 3267, 3268, 3269, 3270, 3271, 3272]
  | 1 => [3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305,
     3306, 3307, 3308, 3309, 3310, 3311, 3312]
  | 2 => [3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345,
     3346, 3347, 3348, 3349, 3350, 3351, 3352]
  | 3 => [3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385,
     3386, 3387, 3388, 3389, 3390, 3391, 3392]
  | 4 => [3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425,
     3426, 3427, 3428, 3429, 3430, 3431, 3432]
  | 5 => [3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465,
     3466, 3467, 3468, 3469, 3470, 3471, 3472]
  | 6 => [3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505,
     3506, 3507, 3508, 3509, 3510, 3511, 3512]
  | 7 => [3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545,
     3546, 3547, 3548, 3549, 3550, 3551, 3552]
  | 8 => [3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588,
     3589, 3590, 3591, 3592, 3593, 3594, 3595]
  | 9 => [3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628,
     3629, 3630, 3631, 3632, 3633, 3634, 3635]
  | 10 => [3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668,
     3669, 3670, 3671, 3672, 3673, 3674, 3675]
  | 11 => [3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708,
     3709, 3710, 3711, 3712, 3713, 3714, 3715]
  | 12 => [3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748,
     3749, 3750, 3751, 3752, 3753, 3754, 3755]
  | 13 => [3780, 3781, 3782, 3783, 3784, 3785, 3786, 3787, 3788,
     3789, 3790, 3791, 3792, 3793, 3794, 3795]
  | 14 => [3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828,
     3829, 3830, 3831, 3832, 3833, 3834, 3835]
  | 15 => [3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868,
     3869, 3870, 3871, 3872, 3873, 3874, 3875]
  | _ => []

/-- The registers a load writes, live at its implicit wait (beyond the code's liveness, which
the load's own destinations are not part of at its `pc`). -/
def Site.extra : Site → List Nat
  | .rldW st j => rldRegs (8 * st.val + j.val)
  | .fldW st j => fldRegs (8 * st.val + j.val)
  | _ => []

/-- The loaded registers of every chunk: value `m` of the chunk loaded last. -/
def loadValues (d : D) : List (Nat × Value) :=
  [(2735, d.o.getD 0 (b32 0)), (2736, d.o.getD 1 (b32 0)), (2737, d.o.getD 2 (b32 0)),
     (2738, d.o.getD 3 (b32 0)), (2739, d.o.getD 4 (b32 0)), (2740, d.o.getD 5 (b32 0)),
     (2741, d.o.getD 6 (b32 0)), (2742, d.o.getD 7 (b32 0)), (2743, d.o.getD 8 (b32 0)),
     (2744, d.o.getD 9 (b32 0)), (2745, d.o.getD 10 (b32 0)), (2746, d.o.getD 11 (b32 0)),
     (2747, d.o.getD 12 (b32 0)), (2748, d.o.getD 13 (b32 0)), (2749, d.o.getD 14 (b32 0)),
     (2750, d.o.getD 15 (b32 0)), (2767, d.o.getD 0 (b32 0)), (2768, d.o.getD 1 (b32 0)),
     (2769, d.o.getD 2 (b32 0)), (2770, d.o.getD 3 (b32 0)), (2771, d.o.getD 4 (b32 0)),
     (2772, d.o.getD 5 (b32 0)), (2773, d.o.getD 6 (b32 0)), (2774, d.o.getD 7 (b32 0)),
     (2775, d.o.getD 8 (b32 0)), (2776, d.o.getD 9 (b32 0)), (2777, d.o.getD 10 (b32 0)),
     (2778, d.o.getD 11 (b32 0)), (2779, d.o.getD 12 (b32 0)), (2780, d.o.getD 13 (b32 0)),
     (2781, d.o.getD 14 (b32 0)), (2782, d.o.getD 15 (b32 0)), (2799, d.o.getD 0 (b32 0)),
     (2800, d.o.getD 1 (b32 0)), (2801, d.o.getD 2 (b32 0)), (2802, d.o.getD 3 (b32 0)),
     (2803, d.o.getD 4 (b32 0)), (2804, d.o.getD 5 (b32 0)), (2805, d.o.getD 6 (b32 0)),
     (2806, d.o.getD 7 (b32 0)), (2807, d.o.getD 8 (b32 0)), (2808, d.o.getD 9 (b32 0)),
     (2809, d.o.getD 10 (b32 0)), (2810, d.o.getD 11 (b32 0)), (2811, d.o.getD 12 (b32 0)),
     (2812, d.o.getD 13 (b32 0)), (2813, d.o.getD 14 (b32 0)), (2814, d.o.getD 15 (b32 0)),
     (2831, d.o.getD 0 (b32 0)), (2832, d.o.getD 1 (b32 0)), (2833, d.o.getD 2 (b32 0)),
     (2834, d.o.getD 3 (b32 0)), (2835, d.o.getD 4 (b32 0)), (2836, d.o.getD 5 (b32 0)),
     (2837, d.o.getD 6 (b32 0)), (2838, d.o.getD 7 (b32 0)), (2839, d.o.getD 8 (b32 0)),
     (2840, d.o.getD 9 (b32 0)), (2841, d.o.getD 10 (b32 0)), (2842, d.o.getD 11 (b32 0)),
     (2843, d.o.getD 12 (b32 0)), (2844, d.o.getD 13 (b32 0)), (2845, d.o.getD 14 (b32 0)),
     (2846, d.o.getD 15 (b32 0)), (2863, d.o.getD 0 (b32 0)), (2864, d.o.getD 1 (b32 0)),
     (2865, d.o.getD 2 (b32 0)), (2866, d.o.getD 3 (b32 0)), (2867, d.o.getD 4 (b32 0)),
     (2868, d.o.getD 5 (b32 0)), (2869, d.o.getD 6 (b32 0)), (2870, d.o.getD 7 (b32 0)),
     (2871, d.o.getD 8 (b32 0)), (2872, d.o.getD 9 (b32 0)), (2873, d.o.getD 10 (b32 0)),
     (2874, d.o.getD 11 (b32 0)), (2875, d.o.getD 12 (b32 0)), (2876, d.o.getD 13 (b32 0)),
     (2877, d.o.getD 14 (b32 0)), (2878, d.o.getD 15 (b32 0)), (2895, d.o.getD 0 (b32 0)),
     (2896, d.o.getD 1 (b32 0)), (2897, d.o.getD 2 (b32 0)), (2898, d.o.getD 3 (b32 0)),
     (2899, d.o.getD 4 (b32 0)), (2900, d.o.getD 5 (b32 0)), (2901, d.o.getD 6 (b32 0)),
     (2902, d.o.getD 7 (b32 0)), (2903, d.o.getD 8 (b32 0)), (2904, d.o.getD 9 (b32 0)),
     (2905, d.o.getD 10 (b32 0)), (2906, d.o.getD 11 (b32 0)), (2907, d.o.getD 12 (b32 0)),
     (2908, d.o.getD 13 (b32 0)), (2909, d.o.getD 14 (b32 0)), (2910, d.o.getD 15 (b32 0)),
     (2927, d.o.getD 0 (b32 0)), (2928, d.o.getD 1 (b32 0)), (2929, d.o.getD 2 (b32 0)),
     (2930, d.o.getD 3 (b32 0)), (2931, d.o.getD 4 (b32 0)), (2932, d.o.getD 5 (b32 0)),
     (2933, d.o.getD 6 (b32 0)), (2934, d.o.getD 7 (b32 0)), (2935, d.o.getD 8 (b32 0)),
     (2936, d.o.getD 9 (b32 0)), (2937, d.o.getD 10 (b32 0)), (2938, d.o.getD 11 (b32 0)),
     (2939, d.o.getD 12 (b32 0)), (2940, d.o.getD 13 (b32 0)), (2941, d.o.getD 14 (b32 0)),
     (2942, d.o.getD 15 (b32 0)), (2959, d.o.getD 0 (b32 0)), (2960, d.o.getD 1 (b32 0)),
     (2961, d.o.getD 2 (b32 0)), (2962, d.o.getD 3 (b32 0)), (2963, d.o.getD 4 (b32 0)),
     (2964, d.o.getD 5 (b32 0)), (2965, d.o.getD 6 (b32 0)), (2966, d.o.getD 7 (b32 0)),
     (2967, d.o.getD 8 (b32 0)), (2968, d.o.getD 9 (b32 0)), (2969, d.o.getD 10 (b32 0)),
     (2970, d.o.getD 11 (b32 0)), (2971, d.o.getD 12 (b32 0)), (2972, d.o.getD 13 (b32 0)),
     (2973, d.o.getD 14 (b32 0)), (2974, d.o.getD 15 (b32 0)), (3257, d.o.getD 0 (b32 0)),
     (3258, d.o.getD 1 (b32 0)), (3259, d.o.getD 2 (b32 0)), (3260, d.o.getD 3 (b32 0)),
     (3261, d.o.getD 4 (b32 0)), (3262, d.o.getD 5 (b32 0)), (3263, d.o.getD 6 (b32 0)),
     (3264, d.o.getD 7 (b32 0)), (3265, d.o.getD 8 (b32 0)), (3266, d.o.getD 9 (b32 0)),
     (3267, d.o.getD 10 (b32 0)), (3268, d.o.getD 11 (b32 0)), (3269, d.o.getD 12 (b32 0)),
     (3270, d.o.getD 13 (b32 0)), (3271, d.o.getD 14 (b32 0)), (3272, d.o.getD 15 (b32 0)),
     (3297, d.o.getD 0 (b32 0)), (3298, d.o.getD 1 (b32 0)), (3299, d.o.getD 2 (b32 0)),
     (3300, d.o.getD 3 (b32 0)), (3301, d.o.getD 4 (b32 0)), (3302, d.o.getD 5 (b32 0)),
     (3303, d.o.getD 6 (b32 0)), (3304, d.o.getD 7 (b32 0)), (3305, d.o.getD 8 (b32 0)),
     (3306, d.o.getD 9 (b32 0)), (3307, d.o.getD 10 (b32 0)), (3308, d.o.getD 11 (b32 0)),
     (3309, d.o.getD 12 (b32 0)), (3310, d.o.getD 13 (b32 0)), (3311, d.o.getD 14 (b32 0)),
     (3312, d.o.getD 15 (b32 0)), (3337, d.o.getD 0 (b32 0)), (3338, d.o.getD 1 (b32 0)),
     (3339, d.o.getD 2 (b32 0)), (3340, d.o.getD 3 (b32 0)), (3341, d.o.getD 4 (b32 0)),
     (3342, d.o.getD 5 (b32 0)), (3343, d.o.getD 6 (b32 0)), (3344, d.o.getD 7 (b32 0)),
     (3345, d.o.getD 8 (b32 0)), (3346, d.o.getD 9 (b32 0)), (3347, d.o.getD 10 (b32 0)),
     (3348, d.o.getD 11 (b32 0)), (3349, d.o.getD 12 (b32 0)), (3350, d.o.getD 13 (b32 0)),
     (3351, d.o.getD 14 (b32 0)), (3352, d.o.getD 15 (b32 0)), (3377, d.o.getD 0 (b32 0)),
     (3378, d.o.getD 1 (b32 0)), (3379, d.o.getD 2 (b32 0)), (3380, d.o.getD 3 (b32 0)),
     (3381, d.o.getD 4 (b32 0)), (3382, d.o.getD 5 (b32 0)), (3383, d.o.getD 6 (b32 0)),
     (3384, d.o.getD 7 (b32 0)), (3385, d.o.getD 8 (b32 0)), (3386, d.o.getD 9 (b32 0)),
     (3387, d.o.getD 10 (b32 0)), (3388, d.o.getD 11 (b32 0)), (3389, d.o.getD 12 (b32 0)),
     (3390, d.o.getD 13 (b32 0)), (3391, d.o.getD 14 (b32 0)), (3392, d.o.getD 15 (b32 0)),
     (3417, d.o.getD 0 (b32 0)), (3418, d.o.getD 1 (b32 0)), (3419, d.o.getD 2 (b32 0)),
     (3420, d.o.getD 3 (b32 0)), (3421, d.o.getD 4 (b32 0)), (3422, d.o.getD 5 (b32 0)),
     (3423, d.o.getD 6 (b32 0)), (3424, d.o.getD 7 (b32 0)), (3425, d.o.getD 8 (b32 0)),
     (3426, d.o.getD 9 (b32 0)), (3427, d.o.getD 10 (b32 0)), (3428, d.o.getD 11 (b32 0)),
     (3429, d.o.getD 12 (b32 0)), (3430, d.o.getD 13 (b32 0)), (3431, d.o.getD 14 (b32 0)),
     (3432, d.o.getD 15 (b32 0)), (3457, d.o.getD 0 (b32 0)), (3458, d.o.getD 1 (b32 0)),
     (3459, d.o.getD 2 (b32 0)), (3460, d.o.getD 3 (b32 0)), (3461, d.o.getD 4 (b32 0)),
     (3462, d.o.getD 5 (b32 0)), (3463, d.o.getD 6 (b32 0)), (3464, d.o.getD 7 (b32 0)),
     (3465, d.o.getD 8 (b32 0)), (3466, d.o.getD 9 (b32 0)), (3467, d.o.getD 10 (b32 0)),
     (3468, d.o.getD 11 (b32 0)), (3469, d.o.getD 12 (b32 0)), (3470, d.o.getD 13 (b32 0)),
     (3471, d.o.getD 14 (b32 0)), (3472, d.o.getD 15 (b32 0)), (3497, d.o.getD 0 (b32 0)),
     (3498, d.o.getD 1 (b32 0)), (3499, d.o.getD 2 (b32 0)), (3500, d.o.getD 3 (b32 0)),
     (3501, d.o.getD 4 (b32 0)), (3502, d.o.getD 5 (b32 0)), (3503, d.o.getD 6 (b32 0)),
     (3504, d.o.getD 7 (b32 0)), (3505, d.o.getD 8 (b32 0)), (3506, d.o.getD 9 (b32 0)),
     (3507, d.o.getD 10 (b32 0)), (3508, d.o.getD 11 (b32 0)), (3509, d.o.getD 12 (b32 0)),
     (3510, d.o.getD 13 (b32 0)), (3511, d.o.getD 14 (b32 0)), (3512, d.o.getD 15 (b32 0)),
     (3537, d.o.getD 0 (b32 0)), (3538, d.o.getD 1 (b32 0)), (3539, d.o.getD 2 (b32 0)),
     (3540, d.o.getD 3 (b32 0)), (3541, d.o.getD 4 (b32 0)), (3542, d.o.getD 5 (b32 0)),
     (3543, d.o.getD 6 (b32 0)), (3544, d.o.getD 7 (b32 0)), (3545, d.o.getD 8 (b32 0)),
     (3546, d.o.getD 9 (b32 0)), (3547, d.o.getD 10 (b32 0)), (3548, d.o.getD 11 (b32 0)),
     (3549, d.o.getD 12 (b32 0)), (3550, d.o.getD 13 (b32 0)), (3551, d.o.getD 14 (b32 0)),
     (3552, d.o.getD 15 (b32 0)), (2993, d.o.getD 0 (b32 0)), (2994, d.o.getD 1 (b32 0)),
     (2995, d.o.getD 2 (b32 0)), (2996, d.o.getD 3 (b32 0)), (2997, d.o.getD 4 (b32 0)),
     (2998, d.o.getD 5 (b32 0)), (2999, d.o.getD 6 (b32 0)), (3000, d.o.getD 7 (b32 0)),
     (3001, d.o.getD 8 (b32 0)), (3002, d.o.getD 9 (b32 0)), (3003, d.o.getD 10 (b32 0)),
     (3004, d.o.getD 11 (b32 0)), (3005, d.o.getD 12 (b32 0)), (3006, d.o.getD 13 (b32 0)),
     (3007, d.o.getD 14 (b32 0)), (3008, d.o.getD 15 (b32 0)), (3025, d.o.getD 0 (b32 0)),
     (3026, d.o.getD 1 (b32 0)), (3027, d.o.getD 2 (b32 0)), (3028, d.o.getD 3 (b32 0)),
     (3029, d.o.getD 4 (b32 0)), (3030, d.o.getD 5 (b32 0)), (3031, d.o.getD 6 (b32 0)),
     (3032, d.o.getD 7 (b32 0)), (3033, d.o.getD 8 (b32 0)), (3034, d.o.getD 9 (b32 0)),
     (3035, d.o.getD 10 (b32 0)), (3036, d.o.getD 11 (b32 0)), (3037, d.o.getD 12 (b32 0)),
     (3038, d.o.getD 13 (b32 0)), (3039, d.o.getD 14 (b32 0)), (3040, d.o.getD 15 (b32 0)),
     (3057, d.o.getD 0 (b32 0)), (3058, d.o.getD 1 (b32 0)), (3059, d.o.getD 2 (b32 0)),
     (3060, d.o.getD 3 (b32 0)), (3061, d.o.getD 4 (b32 0)), (3062, d.o.getD 5 (b32 0)),
     (3063, d.o.getD 6 (b32 0)), (3064, d.o.getD 7 (b32 0)), (3065, d.o.getD 8 (b32 0)),
     (3066, d.o.getD 9 (b32 0)), (3067, d.o.getD 10 (b32 0)), (3068, d.o.getD 11 (b32 0)),
     (3069, d.o.getD 12 (b32 0)), (3070, d.o.getD 13 (b32 0)), (3071, d.o.getD 14 (b32 0)),
     (3072, d.o.getD 15 (b32 0)), (3089, d.o.getD 0 (b32 0)), (3090, d.o.getD 1 (b32 0)),
     (3091, d.o.getD 2 (b32 0)), (3092, d.o.getD 3 (b32 0)), (3093, d.o.getD 4 (b32 0)),
     (3094, d.o.getD 5 (b32 0)), (3095, d.o.getD 6 (b32 0)), (3096, d.o.getD 7 (b32 0)),
     (3097, d.o.getD 8 (b32 0)), (3098, d.o.getD 9 (b32 0)), (3099, d.o.getD 10 (b32 0)),
     (3100, d.o.getD 11 (b32 0)), (3101, d.o.getD 12 (b32 0)), (3102, d.o.getD 13 (b32 0)),
     (3103, d.o.getD 14 (b32 0)), (3104, d.o.getD 15 (b32 0)), (3121, d.o.getD 0 (b32 0)),
     (3122, d.o.getD 1 (b32 0)), (3123, d.o.getD 2 (b32 0)), (3124, d.o.getD 3 (b32 0)),
     (3125, d.o.getD 4 (b32 0)), (3126, d.o.getD 5 (b32 0)), (3127, d.o.getD 6 (b32 0)),
     (3128, d.o.getD 7 (b32 0)), (3129, d.o.getD 8 (b32 0)), (3130, d.o.getD 9 (b32 0)),
     (3131, d.o.getD 10 (b32 0)), (3132, d.o.getD 11 (b32 0)), (3133, d.o.getD 12 (b32 0)),
     (3134, d.o.getD 13 (b32 0)), (3135, d.o.getD 14 (b32 0)), (3136, d.o.getD 15 (b32 0)),
     (3153, d.o.getD 0 (b32 0)), (3154, d.o.getD 1 (b32 0)), (3155, d.o.getD 2 (b32 0)),
     (3156, d.o.getD 3 (b32 0)), (3157, d.o.getD 4 (b32 0)), (3158, d.o.getD 5 (b32 0)),
     (3159, d.o.getD 6 (b32 0)), (3160, d.o.getD 7 (b32 0)), (3161, d.o.getD 8 (b32 0)),
     (3162, d.o.getD 9 (b32 0)), (3163, d.o.getD 10 (b32 0)), (3164, d.o.getD 11 (b32 0)),
     (3165, d.o.getD 12 (b32 0)), (3166, d.o.getD 13 (b32 0)), (3167, d.o.getD 14 (b32 0)),
     (3168, d.o.getD 15 (b32 0)), (3185, d.o.getD 0 (b32 0)), (3186, d.o.getD 1 (b32 0)),
     (3187, d.o.getD 2 (b32 0)), (3188, d.o.getD 3 (b32 0)), (3189, d.o.getD 4 (b32 0)),
     (3190, d.o.getD 5 (b32 0)), (3191, d.o.getD 6 (b32 0)), (3192, d.o.getD 7 (b32 0)),
     (3193, d.o.getD 8 (b32 0)), (3194, d.o.getD 9 (b32 0)), (3195, d.o.getD 10 (b32 0)),
     (3196, d.o.getD 11 (b32 0)), (3197, d.o.getD 12 (b32 0)), (3198, d.o.getD 13 (b32 0)),
     (3199, d.o.getD 14 (b32 0)), (3200, d.o.getD 15 (b32 0)), (3217, d.o.getD 0 (b32 0)),
     (3218, d.o.getD 1 (b32 0)), (3219, d.o.getD 2 (b32 0)), (3220, d.o.getD 3 (b32 0)),
     (3221, d.o.getD 4 (b32 0)), (3222, d.o.getD 5 (b32 0)), (3223, d.o.getD 6 (b32 0)),
     (3224, d.o.getD 7 (b32 0)), (3225, d.o.getD 8 (b32 0)), (3226, d.o.getD 9 (b32 0)),
     (3227, d.o.getD 10 (b32 0)), (3228, d.o.getD 11 (b32 0)), (3229, d.o.getD 12 (b32 0)),
     (3230, d.o.getD 13 (b32 0)), (3231, d.o.getD 14 (b32 0)), (3232, d.o.getD 15 (b32 0)),
     (3580, d.o.getD 0 (b32 0)), (3581, d.o.getD 1 (b32 0)), (3582, d.o.getD 2 (b32 0)),
     (3583, d.o.getD 3 (b32 0)), (3584, d.o.getD 4 (b32 0)), (3585, d.o.getD 5 (b32 0)),
     (3586, d.o.getD 6 (b32 0)), (3587, d.o.getD 7 (b32 0)), (3588, d.o.getD 8 (b32 0)),
     (3589, d.o.getD 9 (b32 0)), (3590, d.o.getD 10 (b32 0)), (3591, d.o.getD 11 (b32 0)),
     (3592, d.o.getD 12 (b32 0)), (3593, d.o.getD 13 (b32 0)), (3594, d.o.getD 14 (b32 0)),
     (3595, d.o.getD 15 (b32 0)), (3620, d.o.getD 0 (b32 0)), (3621, d.o.getD 1 (b32 0)),
     (3622, d.o.getD 2 (b32 0)), (3623, d.o.getD 3 (b32 0)), (3624, d.o.getD 4 (b32 0)),
     (3625, d.o.getD 5 (b32 0)), (3626, d.o.getD 6 (b32 0)), (3627, d.o.getD 7 (b32 0)),
     (3628, d.o.getD 8 (b32 0)), (3629, d.o.getD 9 (b32 0)), (3630, d.o.getD 10 (b32 0)),
     (3631, d.o.getD 11 (b32 0)), (3632, d.o.getD 12 (b32 0)), (3633, d.o.getD 13 (b32 0)),
     (3634, d.o.getD 14 (b32 0)), (3635, d.o.getD 15 (b32 0)), (3660, d.o.getD 0 (b32 0)),
     (3661, d.o.getD 1 (b32 0)), (3662, d.o.getD 2 (b32 0)), (3663, d.o.getD 3 (b32 0)),
     (3664, d.o.getD 4 (b32 0)), (3665, d.o.getD 5 (b32 0)), (3666, d.o.getD 6 (b32 0)),
     (3667, d.o.getD 7 (b32 0)), (3668, d.o.getD 8 (b32 0)), (3669, d.o.getD 9 (b32 0)),
     (3670, d.o.getD 10 (b32 0)), (3671, d.o.getD 11 (b32 0)), (3672, d.o.getD 12 (b32 0)),
     (3673, d.o.getD 13 (b32 0)), (3674, d.o.getD 14 (b32 0)), (3675, d.o.getD 15 (b32 0)),
     (3700, d.o.getD 0 (b32 0)), (3701, d.o.getD 1 (b32 0)), (3702, d.o.getD 2 (b32 0)),
     (3703, d.o.getD 3 (b32 0)), (3704, d.o.getD 4 (b32 0)), (3705, d.o.getD 5 (b32 0)),
     (3706, d.o.getD 6 (b32 0)), (3707, d.o.getD 7 (b32 0)), (3708, d.o.getD 8 (b32 0)),
     (3709, d.o.getD 9 (b32 0)), (3710, d.o.getD 10 (b32 0)), (3711, d.o.getD 11 (b32 0)),
     (3712, d.o.getD 12 (b32 0)), (3713, d.o.getD 13 (b32 0)), (3714, d.o.getD 14 (b32 0)),
     (3715, d.o.getD 15 (b32 0)), (3740, d.o.getD 0 (b32 0)), (3741, d.o.getD 1 (b32 0)),
     (3742, d.o.getD 2 (b32 0)), (3743, d.o.getD 3 (b32 0)), (3744, d.o.getD 4 (b32 0)),
     (3745, d.o.getD 5 (b32 0)), (3746, d.o.getD 6 (b32 0)), (3747, d.o.getD 7 (b32 0)),
     (3748, d.o.getD 8 (b32 0)), (3749, d.o.getD 9 (b32 0)), (3750, d.o.getD 10 (b32 0)),
     (3751, d.o.getD 11 (b32 0)), (3752, d.o.getD 12 (b32 0)), (3753, d.o.getD 13 (b32 0)),
     (3754, d.o.getD 14 (b32 0)), (3755, d.o.getD 15 (b32 0)), (3780, d.o.getD 0 (b32 0)),
     (3781, d.o.getD 1 (b32 0)), (3782, d.o.getD 2 (b32 0)), (3783, d.o.getD 3 (b32 0)),
     (3784, d.o.getD 4 (b32 0)), (3785, d.o.getD 5 (b32 0)), (3786, d.o.getD 6 (b32 0)),
     (3787, d.o.getD 7 (b32 0)), (3788, d.o.getD 8 (b32 0)), (3789, d.o.getD 9 (b32 0)),
     (3790, d.o.getD 10 (b32 0)), (3791, d.o.getD 11 (b32 0)), (3792, d.o.getD 12 (b32 0)),
     (3793, d.o.getD 13 (b32 0)), (3794, d.o.getD 14 (b32 0)), (3795, d.o.getD 15 (b32 0)),
     (3820, d.o.getD 0 (b32 0)), (3821, d.o.getD 1 (b32 0)), (3822, d.o.getD 2 (b32 0)),
     (3823, d.o.getD 3 (b32 0)), (3824, d.o.getD 4 (b32 0)), (3825, d.o.getD 5 (b32 0)),
     (3826, d.o.getD 6 (b32 0)), (3827, d.o.getD 7 (b32 0)), (3828, d.o.getD 8 (b32 0)),
     (3829, d.o.getD 9 (b32 0)), (3830, d.o.getD 10 (b32 0)), (3831, d.o.getD 11 (b32 0)),
     (3832, d.o.getD 12 (b32 0)), (3833, d.o.getD 13 (b32 0)), (3834, d.o.getD 14 (b32 0)),
     (3835, d.o.getD 15 (b32 0)), (3860, d.o.getD 0 (b32 0)), (3861, d.o.getD 1 (b32 0)),
     (3862, d.o.getD 2 (b32 0)), (3863, d.o.getD 3 (b32 0)), (3864, d.o.getD 4 (b32 0)),
     (3865, d.o.getD 5 (b32 0)), (3866, d.o.getD 6 (b32 0)), (3867, d.o.getD 7 (b32 0)),
     (3868, d.o.getD 8 (b32 0)), (3869, d.o.getD 9 (b32 0)), (3870, d.o.getD 10 (b32 0)),
     (3871, d.o.getD 11 (b32 0)), (3872, d.o.getD 12 (b32 0)), (3873, d.o.getD 13 (b32 0)),
     (3874, d.o.getD 14 (b32 0)), (3875, d.o.getD 15 (b32 0))]

/-- The registers of the chunks: the products of each rescaled chunk (written before its
`tcgen05.st`) and the half-precision words of each normalized chunk (before its stores). Only
the current chunk's registers are live at a site, so all chunks share `d.o`. -/
def chunkValues (d : D) : List (Nat × Value) :=
  [(2751, rs d 7 0), (2752, rs d 7 1), (2753, rs d 6 0), (2754, rs d 6 1), (2755, rs d 5 0),
     (2756, rs d 5 1), (2757, rs d 4 0), (2758, rs d 4 1), (2759, rs d 3 0), (2760, rs d 3 1),
     (2761, rs d 2 0), (2762, rs d 2 1), (2763, rs d 1 0), (2764, rs d 1 1), (2765, rs d 0 0),
     (2766, rs d 0 1), (2783, rs d 7 0), (2784, rs d 7 1), (2785, rs d 6 0), (2786, rs d 6 1),
     (2787, rs d 5 0), (2788, rs d 5 1), (2789, rs d 4 0), (2790, rs d 4 1), (2791, rs d 3 0),
     (2792, rs d 3 1), (2793, rs d 2 0), (2794, rs d 2 1), (2795, rs d 1 0), (2796, rs d 1 1),
     (2797, rs d 0 0), (2798, rs d 0 1), (2815, rs d 7 0), (2816, rs d 7 1), (2817, rs d 6 0),
     (2818, rs d 6 1), (2819, rs d 5 0), (2820, rs d 5 1), (2821, rs d 4 0), (2822, rs d 4 1),
     (2823, rs d 3 0), (2824, rs d 3 1), (2825, rs d 2 0), (2826, rs d 2 1), (2827, rs d 1 0),
     (2828, rs d 1 1), (2829, rs d 0 0), (2830, rs d 0 1), (2847, rs d 7 0), (2848, rs d 7 1),
     (2849, rs d 6 0), (2850, rs d 6 1), (2851, rs d 5 0), (2852, rs d 5 1), (2853, rs d 4 0),
     (2854, rs d 4 1), (2855, rs d 3 0), (2856, rs d 3 1), (2857, rs d 2 0), (2858, rs d 2 1),
     (2859, rs d 1 0), (2860, rs d 1 1), (2861, rs d 0 0), (2862, rs d 0 1), (2879, rs d 7 0),
     (2880, rs d 7 1), (2881, rs d 6 0), (2882, rs d 6 1), (2883, rs d 5 0), (2884, rs d 5 1),
     (2885, rs d 4 0), (2886, rs d 4 1), (2887, rs d 3 0), (2888, rs d 3 1), (2889, rs d 2 0),
     (2890, rs d 2 1), (2891, rs d 1 0), (2892, rs d 1 1), (2893, rs d 0 0), (2894, rs d 0 1),
     (2911, rs d 7 0), (2912, rs d 7 1), (2913, rs d 6 0), (2914, rs d 6 1), (2915, rs d 5 0),
     (2916, rs d 5 1), (2917, rs d 4 0), (2918, rs d 4 1), (2919, rs d 3 0), (2920, rs d 3 1),
     (2921, rs d 2 0), (2922, rs d 2 1), (2923, rs d 1 0), (2924, rs d 1 1), (2925, rs d 0 0),
     (2926, rs d 0 1), (2943, rs d 7 0), (2944, rs d 7 1), (2945, rs d 6 0), (2946, rs d 6 1),
     (2947, rs d 5 0), (2948, rs d 5 1), (2949, rs d 4 0), (2950, rs d 4 1), (2951, rs d 3 0),
     (2952, rs d 3 1), (2953, rs d 2 0), (2954, rs d 2 1), (2955, rs d 1 0), (2956, rs d 1 1),
     (2957, rs d 0 0), (2958, rs d 0 1), (2975, rs d 7 0), (2976, rs d 7 1), (2977, rs d 6 0),
     (2978, rs d 6 1), (2979, rs d 5 0), (2980, rs d 5 1), (2981, rs d 4 0), (2982, rs d 4 1),
     (2983, rs d 3 0), (2984, rs d 3 1), (2985, rs d 2 0), (2986, rs d 2 1), (2987, rs d 1 0),
     (2988, rs d 1 1), (2989, rs d 0 0), (2990, rs d 0 1), (3009, rs d 7 0), (3010, rs d 7 1),
     (3011, rs d 6 0), (3012, rs d 6 1), (3013, rs d 5 0), (3014, rs d 5 1), (3015, rs d 4 0),
     (3016, rs d 4 1), (3017, rs d 3 0), (3018, rs d 3 1), (3019, rs d 2 0), (3020, rs d 2 1),
     (3021, rs d 1 0), (3022, rs d 1 1), (3023, rs d 0 0), (3024, rs d 0 1), (3041, rs d 7 0),
     (3042, rs d 7 1), (3043, rs d 6 0), (3044, rs d 6 1), (3045, rs d 5 0), (3046, rs d 5 1),
     (3047, rs d 4 0), (3048, rs d 4 1), (3049, rs d 3 0), (3050, rs d 3 1), (3051, rs d 2 0),
     (3052, rs d 2 1), (3053, rs d 1 0), (3054, rs d 1 1), (3055, rs d 0 0), (3056, rs d 0 1),
     (3073, rs d 7 0), (3074, rs d 7 1), (3075, rs d 6 0), (3076, rs d 6 1), (3077, rs d 5 0),
     (3078, rs d 5 1), (3079, rs d 4 0), (3080, rs d 4 1), (3081, rs d 3 0), (3082, rs d 3 1),
     (3083, rs d 2 0), (3084, rs d 2 1), (3085, rs d 1 0), (3086, rs d 1 1), (3087, rs d 0 0),
     (3088, rs d 0 1), (3105, rs d 7 0), (3106, rs d 7 1), (3107, rs d 6 0), (3108, rs d 6 1),
     (3109, rs d 5 0), (3110, rs d 5 1), (3111, rs d 4 0), (3112, rs d 4 1), (3113, rs d 3 0),
     (3114, rs d 3 1), (3115, rs d 2 0), (3116, rs d 2 1), (3117, rs d 1 0), (3118, rs d 1 1),
     (3119, rs d 0 0), (3120, rs d 0 1), (3137, rs d 7 0), (3138, rs d 7 1), (3139, rs d 6 0),
     (3140, rs d 6 1), (3141, rs d 5 0), (3142, rs d 5 1), (3143, rs d 4 0), (3144, rs d 4 1),
     (3145, rs d 3 0), (3146, rs d 3 1), (3147, rs d 2 0), (3148, rs d 2 1), (3149, rs d 1 0),
     (3150, rs d 1 1), (3151, rs d 0 0), (3152, rs d 0 1), (3169, rs d 7 0), (3170, rs d 7 1),
     (3171, rs d 6 0), (3172, rs d 6 1), (3173, rs d 5 0), (3174, rs d 5 1), (3175, rs d 4 0),
     (3176, rs d 4 1), (3177, rs d 3 0), (3178, rs d 3 1), (3179, rs d 2 0), (3180, rs d 2 1),
     (3181, rs d 1 0), (3182, rs d 1 1), (3183, rs d 0 0), (3184, rs d 0 1), (3201, rs d 7 0),
     (3202, rs d 7 1), (3203, rs d 6 0), (3204, rs d 6 1), (3205, rs d 5 0), (3206, rs d 5 1),
     (3207, rs d 4 0), (3208, rs d 4 1), (3209, rs d 3 0), (3210, rs d 3 1), (3211, rs d 2 0),
     (3212, rs d 2 1), (3213, rs d 1 0), (3214, rs d 1 1), (3215, rs d 0 0), (3216, rs d 0 1),
     (3233, rs d 7 0), (3234, rs d 7 1), (3235, rs d 6 0), (3236, rs d 6 1), (3237, rs d 5 0),
     (3238, rs d 5 1), (3239, rs d 4 0), (3240, rs d 4 1), (3241, rs d 3 0), (3242, rs d 3 1),
     (3243, rs d 2 0), (3244, rs d 2 1), (3245, rs d 1 0), (3246, rs d 1 1), (3247, rs d 0 0),
     (3248, rs d 0 1), (3275, fw d 7), (3278, fw d 6), (3281, fw d 5), (3284, fw d 4),
     (3287, fw d 3), (3290, fw d 2), (3293, fw d 1), (3296, fw d 0), (3315, fw d 7),
     (3318, fw d 6), (3321, fw d 5), (3324, fw d 4), (3327, fw d 3), (3330, fw d 2),
     (3333, fw d 1), (3336, fw d 0), (3355, fw d 7), (3358, fw d 6), (3361, fw d 5),
     (3364, fw d 4), (3367, fw d 3), (3370, fw d 2), (3373, fw d 1), (3376, fw d 0),
     (3395, fw d 7), (3398, fw d 6), (3401, fw d 5), (3404, fw d 4), (3407, fw d 3),
     (3410, fw d 2), (3413, fw d 1), (3416, fw d 0), (3435, fw d 7), (3438, fw d 6),
     (3441, fw d 5), (3444, fw d 4), (3447, fw d 3), (3450, fw d 2), (3453, fw d 1),
     (3456, fw d 0), (3475, fw d 7), (3478, fw d 6), (3481, fw d 5), (3484, fw d 4),
     (3487, fw d 3), (3490, fw d 2), (3493, fw d 1), (3496, fw d 0), (3515, fw d 7),
     (3518, fw d 6), (3521, fw d 5), (3524, fw d 4), (3527, fw d 3), (3530, fw d 2),
     (3533, fw d 1), (3536, fw d 0), (3555, fw d 7), (3558, fw d 6), (3561, fw d 5),
     (3564, fw d 4), (3567, fw d 3), (3570, fw d 2), (3573, fw d 1), (3576, fw d 0),
     (3598, fw d 7), (3601, fw d 6), (3604, fw d 5), (3607, fw d 4), (3610, fw d 3),
     (3613, fw d 2), (3616, fw d 1), (3619, fw d 0), (3638, fw d 7), (3641, fw d 6),
     (3644, fw d 5), (3647, fw d 4), (3650, fw d 3), (3653, fw d 2), (3656, fw d 1),
     (3659, fw d 0), (3678, fw d 7), (3681, fw d 6), (3684, fw d 5), (3687, fw d 4),
     (3690, fw d 3), (3693, fw d 2), (3696, fw d 1), (3699, fw d 0), (3718, fw d 7),
     (3721, fw d 6), (3724, fw d 5), (3727, fw d 4), (3730, fw d 3), (3733, fw d 2),
     (3736, fw d 1), (3739, fw d 0), (3758, fw d 7), (3761, fw d 6), (3764, fw d 5),
     (3767, fw d 4), (3770, fw d 3), (3773, fw d 2), (3776, fw d 1), (3779, fw d 0),
     (3798, fw d 7), (3801, fw d 6), (3804, fw d 5), (3807, fw d 4), (3810, fw d 3),
     (3813, fw d 2), (3816, fw d 1), (3819, fw d 0), (3838, fw d 7), (3841, fw d 6),
     (3844, fw d 5), (3847, fw d 4), (3850, fw d 3), (3853, fw d 2), (3856, fw d 1),
     (3859, fw d 0), (3878, fw d 7), (3881, fw d 6), (3884, fw d 5), (3887, fw d 4),
     (3890, fw d 3), (3893, fw d 2), (3896, fw d 1), (3899, fw d 0)]

/-- The thread's other register values. -/
def values (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let n := trips L
  [(336, b32 (warpOf L g)), (337, b32 (sb L + 0)), (342, b32 0), (343, b32 (sb L + 240)),
   (665, b32 (skOf L)), (970, b32 (sb L + 256)), (3250, b32 (sb L + 192)),
   (3251, b32 (sb L + 272)), (3907, b32 (totOf L)), (3936, b32 (work L g d.i)),
   (618, b32 (tidOf L g)), (619, b32 (rowOf L g)), (2704, b32 (kOf L g)),
   (620, leadPtr L g 144), (621, leadPtr L g 152), (3939, b32 ((d.i + 1) % 2)),
   (622, b32 (kOf L g + 3)), (623, b32 (kOf L g + 7)),
   (625, b32 (stage L g 0 0)), (626, b32 (stage L g 1 0)), (3900, b32 (sb L + 280)),
   (298, .pred (decide (n ≤ 1))),
   (627, b32 (sb L + 4 * rowOf L g)), (628, b32 (sb L + 248)),
   (629, b32 (tmem L g 384)),
   (630, b32 (tmem L g 256)), (631, b32 (tmem L g 272)), (632, b32 (tmem L g 288)),
   (633, b32 (tmem L g 304)), (634, b32 (tmem L g 320)), (635, b32 (tmem L g 336)),
   (636, b32 (tmem L g 352)), (637, b32 (tmem L g 368)),
   (638, b32 (tmem L g 400)), (639, b32 (tmem L g 416)), (640, b32 (tmem L g 432)),
   (641, b32 (tmem L g 448)), (642, b32 (tmem L g 464)), (643, b32 (tmem L g 480)),
   (644, b32 (tmem L g 496)),
   (645, b32 (stage L g 0 1)), (646, b32 (stage L g 0 2)), (647, b32 (stage L g 0 3)),
   (648, b32 (stage L g 0 4)), (649, b32 (stage L g 0 5)), (650, b32 (stage L g 0 6)),
   (651, b32 (stage L g 0 7)),
   (652, b32 (stage L g 1 1)), (653, b32 (stage L g 1 2)), (654, b32 (stage L g 1 3)),
   (655, b32 (stage L g 1 4)), (656, b32 (stage L g 1 5)), (657, b32 (stage L g 1 6)),
   (658, b32 (stage L g 1 7)),
   (659, b32 (neg32 n)), (660, b32 (nClusters L)), (661, b32 (sb L + 264)),
   (3252, b32 (sb L + 200)), (662, b32 (n - 1)), (3937, b32 (d.i % 2)),
   (3938, b32 ((neg32 n + d.t) % 2 ^ 32)),
   (2733, b32 1), (2991, b32 1), (3249, b32 1), (3253, b32 1),
   (663, d.aw), (664, d.aw), (3254, d.aw), (3577, d.aw),
   (299, .pred (ltOne d.aw)), (301, .pred (ltOne d.aw)),
   (4814, rcPair d), (4944, rcPair d),
   (3256, recipV d.aw), (3579, recipV d.aw), (5068, fcPair d), (5199, fcPair d)]

/-- A register's value: a chunk register holds its product or word, the others are given by
`values`. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((chunkValues d ++ loadValues d ++ values L g d).lookup r).getD (b32 0)

def factsAt (L : Launch) (g pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc ++ d.site.extra) (valueOf L g d)

/-! ### Transitions -/

/-- The item after item `i`, or the tail. -/
def nextItem (L : Launch) (g : Nat) (d : D) : D :=
  if d.i + 1 < items L g then { d with site := .sync 0 .first, i := d.i + 1, t := 0 }
  else { d with site := .tailWait, i := d.i + 1, t := 0 }

/-- After a stage's trip: the other stage's credit, or the next trip, or the loop's end. -/
def afterTrip (L : Launch) (d : D) : D :=
  if d.t + 2 < trips L then { d with site := .sync 0 .loop, t := d.t + 1 }
  else { d with site := .credit 3 }

def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some { d with site := .bar0 })
  | .bar0 => some (some { d with site := .free 0 })
  | .free 0 => some (some { d with site := .free 1 })
  | .free 1 =>
    if 0 < items L g then some (some { d with site := .sync 0 .first, i := 0, t := 0 })
    else some (some { d with site := .tailWait, i := 0, t := 0 })
  | .sync 0 .first => some (some { d with site := .credit 0 })
  | .credit 0 => some (some { d with site := .sync 1 .first })
  | .sync 1 .first =>
    if trips L ≤ 1 then some (some { d with site := .credit 3 })
    else some (some { d with site := .sync 0 .loop, t := 0 })
  | .sync 0 .loop => some (some { d with site := .ldA 0 })
  | .sync 1 .loop => some (some { d with site := .ldA 1 })
  | .ldA st => match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => match ltOneE v with
        | .ok _ => some (some { d with site := .vote st, aw := v, a := rd32 v })
        | .error _ => none
      | .error _ => none
    | _ => none
  | .vote st => match e.kind with
    | .vote _ _ bal =>
      if bal = 0 then some (some { d with site := .oFree st false })
      else some (some { d with site := .rld st 0 })
    | _ => none
  | .rld st j => match e.kind with
    | .tc (.ld _ vals .s32x32b) => some (some { d with site := .rldW st j, o := vals })
    | _ => none
  | .rldW st j =>
    if d.aw.bytes = 4 ∧ chunkOk d.o (rcPair d) = true then
      some (some { d with site := .rst st j })
    else none
  | .rst st j =>
    if h : j.val + 1 < 8 then some (some { d with site := .rld st ⟨j.val + 1, h⟩ })
    else some (some { d with site := .rwait st })
  | .rwait st => some (some { d with site := .oFree st false })
  | .oFree 0 false => some (some { d with site := .credit 1 })
  | .credit 1 => some (some { d with site := .sync 1 .loop })
  | .oFree 1 false => some (some { d with site := .credit 2 })
  | .credit 2 => some (some (afterTrip L d))
  | .credit 3 => some (some { d with site := .sync 0 .last })
  | .sync 0 .last => some (some { d with site := .ldL 0 })
  | .sync 1 .last => some (some { d with site := .ldL 1 })
  | .ldL st => match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => some (some { d with site := .credit ⟨4 + st.val, by omega⟩, aw := v })
      | .error _ => none
    | _ => none
  | .credit 4 => match recipE d.aw with
    | .ok r => some (some { d with site := .oWait 0, a := rd32 r })
    | .error _ => none
  | .credit 5 => match recipE d.aw with
    | .ok r => some (some { d with site := .oWait 1, a := rd32 r })
    | .error _ => none
  | .oWait st => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .fWait st else .oWait st })
    | _ => none
  | .fWait st => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .fld st 0 else .fWait st })
    | _ => none
  | .fld st j => match e.kind with
    | .tc (.ld _ vals .s32x32b) => some (some { d with site := .fldW st j, o := vals })
    | _ => none
  | .fldW st j =>
    if finOk d.o (fcPair d) = true then some (some { d with site := .fst st j 0 0 })
    else none
  | .fst st j h el =>
    if hel : el.val + 1 < 4 then some (some { d with site := .fst st j h ⟨el.val + 1, hel⟩ })
    else if h.val = 0 then some (some { d with site := .fst st j 1 0 })
    else if hj : j.val + 1 < 8 then some (some { d with site := .fld st ⟨j.val + 1, hj⟩ })
    else some (some { d with site := .fence st })
  | .fence st => some (some { d with site := .oFree st true })
  | .oFree 0 true => some (some { d with site := .staged 0 })
  | .oFree 1 true => some (some { d with site := .staged 1 })
  | .staged 0 => some (some { d with site := .sync 1 .last })
  | .staged 1 => some (some (nextItem L g d))
  | .tailWait => match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .barEnd else .tailWait })
    | _ => none
  | .barEnd => some (some { d with site := .exit })
  | .exit => none

/-! ### The invariant of a state -/

/-- Sites inside an item. -/
def Site.inItem : Site → Bool
  | .setMaxReg | .bar0 | .free _ | .tailWait | .barEnd | .exit => false
  | _ => true

/-- Sites inside a loop trip. -/
def Site.inTrip : Site → Bool
  | .sync _ .loop | .ldA _ | .vote _ | .rld _ _ | .rldW _ _ | .rst _ _ | .rwait _
  | .oFree _ false
  | .credit 1 | .credit 2 => true
  | _ => false

/-- Sites where the statistics word read is the `α` the rescale multiplies with. -/
def Site.rescale : Site → Bool
  | .vote _ | .rld _ _ | .rldW _ _ | .rst _ _ => true
  | _ => false

structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  /-- An item site is in an item of the cluster; the tail is after all of them. -/
  item : d.site.inItem = true → d.i < items L g
  tail : d.site.inItem = false → d.site ≠ .setMaxReg → d.site ≠ .bar0 →
    (∀ st, d.site ≠ .free st) → d.i = items L g
  start : d.site = .setMaxReg ∨ d.site = .bar0 ∨ (∃ st, d.site = .free st) → d.i = 0
  /-- A trip site is in one of the `n - 1` trips. -/
  trip : d.site.inTrip = true → d.t + 1 < trips L
  /-- The word read in a trip is one the vote's comparison reads. -/
  alpha : d.site.rescale = true → ∃ b, ltOneE d.aw = .ok b

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
