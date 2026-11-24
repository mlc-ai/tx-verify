-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Support.Geometry
public import Lemmas.Flow.Regs

@[expose] public section

/-! Register values of the loader's K loop, for the tile `(m, n)` and K block `q` (a multiple
of eight: one trip issues eight blocks). Read off the PTX; `Loader.lean` proves that
local execution computes them. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof
noncomputable section
set_option maxRecDepth 100000

def values0 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(49,b32 (512*m)),
   (50,b32 (512*m+128)),
   (51,b32 (256*n)),
   (896,.ptr 64 false (.param "gemm_kernel_param_0") 0),
   (895,.ptr 64 false (.param "gemm_kernel_param_1") 0),
   (750, .ptr 32 false (.shared (g / L.block) (2* ((g/L.block)/2)))
       (BitVec.ofNat 64 (L.sharedBase+8))),
   (877,b32 q)]

def values1 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(670,b32 L.sharedBase),
   (656,b32 (L.sharedBase+40)),
   (657,b32 1),
   (658,b32 10000000),
   (661,b32 (64*(q+0))),
   (659,b32 ((g/L.block)%2)),
   (671,b32 (256*((g/L.block)%2))),
   (662,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (927,.ptr 64 true (.param "gemm_kernel_param_0") 0),
   (660,b32 (L.sharedBase+1024)),
   (663,b32 ((g/L.block)%2)),
   (672,b32 (256*((g/L.block)%2))),
   (665,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (664,b32 (L.sharedBase+17408)),
   (666,b32 ((g/L.block)%2)),
   (673,b32 (128*((g/L.block)%2))),
   (668,b32 (256*n+128*((g/L.block)%2))),
   (928,.ptr 64 true (.param "gemm_kernel_param_1") 0),
   (667,b32 (L.sharedBase+132096)),
   (669,b32 ((g/L.block)%2)),
   (26,.pred (decide ((g/L.block)%2 ≠ 0))),
   (674,b32 98304)]

def values2 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(689,b32 L.sharedBase),
   (675,b32 (L.sharedBase+48)),
   (676,b32 1),
   (677,b32 10000000),
   (680,b32 (64*(q+1))),
   (678,b32 ((g/L.block)%2)),
   (690,b32 (256*((g/L.block)%2))),
   (681,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (770, .ptr 32 false (.shared (g / L.block) (2* ((g/L.block)/2)))
       (BitVec.ofNat 64 (L.sharedBase+16))),
   (679,b32 (L.sharedBase+33792)),
   (682,b32 ((g/L.block)%2)),
   (691,b32 (256*((g/L.block)%2))),
   (684,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (683,b32 (L.sharedBase+50176)),
   (685,b32 ((g/L.block)%2)),
   (692,b32 (128*((g/L.block)%2))),
   (687,b32 (256*n+128*((g/L.block)%2))),
   (686,b32 (L.sharedBase+148480)),
   (688,b32 ((g/L.block)%2)),
   (27,.pred (decide ((g/L.block)%2 ≠ 0))),
   (693,b32 98304)]

def values3 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(708,b32 L.sharedBase),
   (694,b32 (L.sharedBase+56)),
   (695,b32 1),
   (696,b32 10000000),
   (699,b32 (64*(q+2))),
   (697,b32 ((g/L.block)%2)),
   (709,b32 (256*((g/L.block)%2))),
   (700,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (790, .ptr 32 false (.shared (g / L.block) (2* ((g/L.block)/2)))
       (BitVec.ofNat 64 (L.sharedBase+24))),
   (698,b32 (L.sharedBase+66560)),
   (701,b32 ((g/L.block)%2)),
   (710,b32 (256*((g/L.block)%2))),
   (703,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (702,b32 (L.sharedBase+82944)),
   (704,b32 ((g/L.block)%2)),
   (711,b32 (128*((g/L.block)%2))),
   (706,b32 (256*n+128*((g/L.block)%2))),
   (705,b32 (L.sharedBase+164864)),
   (707,b32 ((g/L.block)%2)),
   (28,.pred (decide ((g/L.block)%2 ≠ 0))),
   (712,b32 98304)]

def values4 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(727,b32 L.sharedBase),
   (713,b32 (L.sharedBase+64)),
   (714,b32 1),
   (715,b32 10000000),
   (718,b32 (64*(q+3))),
   (716,b32 ((g/L.block)%2)),
   (728,b32 (256*((g/L.block)%2))),
   (719,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (810, .ptr 32 false (.shared (g / L.block) (2* ((g/L.block)/2)))
       (BitVec.ofNat 64 (L.sharedBase+32))),
   (717,b32 (L.sharedBase+99328)),
   (720,b32 ((g/L.block)%2)),
   (729,b32 (256*((g/L.block)%2))),
   (722,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (721,b32 (L.sharedBase+115712)),
   (723,b32 ((g/L.block)%2)),
   (730,b32 (128*((g/L.block)%2))),
   (725,b32 (256*n+128*((g/L.block)%2))),
   (724,b32 (L.sharedBase+181248)),
   (726,b32 ((g/L.block)%2)),
   (29,.pred (decide ((g/L.block)%2 ≠ 0))),
   (731,b32 98304)]

def values5 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(746,b32 L.sharedBase),
   (732,b32 (L.sharedBase+40)),
   (733,b32 0),
   (734,b32 10000000),
   (737,b32 (64*(q+4))),
   (735,b32 ((g/L.block)%2)),
   (747,b32 (256*((g/L.block)%2))),
   (738,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (736,b32 (L.sharedBase+1024)),
   (739,b32 ((g/L.block)%2)),
   (748,b32 (256*((g/L.block)%2))),
   (741,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (740,b32 (L.sharedBase+17408)),
   (742,b32 ((g/L.block)%2)),
   (749,b32 (128*((g/L.block)%2))),
   (744,b32 (256*n+128*((g/L.block)%2))),
   (743,b32 (L.sharedBase+132096)),
   (745,b32 ((g/L.block)%2)),
   (30,.pred (decide ((g/L.block)%2 ≠ 0))),
   (751,b32 98304)]

def values6 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(766,b32 L.sharedBase),
   (752,b32 (L.sharedBase+48)),
   (753,b32 0),
   (754,b32 10000000),
   (757,b32 (64*(q+5))),
   (755,b32 ((g/L.block)%2)),
   (767,b32 (256*((g/L.block)%2))),
   (758,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (756,b32 (L.sharedBase+33792)),
   (759,b32 ((g/L.block)%2)),
   (768,b32 (256*((g/L.block)%2))),
   (761,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (760,b32 (L.sharedBase+50176)),
   (762,b32 ((g/L.block)%2)),
   (769,b32 (128*((g/L.block)%2))),
   (764,b32 (256*n+128*((g/L.block)%2))),
   (763,b32 (L.sharedBase+148480)),
   (765,b32 ((g/L.block)%2)),
   (31,.pred (decide ((g/L.block)%2 ≠ 0))),
   (771,b32 98304)]

def values7 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(786,b32 L.sharedBase),
   (772,b32 (L.sharedBase+56)),
   (773,b32 0),
   (774,b32 10000000),
   (777,b32 (64*(q+6))),
   (775,b32 ((g/L.block)%2)),
   (787,b32 (256*((g/L.block)%2))),
   (778,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (776,b32 (L.sharedBase+66560)),
   (779,b32 ((g/L.block)%2)),
   (788,b32 (256*((g/L.block)%2))),
   (781,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (780,b32 (L.sharedBase+82944)),
   (782,b32 ((g/L.block)%2)),
   (789,b32 (128*((g/L.block)%2))),
   (784,b32 (256*n+128*((g/L.block)%2))),
   (783,b32 (L.sharedBase+164864)),
   (785,b32 ((g/L.block)%2)),
   (32,.pred (decide ((g/L.block)%2 ≠ 0))),
   (791,b32 98304)]

def values8 (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  [(806,b32 L.sharedBase),
   (792,b32 (L.sharedBase+64)),
   (793,b32 0),
   (794,b32 10000000),
   (797,b32 (64*(q+7))),
   (795,b32 ((g/L.block)%2)),
   (807,b32 (256*((g/L.block)%2))),
   (798,b32 (outputRow (m) ((g/L.block)%2) 0 0)),
   (796,b32 (L.sharedBase+99328)),
   (799,b32 ((g/L.block)%2)),
   (808,b32 (256*((g/L.block)%2))),
   (801,b32 (outputRow (m) ((g/L.block)%2) 1 0)),
   (800,b32 (L.sharedBase+115712)),
   (802,b32 ((g/L.block)%2)),
   (809,b32 (128*((g/L.block)%2))),
   (804,b32 (256*n+128*((g/L.block)%2))),
   (803,b32 (L.sharedBase+181248)),
   (805,b32 ((g/L.block)%2)),
   (33,.pred (decide ((g/L.block)%2 ≠ 0))),
   (811,b32 98304)]

/-- All K-loop register values of one trip. -/
def table (L : Launch) (g m n q : Nat) : List (Nat × Value) :=
  values0 L g m n q ++ values1 L g m n q ++ values2 L g m n q ++ values3 L g m n q ++
    values4 L g m n q ++ values5 L g m n q ++ values6 L g m n q ++ values7 L g m n q ++
    values8 L g m n q

def value (L : Launch) (g m n q : Nat) (r : Nat) : Value :=
  ((table L g m n q).lookup r).getD (b32 0)

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
