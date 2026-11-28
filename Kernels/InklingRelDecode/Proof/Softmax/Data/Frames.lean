-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale


@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option hygiene false in
macro "ds_frame" "(" s:term "," zs:term "," S:term ")" : tactic => `(tactic| (
  apply dstep_site (s := $s) (zs := $zs) hs $S (by decide +kernel) (by decide +kernel)
  · intro ev c' h
    simp only [Control.next, hs] at h
    (try split at h) <;> first | (simp at h; done) |
      (simp only [Option.some.injEq] at h; subst h; (try split) <;> simp [advance, loopSite] <;>
        split_ifs <;> simp_all)
  · intro ev z hz
    first | exact record_main ev z (by rw [hs]; rfl) | simp [record, hs, Vals.main]
  · intro v z hz x hx
    simp [dFS, inRound] at hz hx ⊢
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all [dFS, inRound]))

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem data_setMaxReg {d : D} (hs : d.c.site = .setMaxReg) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.setMaxReg, [.bar0], [])

theorem data_waitS {d : D} (hs : d.c.site = .waitS) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.waitS, [.shfl4, .waitS], [(1258, 3)])

theorem data_shfl4 {d : D} (hs : d.c.site = .shfl4) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl4, [.ldS], [(1262, 3)])

theorem data_ldS {d : D} (hs : d.c.site = .ldS) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.ldS, [.waitLd], [(1266, 32)])

theorem data_waitLd {d : D} (hs : d.c.site = .waitLd) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.waitLd, [.shfl5], [(1299, 539)])

theorem data_bar22 {d : D} (hs : d.c.site = .bar22) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.bar22, [.shfl7], [])

theorem data_waitO {d : D} (hs : d.c.site = .waitO) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.waitO, [.bar22, .waitO], [(2240, 1)])

theorem data_shfl7 {d : D} (hs : d.c.site = .shfl7) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl7, [.shfl8], [(2243, 1)])

theorem data_shfl8 {d : D} (hs : d.c.site = .shfl8) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl8, [.shfl9], [(2245, 1)])

theorem data_shfl9 {d : D} (hs : d.c.site = .shfl9) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl9, [.shfl10], [(2247, 1)])

theorem data_shfl10 {d : D} (hs : d.c.site = .shfl10) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl10, [.store10], [(2249, 1)])

theorem data_store10 {d : D} (hs : d.c.site = .store10) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.store10, [.bar23], [])

theorem data_bar23 {d : D} (hs : d.c.site = .bar23) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.bar23, [.ldL], [])

theorem data_ldL {d : D} (hs : d.c.site = .ldL) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.ldL, [.shfl11], [])

theorem data_shfl11 {d : D} (hs : d.c.site = .shfl11) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.shfl11, [.shfl12], [(2254, 1)])

theorem data_bar24 {d : D} (hs : d.c.site = .bar24) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.bar24, [.stO], [(2327, 2)])

theorem data_stO {d : D} (hs : d.c.site = .stO) :
    DataStep (code e L g) (dF L) d := by
  apply dstep_site (s := .stO) (zs := [.waitStO]) hs [(2328, 1)] (by decide +kernel)
    (by decide +kernel)
  · intro ev c' h
    simp only [Control.next, hs] at h
    simp only [Option.some.injEq] at h
    subst h
    simp
  · intro ev z hz
    exact record_main ev z (by rw [hs]; rfl)
  · intro v z hz x hx
    simp only [List.mem_singleton] at hz
    subst hz
    simp only [dFS, inRound, ↓reduceIte] at hx
    exact round_sub_rs2 v x hx

theorem data_bar20 {d : D} (hs : d.c.site = .bar20) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.bar20, [.tmemSt], [(1000, 10)])

theorem data_tmemSt {d : D} (hs : d.c.site = .tmemSt) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.tmemSt, [.tmemWait], [(1009, 1)])

theorem data_tmemWait {d : D} (hs : d.c.site = .tmemWait) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.tmemWait, [.bar21], [(1011, 1)])

theorem data_bar21 {d : D} (hs : d.c.site = .bar21) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.bar21, [.arrive, .nxt 0, .waitS, .epilogue], [(1013, 244), (2560, 5)])

theorem data_arrive {d : D} (hs : d.c.site = .arrive) :
    DataStep (code e L g) (dF L) d := by
  ds_frame (.arrive, [.nxt 0, .waitS, .epilogue], [(1013, 244), (2560, 5)])

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
