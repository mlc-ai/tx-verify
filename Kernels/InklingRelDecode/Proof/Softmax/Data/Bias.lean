-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Site
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The code the preloads of the first block may run through (their guards may all be false). -/
def preIvs : List (Nat × Nat) := [(680, 319), (1049, 208), (2560, 5)]

/-- The code the later blocks' loads may run through. -/
def nxtIvs : List (Nat × Nat) := [(1124, 133)]

theorem pre_ivs : ivsOk preIvs [525, 498] = true := by decide +kernel
theorem nxt_ivs : ivsOk nxtIvs [498, 1914] = true := by decide +kernel

theorem pre_ok : ∀ j : Fin 63,
    siteOk (.pre ⟨j, by omega⟩) [.pre ⟨j + 1, by omega⟩] preIvs = true := by decide +kernel

theorem nxt_ok : ∀ j : Fin 63,
    siteOk (.nxt ⟨j, by omega⟩) [.nxt ⟨j + 1, by omega⟩] nxtIvs = true := by decide +kernel

theorem data_nxt {d : D} {j : Fin 64} (hs : d.c.site = .nxt j) :
    DataStep (code e L g) (dF L) d := by
  by_cases h : j.val + 1 < 64
  · have ok := nxt_ok ⟨j.val, by omega⟩
    apply dstep_site (s := .nxt j) (zs := [.nxt ⟨j.val + 1, h⟩]) hs nxtIvs ok nxt_ivs
    · intro ev c' hc
      simp only [Control.next, hs, h, ↓reduceDIte, Option.some.injEq] at hc
      subst hc
      simp
    · intro ev z hz
      exact record_main ev z (by rw [hs]; rfl)
    · intro v z hz x hx
      simp [dFS, inRound] at hz hx ⊢
      subst hz
      simp_all
  · have jj : j = 63 := Fin.ext (by omega)
    subst jj
    apply dstep_site (s := .nxt 63) (zs := [.waitS]) hs [(1250, 7)] (by decide +kernel)
      (by decide +kernel)
    · intro ev c' hc
      simp only [Control.next, hs, h, ↓reduceDIte, Option.some.injEq] at hc
      subst hc
      simp
    · intro ev z hz
      exact record_main ev z (by rw [hs]; rfl)
    · intro v z hz x hx
      simp [dFS, inRound] at hz hx ⊢
      subst hz
      simp_all

theorem data_pre {d : D} {j : Fin 64} (hs : d.c.site = .pre j) (h : j.val + 1 < 64) :
    DataStep (code e L g) (dF L) d := by
  have ok := pre_ok ⟨j.val, by omega⟩
  apply dstep_site (s := .pre j) (zs := [.pre ⟨j.val + 1, h⟩]) hs preIvs ok pre_ivs
  · intro ev c' hc
    simp only [Control.next, hs, h, ↓reduceDIte, Option.some.injEq] at hc
    subst hc
    simp
  · intro ev z hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact record_main_pre ev _ j hs (by simp)
  · intro v z hz x hx
    simp [dFS] at hz hx ⊢
    subst hz
    simpa [dFS] using hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
