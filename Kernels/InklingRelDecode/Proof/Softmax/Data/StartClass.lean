-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartRegion
public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedSite
import Kernels.InklingRelDecode.Proof.Lib.Havoc

@[expose] public section

/-! # The derived constants at the states that keep them

The preloads (before the loop's first stop) keep `keysB`, the loop's sites keep `keysC`: one region
check each (`DataStep.constAny`) and the control machine's successor classes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The sites before the loop: the register increase, the barrier and the preloads. -/
def isEarly : Site → Bool
  | .setMaxReg | .bar0 | .pre _ => true
  | _ => false

/-- A site after the loop's start is followed by one. -/
theorem next_late {d d' : Control.D} {ev : Event}
    (h : Control.next e L g d ev = some (some d')) (hd : isEarly d.site = false) :
    isEarly d'.site = false := by
  obtain ⟨s, i, held⟩ := d
  simp only at hd
  cases s <;> simp only [Control.next] at h <;> simp only [isEarly] at hd <;>
    (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
    simp [advance, loopSite] <;> (try split_ifs) <;> (try simp [isEarly]) <;>
    (try simp at hd)

/-- A preload but the last is followed by a preload. -/
theorem next_pre {d d' : Control.D} {ev : Event} {j : Fin 64} (hs : d.site = .pre j)
    (hj : j.val < 63) (h : Control.next e L g d ev = some (some d')) : ∃ k, d'.site = .pre k := by
  obtain ⟨s, i, held⟩ := d
  simp only at hs
  subst hs
  simp only [Control.next, Option.some.injEq] at h
  have : j.val + 1 < 64 := by omega
  simp only [this, ↓reduceDIte] at h
  subst h
  exact ⟨_, rfl⟩

def ivsB : List (Nat × Nat) := [(680, 1651), (2560, 6)]
def ivsC : List (Nat × Nat) := [(943, 1388), (2560, 6)]

theorem region_B : regionH kernel Lib.hooks ivsB keysB = true := by decide +kernel
theorem region_C : regionH kernel Lib.hooks ivsC keysC = true := by decide +kernel

/-- The checks of a site: its position and the next lie in the region, no segment starts there,
and its event writes none of the registers. -/
def siteK (ivs : List (Nat × Nat)) (keys : List Nat) (s : Site) : Bool :=
  inIvs ivs s.pc && inIvs ivs (s.pc + 1) && !Assumptions.emuSites.contains s.pc &&
  (match kernel.code[s.pc]? with
    | some ins => keys.all fun r => !(eventWrites ins.op).contains r
    | none => true)

theorem siteB_ok (j : Fin 64) (h : j.val < 63) : siteK ivsB keysB (.pre j) = true := by
  revert j; decide +kernel

theorem siteC2_ok (s : Site) (h : isEarly s = false) (h' : s ≠ .epilogue) :
    siteK ivsC keysC s = true := by
  cases s with
  | nxt j => revert j; decide +kernel
  | epilogue => exact absurd rfl h'
  | pre j => exact absurd h (by simp [isEarly])
  | _ => first | decide +kernel | exact absurd h (by simp [isEarly])

theorem derF_late {s : Site} (h : isEarly s = false) (h' : s ≠ .epilogue) :
    derF e L g s = factsFrom keysC (derV e L g) := by
  cases s <;> simp_all [derF, isEarly]

theorem derF_cases {s : Site} (h : isEarly s = false) :
    derF e L g s = [] ∨ derF e L g s = factsFrom keysC (derV e L g) := by
  by_cases h' : s = .epilogue
  · subst h'; exact .inl rfl
  · exact .inr (derF_late h h')

theorem keys_factsFrom (ks : List Nat) (v : Nat → Value) : (factsFrom ks v).map Prod.fst = ks := by
  simp [factsFrom, List.map_map, Function.comp_def]

/-- **The derived constants of a loop site** are kept by its event and the code after it. -/
theorem der_loop {d : D} (hs : isEarly d.c.site = false) (hne : d.c.site ≠ .epilogue) :
    DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  have ok := siteC2_ok d.c.site hs hne
  simp only [siteK, Bool.and_eq_true, Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
  have key : DataStep (codeS e L g) (fun d => derF e L g d.c.site) d :=
    DataStep.constAny (C := codeS e L g) (sF := fun d => derF e L g d.c.site) (d := d)
    (A := Assumptions.all) (tab := Lib.hooks) (ivs := ivsC)
    Lib.rulesFrame hooks_any (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩
    (fun R h => ((holds_append _ _ _).mp
      ((holds_append _ _ _).mp ((holds_append _ _ _).mp h).2).2).1) (fun ins hc => ?_)
    (by simp only [derF_late hs hne, keys_factsFrom]; exact region_C) ?_
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    simp only [derF_late hs hne, keys_factsFrom]
    exact h4
  · intro ev d' hn x hx
    obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
    rcases derF_cases (e := e) (L := L) (g := g) (next_late hnc hs) with h | h
    · simp [h] at hx
    · rw [derF_late hs hne]
      rw [h] at hx
      exact hx

/-- **The derived constants of a preload but the last** are kept. -/
theorem der_pre {d : D} {j : Fin 64} (hs : d.c.site = .pre j) (hj : j.val < 63) :
    DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  have ok := siteB_ok j hj
  simp only [siteK, Bool.and_eq_true, Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
  rw [← hs] at h1 h2 h3 h4
  have key : DataStep (codeS e L g) (fun d => derF e L g d.c.site) d :=
    DataStep.constAny (C := codeS e L g) (sF := fun d => derF e L g d.c.site) (d := d)
    (A := Assumptions.all) (tab := Lib.hooks) (ivs := ivsB)
    Lib.rulesFrame hooks_any (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩
    (fun R h => ((holds_append _ _ _).mp
      ((holds_append _ _ _).mp ((holds_append _ _ _).mp h).2).2).1) (fun ins hc => ?_)
    (by simp only [hs, derF, keys_factsFrom]; exact region_B) ?_
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    simp only [hs, derF, keys_factsFrom]
    exact h4
  · intro ev d' hn x hx
    obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
    obtain ⟨k, hk⟩ := next_pre hs hj hnc
    simpa [hs, hk, derF] using hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
