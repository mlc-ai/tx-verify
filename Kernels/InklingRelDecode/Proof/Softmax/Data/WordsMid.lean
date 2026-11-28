-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Pairs
public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartRegion

@[expose] public section

/-! # The bias words kept by the sites that neither load nor pack

Between the loop's loads and the pack after the round the facts of the bias words only shrink
(the packs are dropped after the score load): the event writes none of them and the code up to
the next event is in a region that writes none (`ivsW`). `succs` lists the sites a site can be
followed by. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The sites a site can be followed by. -/
def succs : Site → List Site
  | .setMaxReg => [.bar0]
  | .bar0 => [.pre 0, .waitS, .nxt 0, .epilogue]
  | .pre j => if h : j.val + 1 < 64 then [.pre ⟨j.val + 1, h⟩] else [.waitS, .nxt 0, .epilogue]
  | .nxt j => if h : j.val + 1 < 64 then [.nxt ⟨j.val + 1, h⟩] else [.waitS]
  | .waitS => [.shfl4, .waitS]
  | .shfl4 => [.ldS]
  | .ldS => [.waitLd]
  | .waitLd => [.shfl5]
  | .shfl5 => [.shfl6]
  | .shfl6 => [.bar20, .waitO]
  | .waitO => [.bar22, .waitO]
  | .bar22 => [.shfl7]
  | .shfl7 => [.shfl8]
  | .shfl8 => [.shfl9]
  | .shfl9 => [.shfl10]
  | .shfl10 => [.store10]
  | .store10 => [.bar23]
  | .bar23 => [.ldL]
  | .ldL => [.shfl11]
  | .shfl11 => [.shfl12]
  | .shfl12 => [.bar20, .ldO]
  | .ldO => [.waitLdO]
  | .waitLdO => [.bar24]
  | .bar24 => [.stO]
  | .stO => [.waitStO]
  | .waitStO => [.bar20]
  | .bar20 => [.tmemSt]
  | .tmemSt => [.tmemWait]
  | .tmemWait => [.bar21]
  | .bar21 => [.arrive, .nxt 0, .waitS, .epilogue]
  | .arrive => [.nxt 0, .waitS, .epilogue]
  | .epilogue => []

theorem next_mem {d : D} {ev : Event} {c' : Control.D}
    (h : Control.next e L g d.c ev = some (some c')) : c'.site ∈ succs d.c.site := by
  cases hs : d.c.site <;> simp only [Control.next, hs] at h <;> (try split at h) <;>
    (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
    simp only [succs] <;> (try split_ifs) <;> simp [advance]
  all_goals first
    | (rcases loopSite_mem e (g % L.block) (d.c.i + 1) with h | h | h <;> simp [h])
    | (rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h])

/-- The region the code after a site of the round runs in. -/
def ivsW : List (Nat × Nat) := [(949, 64), (1257, 1074), (2560, 6)]

/-- The checks of a site of the round: its position, the next, and what its event writes. -/
def siteW (s : Site) : Bool :=
  inIvs ivsW s.pc && inIvs ivsW (s.pc + 1) && !Assumptions.emuSites.contains s.pc &&
  (match kernel.code[s.pc]? with
    | some ins => (packK ++ nwK).all fun r => !(eventWrites ins.op).contains r
    | none => true)

/-- The facts of the successors are among the site's. -/
def subB (s : Site) : Bool :=
  (succs s).all fun z => (!wP z || wP s) && decide (wN z ≤ wN s) && (match z with
    | .pre _ => false | _ => true)

theorem wordF_sub {reg : Nat → Nat} {ws : Nat → Value} {n m : Nat} (h : n ≤ m) :
    ∀ x ∈ wordF reg ws n, x ∈ wordF reg ws m := by
  intro x hx
  simp only [wordF, List.mem_map, List.mem_range] at hx ⊢
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, by omega, rfl⟩

theorem wFS_np {s : Site} (h : ∀ j, s ≠ .pre j) (v : Vals) :
    wFS s v = (if wP s then packF v.cur else []) ++ wordF nxtReg v.ld (wN s) := by
  cases s <;> first | rfl | exact absurd rfl (h _)

theorem wFS_sub {s z : Site} (hm : midB s = true) (h : subB s = true) (hz : z ∈ succs s)
    (v : Vals) : ∀ x ∈ wFS z v, x ∈ wFS s v := by
  simp only [subB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h z hz
  have hs : ∀ j, s ≠ .pre j := by rintro j rfl; simp [midB] at hm
  have hz' : ∀ j, z ≠ .pre j := by rintro j rfl; simp at h3
  intro x hx
  rw [wFS_np hz'] at hx
  rw [wFS_np hs]
  simp only [List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · refine .inl ?_
    by_cases hp : wP z = true
    · have := h1.resolve_left (by simp [hp])
      simpa [hp, this] using hx
    · simp [hp] at hx
  · exact .inr (wordF_sub h2 x hx)

theorem wN_le (s : Site) : wN s ≤ 64 := by
  cases s <;> first | decide | (rename_i j; simp only [wN]; omega)

theorem wFS_keyEq (s : Site) (v : Vals) (hs : ∀ j, s ≠ .pre j) :
    (wFS s v).map Prod.fst = (if wP s then packK else []) ++ (List.range (wN s)).map nxtReg := by
  rw [wFS_np hs]
  simp only [List.map_append, apply_ite (List.map Prod.fst), packF, wordF, packK,
    List.map_map, Function.comp_def, List.map_nil]

theorem wFS_congr (s : Site) {v w : Vals} (h1 : v.ld = w.ld) (h2 : v.cur = w.cur) :
    wFS s v = wFS s w := by
  cases s <;> simp [wFS, h1, h2]

theorem wFS_keys (s : Site) (v : Vals) (hs : ∀ j, s ≠ .pre j) :
    ∀ r ∈ (wFS s v).map Prod.fst, r ∈ packK ++ nwK := by
  intro r hr
  rw [wFS_keyEq s v hs, List.mem_append] at hr
  rw [List.mem_append]
  rcases hr with hr | hr
  · split at hr
    · exact .inl hr
    · simp at hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact .inr (List.mem_map.mpr ⟨k, List.mem_range.mpr
      (lt_of_lt_of_le (List.mem_range.mp hk) (wN_le s)), rfl⟩)

theorem record_wd {d : D} (ev : Event) (z : Site) (h : midB d.c.site = true) :
    (record L d ev z).ld = d.v.ld ∧ (record L d ev z).cur = d.v.cur := by
  unfold record
  split <;> simp_all [midB] <;> split <;> simp
