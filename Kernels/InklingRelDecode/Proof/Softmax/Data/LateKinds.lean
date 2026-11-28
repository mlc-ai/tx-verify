-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Flow.OutKinds
public import Lemmas.Flow.OutPre

@[expose] public section

/-! # What the kinds of a run say at the pack inside it

A prefix of an accepted run is accepted (`kRun_take`). At a pack `cvt.rn.bf16x2.f32` inside a run
whose registers are `xFinal V (take j items)`, both sources are written before it or read from the
start, and have a kind up to `ni` (`packSites`): they read as extended reals. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Iface

theorem kRun_take : ∀ {items : List XItem} {K K' : Nat → Kd}, kRun K items = some K' →
    ∀ j, ∃ K'', kRun K (items.take j) = some K''
  | [], _, _, h, j => ⟨_, by simpa using h⟩
  | it :: its, K, K', h, j => by
    cases j with
    | zero => exact ⟨K, rfl⟩
    | succ j =>
      obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp (by simpa only [kRun] using h)
      obtain ⟨K2, h3⟩ := kRun_take h2 j
      exact ⟨K2, by simp only [List.take_succ_cons, kRun, h1, Option.bind_some, h3]⟩

theorem kFns_take : ∀ {items : List XItem}, kFns items → ∀ j, kFns (items.take j)
  | [], _, j => by simp [kFns]
  | it :: its, h, j => by
    cases j with
    | zero => exact trivial
    | succ j => exact ⟨h.1, kFns_take h.2 j⟩

/-- A source of kind at most `ni`, written by the run before the pack or read from the start. -/
def srcOk (K : Nat → Kd) (dom ws : List Nat) : Opnd → Bool
  | .reg a => (ws.contains a || dom.contains a) &&
    match K a with | .s k => k.le .ni | _ => false
  | _ => false

/-- **The packs of a run read numbers**: at each pc of the run that is a pack, the sources. -/
def packSites (K : Nat → Kd) (items : List XItem) (dom : List Nat) (s0 : Nat) : Bool :=
  (List.range items.length).all fun j =>
    match kernel.code[s0 + j]? with
    | some ⟨_, .cvt c⟩ => !packOp (.cvt c) ||
        c.srcs.all (srcOk (kOut K (items.take j)) dom (xWrites (items.take j)))
    | _ => true

/-- **A pack inside a run reads extended reals**, from the kinds of the run's start. -/
theorem pack_reads {K K' : Nat → Kd} {items : List XItem} {dom : List Nat} {s0 j : Nat}
    {V : Nat → Value} {t : TState}
    (hk : kRun K items = some K') (hF : kFns items) (hV : ∀ r, (K r).Has (V r))
    (hs : packSites K items dom s0 = true) (hj : j < items.length) (hpc : t.pc = s0 + j)
    (hregs : ∀ r ∈ xWrites (items.take j) ++ dom,
      t.regs r = some (xFinal V (items.take j) r)) {c : CvtInstr}
    (hc : kernel.code[t.pc]? = some ⟨none, .cvt c⟩) (hp : packOp (.cvt c) = true) :
    ∀ r ∈ c.srcs, ∀ a, r = .reg a → ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x) := by
  intro r hr a hra
  subst hra
  obtain ⟨K1, h1⟩ := kRun_take hk j
  have hsj := List.all_eq_true.mp hs j (List.mem_range.mpr hj)
  rw [← hpc, hc] at hsj
  simp only [hp, Bool.not_true, Bool.false_or, List.all_eq_true] at hsj
  have hrr := hsj _ hr
  simp only [srcOk, kOut, h1, Option.getD_some, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at hrr
  obtain ⟨hmem, hkd⟩ := hrr
  have hmem' : a ∈ xWrites (items.take j) ++ dom := by
    rcases hmem with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h
  have hval := (kRun_sound h1 hV (kFns_take hF j)).2 a
  rw [readERealOpnd_reg (hregs a hmem')]
  cases hka : K1 a with
  | s k =>
    rw [hka] at hkd hval
    obtain ⟨x, hx, -⟩ := SK.lane_of (by simpa using hkd) hval
    exact ⟨x, hx⟩
  | _ => rw [hka] at hkd; simp at hkd

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
