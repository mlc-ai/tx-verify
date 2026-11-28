-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.LocalLanding
public import Kernels.InklingRelDecode.Proof.Softmax.Data.RunAdv
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # A software `exp2` instance on a register file

One generic step for every instance of the kernel's `_gl_ex2_emu` (pcs 1913 + 11 i): from a
register file that knows the input register (a number or `-inf`) the 11 instructions end 11 pcs
later with the output register holding `swY` of the input, the temporaries unknown and every
other known register as before. A `+inf` input is a fault (the thread is dead). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- The input register of the instance at `pc`. -/
def swX (pc : Nat) : Nat := Assumptions.emuReg (Lib.emuAsg pc) .x
/-- The output register of the instance at `pc`. -/
def swR (pc : Nat) : Nat := Assumptions.emuReg (Lib.emuAsg pc) .y

/-- **The output of an instance on its input word**: `2 ^ x` for the extended real `x` it reads
as (`0` for `-inf`). -/
def swY (v : Value) : Value :=
  match readEReal .f32 v with
  | some (.ok x) => .float .f32 (if x = ⊥ then 0 else Real.rpow 2 x.toReal)
  | _ => .bits 32 0

/-- The registers known after an instance: those known before but the ones it writes, and the
output. -/
def swK (pc : Nat) (K : List Nat) : List Nat :=
  K.filter (fun r => !(Lib.emuW pc).contains r) ++ [swR pc]

/-- The register file after an instance. -/
def swV (pc : Nat) (V : Nat → Value) : Nat → Value :=
  valueEx V [(swR pc, swY (V (swX pc)))]

/-- The instance's site checks: the instruction there is unguarded and local, and the template
matches the code. -/
def emuSiteOk (pc : Nat) : Bool :=
  (match kernel.code[pc]? with | some ⟨none, op⟩ => op.isLocal | _ => false) &&
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) []).isSome

theorem emuSites_ok : Assumptions.emuSites.all emuSiteOk = true := by decide +kernel

theorem emuSite_code {pc : Nat} (h : emuSiteOk pc = true) :
    ∃ op, kernel.code[pc]? = some ⟨none, op⟩ ∧ op.isLocal = true := by
  simp only [emuSiteOk, Bool.and_eq_true] at h
  rcases hc : kernel.code[pc]? with _ | ⟨_ | _, op⟩ <;> simp [hc] at h
  exact ⟨op, rfl, h.1⟩

theorem ni_read {v : Value} (h : SK.ni.Has v) :
    ∃ x : EReal, readEReal .f32 v = some (.ok x) ∧ x ≠ ⊤ := by
  obtain ⟨x, hx, lx⟩ := SK.lane_of (k := .ni) (by decide) h
  refine ⟨x, hx, ?_⟩
  rcases lx with ⟨r, rfl⟩ | rfl <;> simp

/-- **One instance of the software `exp2`** is one exact step, from a register file that knows
its input as a number or `-inf`. -/
theorem sw_seg {pc : Nat} (hs : Assumptions.emuSites.contains pc = true) {K : List Nat}
    {V : Nat → Value} (hx : swX pc ∈ K) (hn : SK.ni.Has (V (swX pc))) :
    Seg kernel Assumptions.all L g 1 pc (factsFrom K V) (pc + 11)
      (factsFrom (swK pc K) (swV pc V)) := by
  have hok : emuSiteOk pc = true := List.all_eq_true.mp emuSites_ok pc (by simpa using hs)
  obtain ⟨op, hc, hl⟩ := emuSite_code hok
  have hm : Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) [] =
      some (Lib.emuAsg pc) := by
    simp only [emuSiteOk, Bool.and_eq_true] at hok
    cases h : Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) [] with
    | none => simp [h] at hok
    | some a => simp [Lib.emuAsg, h]
  obtain ⟨xv, hxv, hxt⟩ := ni_read hn
  intro t ht
  obtain ⟨hpc, hsub, hacc, hft, hR⟩ := ht
  have hr := holds_mem hR (mem_factsFrom (val := V) hx)
  have hrd : readERealOpnd t .f32 (.reg (Assumptions.emuReg (Lib.emuAsg pc) .x)) =
      some (.ok xv) := by
    simp only [readERealOpnd, readReg, show Assumptions.emuReg (Lib.emuAsg pc) .x = swX pc from rfl,
      hr, pure, Except.pure, hxv]
  let u : TState := { t with
    regs := Function.update (Assumptions.emuWrites.foldl
      (fun rs s => Function.update rs (Assumptions.emuReg (Lib.emuAsg pc) s) none) t.regs)
      (swR pc) (some (swY (V (swX pc)))),
    pc := t.pc + Assumptions.emuBody.length, sub := 0, acc := [] }
  have hsw : swY (V (swX pc)) = .float .f32 (if xv = ⊥ then 0 else Real.rpow 2 xv.toReal) := by
    simp only [swY, hxv]
  have he : Assumptions.execEmu (Lib.emuAsg pc) t = some (.ok u) := by
    simp only [Assumptions.execEmu, bindRead, hrd, hxt, ite_false, hsw, u, swR, pure, Except.pure]
  have hseg : (Assumptions.swExp2 kernel).segmentRule L g t = some (.ok u) := by
    show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
        (Assumptions.execEmu · t) else none) = _
    have hcond : Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty = true :=
      ⟨hpc ▸ hs, hsub, by simp [hacc]⟩
    simp only [hpc, hm, hs, hsub, hacc, List.isEmpty_nil, and_self, ite_true, Option.bind_some]
    exact he
  have hfree : SegFreePc [Assumptions.idealArith, Assumptions.approx] pc := by
    intro a ha L g t _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  have hrun := run_select (A₁ := [Assumptions.idealArith, Assumptions.approx])
    (A₂ := Assumptions.all.drop 3) (pc := pc) hc hl ⟨hpc, hsub, hacc, hft, hR⟩ hseg hfree
  refine ⟨u, hrun, ?_⟩
  have hu := Lib.execEmu_spec (u := u) he
  have hyw : swR pc ∈ Lib.emuW pc := by simp [swR, Lib.emuW, Assumptions.emuWrites]
  refine ⟨by simp [hu.1, hpc], rfl, rfl, hft, holds_of_pointwise fun r hr => ?_⟩
  simp only [swK, List.mem_append, List.mem_filter, List.mem_singleton, Bool.not_eq_true'] at hr
  rcases hr with ⟨hrK, hrw'⟩ | rfl
  · have hrw : r ∉ Lib.emuW pc := fun h => by simp [h] at hrw'
    have hne : r ≠ swR pc := fun e => hrw (e ▸ hyw)
    rw [hu.2 r hrw]
    simp only [swV, valueEx, List.lookup, beq_false_of_ne hne, Option.getD_none]
    exact holds_mem hR (mem_factsFrom hrK)
  · simp [swV, valueEx, u, swR]

theorem sw_adv {pc : Nat} (hs : Assumptions.emuSites.contains pc = true) {K : List Nat}
    {V : Nat → Value} (hx : swX pc ∈ K) (hn : SK.ni.Has (V (swX pc))) :
    SegU kernel Assumptions.all L g pc (factsFrom K V) (pc + 11)
      (factsFrom (swK pc K) (swV pc V)) :=
  SegU.of_seg (sw_seg hs hx hn)

/-! ### The sixteen instances in a row -/

/-- The first pc of instance `i`. -/
def swPc (i : Nat) : Nat := 1913 + 11 * i

/-- The registers known after the first `n` instances. -/
def swKs (K : List Nat) : Nat → List Nat
  | 0 => K
  | n + 1 => swK (swPc n) (swKs K n)

/-- The register file after the first `n` instances. -/
def swVs (V : Nat → Value) : Nat → Nat → Value
  | 0 => V
  | n + 1 => swV (swPc n) (swVs V n)

/-- No instance reads a register an earlier one writes, and the outputs differ. -/
def swDisjoint : Bool :=
  (List.range 16).all fun i => (List.range i).all fun j =>
    swX (swPc i) != swR (swPc j) && !(Lib.emuW (swPc j)).contains (swX (swPc i)) &&
      swR (swPc i) != swR (swPc j)

theorem swDisjoint_ok : swDisjoint = true := by decide +kernel

theorem swPc_site {i : Nat} (h : i < 16) : Assumptions.emuSites.contains (swPc i) = true := by
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range, swPc]
  exact ⟨i, h, by omega⟩

private theorem swDis {i j : Nat} (hi : i < 16) (hj : j < i) :
    swX (swPc i) ≠ swR (swPc j) ∧ (Lib.emuW (swPc j)).contains (swX (swPc i)) = false ∧
      swR (swPc i) ≠ swR (swPc j) := by
  have := List.all_eq_true.mp (List.all_eq_true.mp swDisjoint_ok i (by simpa using hi)) j
    (by simpa using hj)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

theorem swDis_xy {i j : Nat} (hi : i < 16) (hj : j < i) : swX (swPc i) ≠ swR (swPc j) := by
  obtain ⟨h, -, -⟩ := swDis hi hj
  exact h

theorem swDis_xw {i j : Nat} (hi : i < 16) (hj : j < i) :
    (Lib.emuW (swPc j)).contains (swX (swPc i)) = false := by
  obtain ⟨-, h, -⟩ := swDis hi hj
  exact h

theorem swDis_yy {i j : Nat} (hi : i < 16) (hj : j < i) : swR (swPc i) ≠ swR (swPc j) := by
  obtain ⟨-, -, h⟩ := swDis hi hj
  exact h

theorem swVs_other {V : Nat → Value} {r : Nat} : ∀ {n : Nat},
    (∀ j < n, r ≠ swR (swPc j)) → swVs V n r = V r
  | 0, _ => rfl
  | n + 1, h => by
    have hn : r ≠ swR (swPc n) := h n (by omega)
    simp only [swVs, swV, valueEx, List.lookup, beq_false_of_ne hn, Option.getD_none]
    exact swVs_other fun j hj => h j (by omega)

theorem swKs_mem {K : List Nat} {r : Nat} : ∀ {n : Nat},
    (∀ j < n, (Lib.emuW (swPc j)).contains r = false) → r ∈ K → r ∈ swKs K n
  | 0, _, h => h
  | n + 1, hw, h => by
    simp only [swKs, swK, List.mem_append, List.mem_filter]
    exact .inl ⟨swKs_mem (fun j hj => hw j (by omega)) h, by
      have := hw n (by omega)
      simpa using this⟩

/-- The output register of instance `i` holds `swY` of its input, once it has run. -/
theorem swVs_out {V : Nat → Value} {i : Nat} : ∀ {n : Nat}, i < n → n ≤ 16 →
    swVs V n (swR (swPc i)) = swY (V (swX (swPc i)))
  | 0, h, _ => absurd h (by omega)
  | n + 1, h, hn => by
    by_cases e : i = n
    · subst e
      have hx : swVs V i (swX (swPc i)) = V (swX (swPc i)) :=
        swVs_other fun j hj => swDis_xy (by omega) hj
      simp only [swVs, swV, valueEx, List.lookup, beq_self_eq_true, Option.getD_some, hx]
    · have hne : swR (swPc i) ≠ swR (swPc n) := (swDis_yy (i := n) (by omega) (by omega)).symm
      simp only [swVs, swV, valueEx, List.lookup, beq_false_of_ne hne, Option.getD_none]
      exact swVs_out (by omega) (by omega)

/-- **The sixteen instances**, for inputs that are known numbers or `-inf`. -/
theorem sw_chain {K : List Nat} {V : Nat → Value} {n : Nat} (hn : n ≤ 16)
    (hx : ∀ i < n, swX (swPc i) ∈ K) (ht : ∀ i < n, SK.ni.Has (V (swX (swPc i)))) :
    SegU kernel Assumptions.all L g (swPc 0) (factsFrom K V) (swPc n)
      (factsFrom (swKs K n) (swVs V n)) := by
  induction n with
  | zero => exact fun t h => .inl ⟨t, .refl, h⟩
  | succ n ih =>
    have ih := ih (by omega) (fun i hi => hx i (by omega)) (fun i hi => ht i (by omega))
    have hs := sw_adv (L := L) (g := g) (swPc_site (i := n) (by omega)) (K := swKs K n)
      (V := swVs V n)
      (swKs_mem (fun j hj => swDis_xw (by omega) hj) (hx n (by omega)))
      (by rw [swVs_other fun j hj => swDis_xy (by omega) hj]; exact ht n (by omega))
    have e : swPc n + 11 = swPc (n + 1) := by simp only [swPc]; omega
    rw [e] at hs
    exact ih.comp hs

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
