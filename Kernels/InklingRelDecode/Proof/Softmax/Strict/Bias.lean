-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
public import Lemmas.Flow.TypedIntG
public import Lemmas.Flow.StepsQFPu
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The strict steps of the loads of the bias words (the preloads and the loop's)
The guarded load at `pc` writes its register; the move after it (for the next register) is the
span to the next load. -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The guarded weak load of two bytes at `pc` under the guard `gd` into the register `r`. -/
def ldOk (pc gd r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (q, false), .mem a⟩ =>
    q == gd && decide (a.kind = .load) && !a.nc && decide (a.ext = .same) && a.regs == [r]
  | _ => false

theorem ldOk_sound {pc gd r : Nat} (h : ldOk pc gd r = true) : ∃ a,
    kernel.code[pc]? = some ⟨some (gd, false), .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
      a.ext = .same ∧ a.regs = [r] := by
  unfold ldOk at h
  split at h
  · rename_i q a hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨rfl, hk⟩, hn⟩, he⟩, hr⟩ := h
    exact ⟨a, hc, hk, hn, he, hr⟩
  · cases h

/-- **A bias load**: the event returns a word of two bytes, the span after it goes to `f v`. -/
theorem ld_soft {d : Data.D} {f : Value → Data.D} {p r gd : Nat} (hp : d.c.site.pc = p)
    (hl : ldOk p gd r = true) (hb : p % 2 = 0 ∧ (680 ≤ p ∧ p ≤ 806 ∨ 1124 ≤ p ∧ p ≤ 1250))
    (hoff : ∀ q ∈ (Data.code e L g).facts d, q.1 ≠ r)
    (hn : ∀ x bs y, rebuild 3 bs = .ok y →
      Data.succ e L g d ⟨p, .rd x bs⟩ = some (some (f y)))
    (hi : ∀ y, Control.Inv e (g % L.block) d.c → Control.Inv e (g % L.block) (f y).c)
    (hq : afterF lateQt p [] = true) (hnk : r ∉ (lateQt (p + 1)).map Prod.fst)
    (seg : ∀ y, SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (p + 1)
      ((r, y) :: (Data.code e L g).facts d) (f y).c.site.pc
      ((Data.code e L g).facts (f y))) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf d ev := by
  subst hp
  obtain ⟨a, hc, hk, hnc, hext, hr⟩ := ldOk_sound hl
  refine Code.StepForQP.ofInv fun hinv => Code.ldWFPu (C := Data.code e L g) (d := d)
    (f := f) hc hk hnc hext hr ?_ (fun x bs v hv => hn x bs v hv) rfl rfl hoff hnk hq
    (fun v => ⟨rfl, rfl, hi v hinv, seg v⟩) ev
  intro e' he hpc x bs hk'
  exact he.bias (by rw [hpc]; exact hb.1) (by rw [hpc]; exact hb.2) x bs hk'

theorem pre_ld : ∀ j < 63, ldOk (680 + 2 * j) 85 (263 + j) = true := by decide +kernel

theorem pre_off : ∀ j < 63, 263 + j ∉ Control.ctlLive (680 + 2 * j) := by decide +kernel

theorem pre_aft : ∀ j < 63, afterF lateQt (680 + 2 * j) [] = true := by decide +kernel

theorem pre_nk : ∀ j < 63, 263 + j ∉ (lateQt (680 + 2 * j + 1)).map Prod.fst := by
  decide +kernel

theorem pre_mv : ∀ j < 63, checkW absF5 lateQt (680 + 2 * j + 1) (680 + 2 * j + 2)
    ((kernel.code.drop (680 + 2 * j + 1)).take (680 + 2 * j + 2 - (680 + 2 * j + 1)))
      [264 + j] = true := by
  decide +kernel

theorem pre_sub : ∀ j < 63, ∀ r ∈ Control.ctlLive (682 + 2 * j),
    r ∈ Control.ctlLive (680 + 2 * j) ∧ r ≠ 264 + j := by
  decide +kernel

/-- The move between two bias loads writes the register of the next load: a strict segment. -/
theorem mv_seg {p r : Nat} {F G : List (Nat × Value)} (hl : p + 2 ≤ 2331)
    (hP : FloatPlain3 Assumptions.all L g (p + 1) (p + 2))
    (hc : checkW absF5 lateQt (p + 1) (p + 2) ((kernel.code.drop (p + 1)).take (p + 2 - (p + 1)))
      [r] = true) (hw : ∀ q ∈ G, q.1 ≠ r) (hG : ∀ q ∈ G, q ∈ F) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (p + 1) F (p + 2) G := by
  refine SegQ.tauAll _ (segQF5_runW lateQt (W := [r]) (by omega)
    (by have := kernel_code_length; omega) hP hc (fun q hq => by simpa using hw q hq) hG)

/-- **A preload but the last** continues at the next one. -/
theorem sstep_pre (j : Fin 64) (hj : j.val + 1 < 64) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.pre j, i, v⟩, w⟩ ev := by
  have hj' : j.val < 63 := by omega
  have h2 := pre_off j.val hj'
  have h4 := pre_mv j.val hj'
  have h5 := pre_sub j.val hj'
  apply ld_soft (d := ⟨⟨.pre j, i, v⟩, w⟩) (p := 680 + 2 * j.val) (r := 263 + j.val)
    (f := fun y => ⟨⟨.pre ⟨j.val + 1, hj⟩, i, v⟩, {w with ld := Function.update w.ld j.val y}⟩)
    rfl (pre_ld j.val hj') ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩ ?_ ?_ ?_
    (pre_aft j.val hj') (pre_nk j.val hj') (fun y => ?_)
  · exact facts_ne h2 (by
      simp only [Data.dKeys, List.mem_cons, List.not_mem_nil, or_false]
      omega)
  · intro x bs y hy
    simp [Data.succ, Control.next, Data.record, Lib.loadWord, hy, hj, Data.loopB, Except.toOption]
  · intro y hi
    refine ⟨hi.entry, hi.thread, hi.bound, (by rintro (h | h) <;> cases h),
      fun _ _ => hi.pre j rfl, nofun, nofun, fun _ _ _ hp => absurd rfl (hp _)⟩
  · have e2 : 680 + 2 * (j.val + 1) = 682 + 2 * j.val := by omega
    refine mv_seg (p := 680 + 2 * j.val) (r := 264 + j.val) (by omega)
      ((fp3_of (a := 681) (b := 807) (by decide +kernel)).mono (by omega) (by omega)) h4 ?_ ?_
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact (h5 r (by rw [← e2]; exact hr)).2
      · have h' : q ∈ [(525, Data.scaleVal L), (498, Data.scaleW L)] := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with rfl | rfl <;> simp <;> omega
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (mem_factsFrom (h5 r (by rw [← e2]; exact hr)).1))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
