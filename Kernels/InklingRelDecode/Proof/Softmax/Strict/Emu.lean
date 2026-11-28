-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Data.SwExp
public import Lemmas.Flow.SegQFQt
public import Lemmas.Flow.SegQPre

@[expose] public section

/-! # The sixteen software `exp2` instances between the generated windows

The windows end at pc 1913 and restart at 2089; the tags the lane carries across are those of
pc 1913 with the registers the instances clear removed and their outputs a datum of four bytes
(`emuEnv`). An instance is one local step, selected by the kernel's `swExp2`; its input is not
`+inf` (`LateR'`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The tags after an instance of the software `exp2` under the table `qt`: its output is a
datum, the registers it clears have no tag, and every other tag is one of the tags before. -/
def emuAfter (qt : Nat → EnvF) (pc : Nat) : Bool :=
  (qt (pc + 11)).all fun p =>
    if p.1 = Data.swR pc then p.2 == .dat32
    else !(Lib.emuW pc).contains p.1 && TagF.sat ((qt pc).lookup p.1) p.2

/-- **An instance of the software `exp2` is a strict segment** under the table `qt` whose tags
after it follow from those before (`emuAfter`): its input is not `+inf` (`LateR'`). -/
theorem seg_emu_qt {qt : Nat → EnvF} {pc : Nat} (hs : Assumptions.emuSites.contains pc = true)
    (hq : emuAfter qt pc = true) {F G : List (Nat × Value)} (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, p.1 ∉ Lib.emuW pc) :
    SegQ kernel Assumptions.all L g (fun t => QTF qt t ∧ TauAll kernel Assumptions.all L g
      (LateR' L g) t) pc F (pc + 11) G := by
  have hok : Data.emuSiteOk pc = true :=
    List.all_eq_true.mp Data.emuSites_ok pc (by simpa using hs)
  obtain ⟨op, hc, hl⟩ := Data.emuSite_code hok
  have hm : Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) [] =
      some (Lib.emuAsg pc) := by
    simp only [Data.emuSiteOk, Bool.and_eq_true] at hok
    cases h : Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) [] with
    | none => simp [h] at hok
    | some a => simp [Lib.emuAsg, h]
  intro t ht hQ
  obtain ⟨hpc, hsub, hacc, hft, hR⟩ := ht
  subst hpc
  obtain ⟨-, -, -, hexp⟩ := hQ.2 t .refl
  obtain ⟨x, hrd, hx⟩ := hexp hs hsub hacc _ hm
  obtain ⟨u, r, hu, hy, hs0, ha0, hf0⟩ : ∃ u r, Assumptions.execEmu (Lib.emuAsg t.pc) t =
      some (.ok u) ∧ u.regs (Data.swR t.pc) = some (.float .f32 r) ∧ u.sub = 0 ∧ u.acc = [] ∧
      u.fault = t.fault := by
    let r0 : ℝ := if x = ⊥ then 0 else Real.rpow 2 x.toReal
    let u : TState := { t with
      regs := Function.update (Assumptions.emuWrites.foldl
        (fun rs s => Function.update rs (Assumptions.emuReg (Lib.emuAsg t.pc) s) none) t.regs)
        (Data.swR t.pc) (some (.float .f32 r0)),
      pc := t.pc + Assumptions.emuBody.length, sub := 0, acc := [] }
    refine ⟨u, r0, ?_, by simp [u], rfl, rfl, rfl⟩
    simp only [Assumptions.execEmu, bindRead, hrd, hx, ite_false, pure, Except.pure, u, r0,
      Data.swR]
  have hseg : (Assumptions.swExp2 kernel).segmentRule L g t = some (.ok u) := by
    show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
        (Assumptions.execEmu · t) else none) = _
    simp only [hm, hs, hsub, hacc, List.isEmpty_nil, and_self, ite_true, Option.bind_some]
    exact hu
  have hfree : SegFreePc [Assumptions.idealArith, Assumptions.approx] t.pc := by
    intro a ha L g t _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  have hex : execLocalA Assumptions.all L g t op = .ok u :=
    execLocalA_select (A₁ := [Assumptions.idealArith, Assumptions.approx])
      (A₂ := Assumptions.all.drop 3) (hfree.at rfl) hseg
  have htau := tau_of_ok (A := Assumptions.all) (L := L) (g := g) hc hl hft hex
  obtain ⟨hu1, hu2⟩ := Lib.execEmu_spec hu
  have hwr : ∀ r', r' ∉ Lib.emuW t.pc → u.regs r' = t.regs r' := hu2
  refine ⟨u, .single htau, ⟨hu1, hs0, ha0, hf0.trans hft, Havoc.holds_of_forall fun p hp => ?_⟩,
    ?_, fun w hw => hQ.2 w (.head htau hw)⟩
  · rw [hwr _ (hd p hp)]
    exact holds_mem hR (hG p hp)
  · show TypedF (qt u.pc) u
    rw [hu1]
    intro r' tg hl
    have := List.all_eq_true.mp hq ⟨r', tg⟩ (lookup_mem' hl)
    by_cases hy' : r' = Data.swR t.pc
    · simp only [hy', ite_true, beq_iff_eq] at this
      subst this hy'
      exact ⟨_, hy, dat32_float r⟩
    · simp only [hy', ite_false, Bool.and_eq_true, Bool.not_eq_true'] at this
      rw [hwr r' (by simpa using this.1)]
      exact TagF.sat_ok this.2 fun tg' h' => hQ.1 r' tg' h'

/-- The tags before the `k`-th instance: those of pc 1913, minus what the instances so far clear,
plus their outputs. -/
def emuEnv : Nat → EnvF
  | 0 => lateQt 1913
  | k + 1 => (Data.swR (1913 + 11 * k), .dat32) ::
      (emuEnv k).filter fun p => !(Lib.emuW (1913 + 11 * k)).contains p.1

/-- The table of the region: `emuEnv` at the start of each instance, the lane's table elsewhere. -/
def emuQt (pc : Nat) : EnvF :=
  if 1913 ≤ pc ∧ pc ≤ 2089 ∧ (pc - 1913) % 11 = 0 then emuEnv ((pc - 1913) / 11) else lateQt pc

theorem emuQt_blk {k : Nat} (h : k ≤ 16) : emuQt (1913 + 11 * k) = emuEnv k := by
  have hc : 1913 ≤ 1913 + 11 * k ∧ 1913 + 11 * k ≤ 2089 ∧ (1913 + 11 * k - 1913) % 11 = 0 :=
    ⟨by omega, by omega, by omega⟩
  simp only [emuQt, hc, and_self, ite_true]
  congr 1
  omega

theorem emuSteps_ok : ∀ k < 16, emuAfter emuQt (1913 + 11 * k) = true := by decide +kernel

theorem emuEnd_ok : tagsInF (lateQt 2089) (emuQt 2089) = true := by decide +kernel

theorem emuStart_ok : tagsInF (emuQt 1913) (lateQt 1913) = true := by decide +kernel

/-- The first `n` instances, from the facts `F` to the facts `G` none of whose registers an
instance writes. -/
theorem seg_emu_n {F G : List (Nat × Value)} (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, ∀ k < 16, p.1 ∉ Lib.emuW (1913 + 11 * k)) :
    ∀ n ≤ 16, SegQ kernel Assumptions.all L g (fun t => QTF emuQt t ∧
      TauAll kernel Assumptions.all L g (LateR' L g) t) 1913 F (1913 + 11 * n) G
  | 0, _ => PTX.Flow.Havoc.SegQ.weaken fun _ hR =>
      Havoc.holds_of_forall fun p hp => holds_mem hR (hG p hp)
  | n + 1, hn => SegQ.comp (seg_emu_n hG hd n (by omega)) (by
      have := seg_emu_qt (L := L) (g := g) (qt := emuQt) (pc := 1913 + 11 * n)
        (by simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map,
          List.mem_range]; exact ⟨n, by omega, rfl⟩)
        (emuSteps_ok n (by omega)) (fun _ h => h) (fun p h => hd p h n (by omega))
      rwa [show 1913 + 11 * n + 11 = 1913 + 11 * (n + 1) by omega] at this)

/-- **The sixteen software `exp2` instances are one strict segment** from pc 1913 to pc 2089. -/
theorem seg_emus {F G : List (Nat × Value)} (hG : ∀ p ∈ G, p ∈ F)
    (hd : ∀ p ∈ G, ∀ k < 16, p.1 ∉ Lib.emuW (1913 + 11 * k)) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1913 F 2089 G :=
  qtfT_conv (seg_emu_n hG hd 16 le_rfl) (Or.inr emuStart_ok) (Or.inr emuEnd_ok)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
