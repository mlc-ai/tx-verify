-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The implicit waits of a loop tile's first three loads

After the implicit wait of load `c < 3` the thread packs the 32 loaded words into 16 pairs
(`mov.b64 %rd, {a, b}`, `SegD.packs`) and reaches load `c + 1` when every word has four bytes
(`WaitOk`); otherwise it is dead. (The wait of the last load is followed by the row maximum,
`ArithSpec`.) -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The waits of a loop tile's loads `0 … 2`. -/
theorem step_ldW1 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (_hpre : Pre P L mem0) (c : Fin 4)
    (hc3 : c.val < 3) (hs : d.site = .ldW true c) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨-, hu⟩ := ldW_at hs h hc hf
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  have hw8 := hi.warp
  have hin : ∀ c', Inv L g ⟨.ld true c', i, tt, s, m, l⟩ := fun c' =>
    inv_move hi rfl rfl rfl rfl (fun h0 => by simp_all [Site.tile0])
      (fun h0 => by simp_all [Site.inTrip]) (by simp)
  rcases fin4_cases c with rfl | rfl | rfl | rfl <;> simp at hc3
  · let d0 : D := ⟨.ldW true 0, i, tt, s, m, l⟩
    have hu' : At u 2729 (factsFrom (Flow.live 2728 ++ ldRegs true 0)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks true 0) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks true 0) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld true 1, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks true 0) = true)
      (fun hC => by
        have h' : WaitOk L g true 0 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g true 0 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 2729) (liveT := Flow.live 2745) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'
  · let d0 : D := ⟨.ldW true 1, i, tt, s, m, l⟩
    have hu' : At u 2746 (factsFrom (Flow.live 2745 ++ ldRegs true 1)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks true 1) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks true 1) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld true 2, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks true 1) = true)
      (fun hC => by
        have h' : WaitOk L g true 1 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g true 1 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 2746) (liveT := Flow.live 2762) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'
  · let d0 : D := ⟨.ldW true 2, i, tt, s, m, l⟩
    have hu' : At u 2763 (factsFrom (Flow.live 2762 ++ ldRegs true 2)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks true 2) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks true 2) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld true 3, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks true 2) = true)
      (fun hC => by
        have h' : WaitOk L g true 2 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g true 2 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 2763) (liveT := Flow.live 2779) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
