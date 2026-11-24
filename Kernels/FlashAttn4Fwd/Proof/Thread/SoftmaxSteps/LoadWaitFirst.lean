-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSpec
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The implicit waits of the first tile's first three loads

After the implicit wait of load `c < 3` the thread packs the 32 loaded words into 16 pairs
(`mov.b64 %rd, {a, b}`, `SegD.packs`) and reaches load `c + 1` when every word has four bytes
(`WaitOk`); otherwise it is dead. (The wait of the last load is followed by the row maximum,
`ArithSpec`.) -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The waits of the first tile's loads `0 … 2`. -/
theorem step_ldW0 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (_hpre : Pre P L mem0) (c : Fin 4)
    (hc3 : c.val < 3) (hs : d.site = .ldW false c) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨-, hu⟩ := ldW_at hs h hc hf
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  have hw8 := hi.warp
  have hin : ∀ c', Inv L g ⟨.ld false c', i, tt, s, m, l⟩ := fun c' =>
    inv_move hi rfl rfl rfl rfl (fun h0 => by simp_all [Site.tile0])
      (fun h0 => by simp_all [Site.inTrip]) (by simp)
  rcases fin4_cases c with rfl | rfl | rfl | rfl <;> simp at hc3
  · let d0 : D := ⟨.ldW false 0, i, tt, s, m, l⟩
    have hu' : At u 1267 (factsFrom (Flow.live 1266 ++ ldRegs false 0)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks false 0) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks false 0) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld false 1, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks false 0) = true)
      (fun hC => by
        have h' : WaitOk L g false 0 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g false 0 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 1267) (liveT := Flow.live 1283) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'
  · let d0 : D := ⟨.ldW false 1, i, tt, s, m, l⟩
    have hu' : At u 1284 (factsFrom (Flow.live 1283 ++ ldRegs false 1)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks false 1) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks false 1) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld false 2, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks false 1) = true)
      (fun hC => by
        have h' : WaitOk L g false 1 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g false 1 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 1284) (liveT := Flow.live 1300) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'
  · let d0 : D := ⟨.ldW false 2, i, tt, s, m, l⟩
    have hu' : At u 1301 (factsFrom (Flow.live 1300 ++ ldRegs false 2)
        (valueEx (valueOf L g d0) [])) := hu
    have hpk : (packVals (valueEx (valueOf L g d0) []) (ldPacks false 2) ++ []).map
        (fun p : Nat × Value => valueOf L g d0 p.1) =
        (packVals (valueEx (valueOf L g d0) []) (ldPacks false 2) ++ []).map Prod.snd := by
      kernel_rfl
    refine step_of_segD (d' := ⟨.ld false 3, i, tt, s, m, l⟩)
      (C := packsOk (valueEx (valueOf L g d0) []) (ldPacks false 2) = true)
      (fun hC => by
        have h' : WaitOk L g false 2 d0 := (waitOk_lt (by decide)).mpr hC
        simp only [next, d0, h', ite_true]; rfl)
      (fun hC => by
        have h' : ¬ WaitOk L g false 2 d0 := mt (waitOk_lt (by decide)).mp hC
        simp only [next, d0, h', ite_false]) (hin _) rfl rfl
      ((SegD.packs (pc := 1301) (liveT := Flow.live 1317) noPack_asms (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
          fun R h => holds_agree hpk h) hu'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
