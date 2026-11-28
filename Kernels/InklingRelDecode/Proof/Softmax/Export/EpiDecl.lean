-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Lib.WinKeep
import Kernels.InklingRelDecode.Proof.Lib.LanePre
import Kernels.InklingRelDecode.Proof.Softmax.Data.EpiKinds
import Kernels.InklingRelDecode.Proof.Softmax.Export.EpiChain
import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.OutRunCond

/-! # The epilogue's products are not declined

A state of a lane at the products (pcs 2642 to 2673) comes from the state after the wait of pc 2608
through the 33 packs. The words the load of pc 2607 returned and the reciprocal (register 1761) are
numbers, so the packs' outputs are pairs of numbers and the products are defined. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Assumption Data Lib

variable {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private def epWin : List (Nat × Nat) := [(2609, 2673)]
private def epTail : List (Nat × Nat) := [(2642, 2846)]
private def epR : List Nat := (List.range 33).map (2346 + ·)

private theorem ep_keep : keepOk epWin [] = true := by decide +kernel
private theorem ep_enter : enterOk epWin 0 = true := by decide +kernel
private theorem ep_zero : inS epWin 0 = false := by decide +kernel
private theorem ep_events : ∀ q ∈ entryEvents epWin, q = 2608 := by decide +kernel
private theorem tl_fwd : fwdOk epTail epR = true := by decide +kernel

/-- **The products of pcs 2642 to 2673 are not declined**, when the load's words and the
reciprocal at pc 2603 are numbers. -/
public theorem epi_decl {X : Execution} {t : TState}
    (hO : ∀ k a vals sh, X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (hR : ∀ s, Iface.LaneState L X g s → s.pc = 2603 → ∃ v, s.regs 1761 = some v ∧ SK.fl.Has v)
    (hl : Iface.LaneState L X g t) (h1 : 2642 ≤ t.pc) (h2 : t.pc ≤ 2673) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) : execIdealFloat L g t i.op ≠ none := by
  have hin : inS epWin t.pc = true := by simp only [inS, epWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, -, hev, hin0, hrt, -⟩ :=
    lane_set_keep ep_keep ep_enter ep_zero hl hin
  obtain ⟨s, hls, hes⟩ := lane_pre hk hr1
  have h08 := ep_events e.pc (by simpa [entryEvents] using hev)
  have hspc := EventFrame.estep_source_pc hes
  have hpost := post_pc hes
  have hs08 : s.pc = 2608 := by omega
  have ht09 : t0.pc = 2609 := by simp only [inS, epWin] at hin0; simp at hin0; omega
  obtain ⟨k', a, vals, sh, s', hget, hls', hs'pc, hlen, hwords, h61⟩ := after_ld hls hs08
  obtain ⟨s'', hls'', hs''pc, heq⟩ := before_ld hls' hs'pc
  obtain ⟨v1, hv1, hf1⟩ := hR s'' hls'' hs''pc
  have hkeep : ∀ r, t0.regs r = s.regs r := fun r => by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes
    rw [hs08, Flow.code_2608] at hci
    obtain rfl := (Option.some.inj hci).symm
    exact estep_keeps hes _ (by rw [hs08, Flow.code_2608]) r
      (by simp [EventFrame.eventWrites, writesRegs])
  have hex : ∀ r, (r = 1761 ∨ (1763 ≤ r ∧ r < 1827)) →
      ∃ w, t0.regs r = some w ∧ SK.fl.Has w := by
    intro r hr
    rcases hr with rfl | ⟨hr1, hr2⟩
    · exact ⟨v1, by rw [hkeep, h61, heq]; exact hv1, hf1⟩
    · have hlt : r - 1763 < vals.length := by omega
      obtain ⟨w, hw⟩ : ∃ w, vals[r - 1763]? = some w :=
        ⟨vals[r - 1763], List.getElem?_eq_getElem hlt⟩
      refine ⟨w, ?_, hO k' a vals sh hget w (List.mem_of_getElem? hw)⟩
      rw [hkeep, show r = 1763 + (r - 1763) by omega, hwords _ (by omega)]
      simpa using hw
  have hV : ∀ r, (epiK r).Has ((fun r => (t0.regs r).getD (.bits 32 0)) r) := fun r => by
    by_cases hr : r = 1761 ∨ (1763 ≤ r ∧ r < 1827)
    · obtain ⟨w, hw, hf⟩ := hex r hr
      have hk : epiK r = Kd.s .fl := by simp [epiK, hr]
      rw [hk]
      show SK.fl.Has _
      simp only [hw, Option.getD_some]
      exact hf
    · simp [epiK, hr, Kd.Has]
  have hd : ∀ r ∈ epiDom, t0.regs r = some ((fun r => (t0.regs r).getD (.bits 32 0)) r) := by
    intro r hr
    have : r = 1761 ∨ (1763 ≤ r ∧ r < 1827) := by
      simp only [epiDom, List.mem_cons, List.mem_map, List.mem_range] at hr
      rcases hr with h | ⟨j, hj, rfl⟩
      · exact .inl h
      · exact .inr ⟨by omega, by omega⟩
    obtain ⟨w, hw, -⟩ := hex r this
    simp [hw]
  have hft : t0.fault = none := by
    rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c1, hc1, -⟩
    · omega
    · obtain ⟨-, -, hf, -⟩ := win_cases hc1
      exact hf
  obtain ⟨j, hj, t1, a1, a2, -, a4, -, -, -, -, -, a10⟩ := xRun_path (K := kernel)
    (A := Assumptions.all) (L := L) (g := g) Gen.epk_items0 _ epiDom t0
    (ht09 ▸ (Gen.epk_at0 L g).code) hft hd epi_reads (epi_req _) epi_local
    (ht09 ▸ (Gen.epk_at0 L g).rules) t hrt
  have hj33 : j = 33 := by
    rw [epi_len] at hj a2
    rcases a2 with h | h
    · exact h
    · rw [h] at a4
      omega
  subst hj33
  have hu : inS epTail t1.pc = true := by simp only [inS, epTail]; simp; omega
  obtain ⟨-, hk2⟩ := win_keep tl_fwd a1 hu
  refine epi_decl_core hV (fun j hj => ?_) h1 h2 hc
  have hm : 2346 + j ∈ epR := by simp only [epR, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  rw [hk2 _ hm, a10 _ (List.mem_append_left _ (epi_writes j hj)),
    List.take_of_length_le (by rw [epi_len])]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
