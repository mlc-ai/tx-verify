-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Reach
public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Canon
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsMid
public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartClass
public import Lemmas.Flow.DataElems
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The first window's result after the wait of the scores

At the wait of the score load every register the first window reads has a fact (the control
machine's, the constants', the pairs of scores', the bias words' and their packs'). The values of
those facts are the file `w1V`; after the wait, whatever path the window takes, the register of
the word the thread sends at the shuffle of pc 1838 holds `vFin` of it (`w1F`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The registers that have a fact at the wait of the score load. -/
def kBase : List Nat :=
  ctlLive 1298 ++ [498, 1914] ++ ([482, 484, 483, 199] ++ (keysC ++
    ((List.range 32).map (2447 + ·) ++ (packK ++ (List.range 64).map nxtReg))))

theorem kW1_sub : kW1.all (fun r => kBase.contains r) = true := by decide +kernel

theorem w1_keys {d : D} (hs : d.c.site = .waitLd) :
    (baseF e L g d).map Prod.fst = kBase := by
  have hw : (wF d).map Prod.fst = packK ++ (List.range 64).map nxtReg := by
    have : wF d = packF d.v.cur ++ wordF nxtReg d.v.ld 64 := by
      simp only [wF, hs]
      rfl
    rw [this]
    simp [packF, wordF, packK, List.map_map, Function.comp_def]
  simp only [baseF, Control.facts, List.map_append, factsFrom_keys, dF, dFS_keys, hs, derF,
    pF, ite_true, spF_keys, hw, kBase, startF]
  rfl

theorem shfl5_pred {s : Site} (h : Site.shfl5 ∈ succs s) : s = .waitLd := by
  cases s <;> first | rfl | (simp only [succs] at h; (try split_ifs at h) <;> simp at h)

/-- **The first window's result after the wait of the scores.** -/
theorem w1_waitLd {d : D} (hs : d.c.site = .waitLd) : DataStep (codeS e L g) (w1F e L g) d := by
  have pc : (codeS e L g).pc d = 1298 := by
    change d.c.site.pc = 1298
    rw [hs]
    rfl
  apply DataStep.next (op := .tcWaitLd) (by rw [pc]; exact Flow.code_tmemWait_1)
    (fun t ev u hf => fires_tcWaitLd_next hf)
  intro hi ev d' t hn hat
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  have hF : Holds t.regs (baseF e L g d) := by
    have h : (codeS e L g).facts d = baseF e L g d ++ lF d := by
      simp [constF, baseF, w1F, xF, xF0, hs, inRound]
    rw [h] at hreg
    exact ((holds_append _ _ _).mp hreg).1
  have hd : (⟨{d.c with site := .waitLd}, d.v⟩ : D) = d := by
    rw [← hs]
  have hv : w1F e L g ⟨{d.c with site := .shfl5}, record L d ev .shfl5⟩ =
      factsFrom kXin (vFin (w1V e L g d)) := by
    simp [w1F, w1V, canon, m0, record, hs]
  rw [hv]
  refine w1_reach (L := L) (g := g) _ (PTX.next t) ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PTX.next, hpc]
    rw [hs]
    rfl
  · simp [PTX.next, hsub]
  · simp [PTX.next, hacc]
  · simp [PTX.next, hft]
  · have hk := kW1_sub
    rw [← w1_keys (e := e) (L := L) (g := g) hs] at hk
    have h := holds_lookupD hF hk
    exact holds_of_pointwise fun r hr => by
      rw [w1V_eq hs hr]; exact holds_mem h (mem_factsFrom hr)

/-- The first window's result is established at the shuffle after the wait and only there. -/
theorem w1_step (d : D) : DataStep (codeS e L g) (w1F e L g) d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hs : d.c.site = .waitLd
  · exact @w1_waitLd e L g d hs t ev u d' ins hat hi hc' hf hn
  · obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
    have hz := next_mem (e := e) (L := L) (g := g) (ev := ev) hnc
    have h5 : c'.site ≠ .shfl5 := fun h => hs (shfl5_pred (h ▸ hz))
    refine .inl fun _ _ _ => ?_
    simp [w1F, h5]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
