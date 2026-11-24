-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.TcColl
public import Kernels.Fp16Gemm8192.Proof.Thread.TcSpecs
public import Kernels.Fp16Gemm8192.Proof.Thread.RankCounts

@[expose] public section

/-! # The writes a Tensor Memory load can read

Two facts the accumulator ring's load sources need. A Tensor Memory load is a consumer's load of
sixteen registers (`ld_len_fact`: the site's destination table). An accumulator commit follows an
MMA of its thread (`acc_commit_mma_fact`): at the accumulator commit the thread has made 128
commits to the input empty barriers (`mma_counts`, a projection of `Mma.Counts`), each right after
the four MMAs of its slot (`mma_batch_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- **A Tensor Memory load returns sixteen words.** -/
theorem ld_len_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc a : Nat} {vals : List Value}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) : vals.length = 16 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ⟩ := state_at hpre hX hg he (by intro _ _ h; cases h)
  have hd : isTcData ⟨pc, .tc (.ld a vals .s32x32b)⟩ = true := rfl
  obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ hd
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj] at hc hfire
    obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_load j))
    rw [fires_tcLd_len (fun _ h => by cases h) hfire rfl]
    exact Consumer.ldRegs_len j
  · rw [hj] at hc hfire
    obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
    have := fires_tcWaitLd hb hfire
    simp at this

/-- **Every Tensor Memory load is a `.32x32b` load**: the consumer's load instruction has the
default shape. -/
theorem ld_shape_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) : sh = .s32x32b := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ⟩ := state_at hpre hX hg he (by intro _ _ h; cases h)
  have hd : isTcData ⟨pc, .tc (.ld a vals sh)⟩ = true := rfl
  obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ hd
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj] at hc hfire
    obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_load j))
    obtain ⟨_, _, he'⟩ := fires_tcLd_data hfire hd
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he'
    exact he'.2.2.2
  · rw [hj] at hc hfire
    obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
    have := fires_tcWaitLd hb hfire
    simp at this

/-- **An accumulator commit follows an MMA of its thread.** -/
theorem acc_commit_mma_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} {d : ThreadD} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tc (.commit sp))
    (hm : sp.mbar = Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩) :
    ∃ k' pc dst sp' acc mask, k' < k ∧
      X.get (g, k') = some ⟨pc, .tc (.mma dst sp' acc mask)⟩ := by
  obtain ⟨m, rfl, -, hsite⟩ := commit_spec_fact hpre hX hg he hσ hk
  have hmacc : m.site = .accCommit := by
    rcases hsite with ⟨s, -, rfl⟩ | ⟨hs, -⟩
    · simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and] at hm
      omega
    · exact hs
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨hrank, hcond⟩ := mma_counts hpre hg htr (k := k) hσ
  rw [hmacc] at hcond
  have h0 := hrank 0
  have hpos : 0 < ((X.tr g).take k).countP
    (commitsTo (inputEmpty L (g / L.block) ((0 : Fin 4) : Nat))) := by
    rw [h0]; omega
  obtain ⟨ec, hmem, hec⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hmem
  rw [List.length_take] at hi
  have hik : i < k := by omega
  have hgi' : X.get (g, i) = some ec := by
    show (X.tr g)[i]? = some ec
    rw [← hgi, List.getElem?_eq_getElem (by omega), List.getElem_take]
  obtain ⟨di, hσi⟩ := state_at hpre hX hg hgi' (by
    intro pc f h; subst h; simp [commitsTo] at hec)
  obtain ⟨spc, hkc⟩ : ∃ spc, ec.kind = .tc (.commit spc) := by
    obtain ⟨pc, kd⟩ := ec
    unfold commitsTo at hec
    split at hec
    · exact ⟨_, by assumption⟩
    · cases hec
  have hmc : spc.mbar = emptyAt L g 0 := by
    rw [commitsTo_of_kind hkc] at hec
    have := of_decide_eq_true hec
    rw [this, ← inputEmpty_emptyAt]
  obtain ⟨mi, rfl, -⟩ := commit_spec_fact hpre hX hg hgi' hσi hkc
  obtain ⟨h4, hb⟩ := mma_batch_fact hpre hX hg hgi' hσi hkc hmc
  obtain ⟨pc, dst, acc, mask, hget, -⟩ := hb 0
  exact ⟨i - 4 + 0, pc, dst, _, acc, mask, by omega, hget⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
