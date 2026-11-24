-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOut
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Wait
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The consumer's Tensor Memory data events

A consumer's accumulator is read by sixteen loads, each followed by its wait: thirty-two
warp-collective `tcgen05` data events per accumulator. Along a consumer's run, its data events
(`dataOps`) are thirty-two per accumulator released, plus its position in the tile it is loading
(`D.tcPos`): `TcTile`, a conjunct of the consumer's run invariant `ConsInv`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The kernel's Tensor Memory loads, stores and waits are at its load and wait sites (decided on
the code, in one pass). -/
theorem kernel_tcData_pcs :
    OpPcsFast kernel.code tcDataOp (Flow.tmemLoad.toList ++ Flow.tmemWait.toList) = true := by
  decide +kernel

/-- A thread's warp-collective Tensor Memory data events. -/
def dataOps (es : List Event) : Nat := es.countP isTcData

theorem dataOps_snoc (es : List Event) (e : Event) :
    dataOps (es ++ [e]) = dataOps es + if isTcData e then 1 else 0 := by
  simp [dataOps, List.countP_append]

/-- No prologue event is a Tensor Memory data event. -/
theorem Prologue.not_tcData {L : Launch} {g : Nat} {p : Prologue.D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o) : isTcData e = false := by
  cases hd : isTcData e
  · rfl
  · exfalso
    have hpc := OpPcsFast.mem kernel_tcData_pcs hc (fires_tcData_op hf hd)
    obtain ⟨site, w⟩ := p
    simp only at hpc
    clear hc hf hd
    revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The data events and the accumulator releases of a consumer: thirty-two data events per
release, plus the position in the tile being loaded. -/
def TcTile (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  dataOps es = 32 * arrivals (accEmpty L g (accIdx L g)) es + d.tcPos

/-- A data event of a consumer is at a load or a wait. -/
theorem data_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hd : isTcData e = true) :
    (∃ j, d.site = .load j) ∨ ∃ j, d.site = .loadWait j := by
  have hpc := OpPcsFast.mem kernel_tcData_pcs hc (fires_tcData_op hf hd)
  clear hc hf hd
  site_of_pc d hpc

set_option maxHeartbeats 8000000 in
theorem tc_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event}
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : TcTile L g d pre) : TcTile L g d' (pre ++ [e]) := by
  have hR := arrives_acc_site hpre hg hat hc hf
  have hR0 : d.site ≠ .accArrive → arrivesOn (accEmpty L g (accIdx L g)) e = false :=
    fun hs => Bool.eq_false_iff.mpr fun h' => hs (hR h')
  have hD0 : (∀ j, d.site ≠ .load j) → (∀ j, d.site ≠ .loadWait j) → isTcData e = false := by
    intro h1 h2
    cases hd : isTcData e
    · rfl
    · rcases data_site hc hf hd with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact absurd hj (h1 j)
      · exact absurd hj (h2 j)
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  unfold TcTile at hq ⊢
  rw [dataOps_snoc, arrivals_snoc]
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case load j =>
    have ha := hR0 (by simp)
    simp only [next] at hn
    split at hn
    · rename_i vals hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hd : isTcData e = true := by simp [isTcData, hk]
      simp only [hd, ha, ↓reduceIte, Bool.false_eq_true, D.tcPos, Nat.add_zero] at hq ⊢
      omega
    · cases hn
  case loadWait j =>
    have ha := hR0 (by simp)
    have hd : isTcData e = true := by
      obtain rfl := Option.some.inj (hc.symm.trans (code_wait j))
      simp [isTcData, fires_tcWaitLd hblk hf]
    simp only [next] at hn
    simp only [hd, ha, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hq ⊢
    simp only [D.tcPos] at hq
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [D.tcPos] <;> omega
  case accArrive =>
    obtain ⟨rel, sc, rfl⟩ := accArrive_event hpre hg rfl hat.2.2.2.2 hc hf
    have hd : isTcData ⟨(Site.accArrive).pc, .arrive (accEmpty L g (accIdx L g)) 0 1 rel sc⟩ =
        false := by simp [isTcData]
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [hd, arrivesOn_arrive rfl, decide_true, ↓reduceIte, Bool.false_eq_true,
      Nat.add_zero, D.tcPos] at hq ⊢
    omega
  all_goals have hd := hD0 (fun _ h => by cases h) (fun _ h => by cases h)
  all_goals have ha := hR0 (by simp)
  all_goals clear hD0 hR hR0 hat hc hf
  all_goals simp only [hd, ha, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq ⊢
  all_goals simp only [next] at hn
  all_goals revert hq
  clc_sweep hn
  all_goals simp [D.tcPos]

end Consumer

end
end PTX.Kernels.Fp16Gemm8192.Proof
