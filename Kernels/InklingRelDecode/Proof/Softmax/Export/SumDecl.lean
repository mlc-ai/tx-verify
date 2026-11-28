-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Lemmas.Flow.OutPre
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFront
import Kernels.InklingRelDecode.Proof.Softmax.Data.E2Kinds
import Kernels.InklingRelDecode.Proof.Softmax.Data.PackWin
import Kernels.InklingRelDecode.Proof.Softmax.Export.SumWord
import Kernels.InklingRelDecode.Flow.Code.Part034

/-! # The sums of the exponentials and the row sum are not declined

Pcs 2201 to 2233 add pairs of exponentials and their halves: the state is the one after a prefix
of the run of the exponentials (pcs 2089 to 2233), whose registers have the kinds the run
accepts. Pc 2235 adds the lane's row sum to the one it received at pc 2234: both are numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Assumption Data

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

/-- **The unrounded sums of pcs 2201 to 2233 are not declined.** -/
public theorem sum_decl {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hl : Iface.LaneState L X g t) (h1 : 2201 ≤ t.pc) (h2 : t.pc ≤ 2233) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) (hd : Iface.declineOp i.op = true) :
    execIdealFloat L g t i.op ≠ none := by
  obtain ⟨m, sent, recv, vH, V, t0, -, -, -, hE, hV, hAt, ht⟩ :=
    exp_front hp hX hf hS h5 hl (by omega) (by omega)
  obtain ⟨N, hpath⟩ := exp_path (L := L) (g := g) m sent recv vH hE hV (n := 16) le_rfl
  obtain ⟨-, t1, -, a1, q1⟩ := hpath t0 hAt t ht (by simp only [swPc]; omega)
  obtain ⟨h0, -, -, hft, hF⟩ := a1
  have e0 : t1.pc = 2089 := by rw [h0]; simp [swPc]
  obtain ⟨-, -, k3, -, -, -⟩ := kE_ok
  have hs : ∀ r ∈ runE2.live, t1.regs r = some (vE2 V r) := fun r hr =>
    holds_mem hF (mem_factsFrom (List.contains_iff_mem.mp (List.all_eq_true.mp k3 r hr)))
  have hW : ∀ r, (kE20 r).Has (vE2 V r) := fun r => by
    by_cases h1 : r ∈ xRegs
    · simpa [kE20, h1] using vE2_x hE h1
    · by_cases h2 : r ∈ swOuts
      · simpa [kE20, h1, h2] using vE2_y hE h2
      · simp [kE20, h1, h2, Kd.Has]
  obtain ⟨j, hj, hjpc, hregs⟩ := xItems_pre (V := vE2 V) (dom := runE2.live)
    (by rw [e0]; exact ex2_at L g) hft hs ex2_reads (ex2_req _) ex2_local q1
    (fun t1' t' e1 hr => by
      have e2 : t1'.pc = 2234 := by rw [e1, e0, ex2_len]
      have := (Lib.rtg_fwd (L := L) (g := g) (lo := 1839) (hi := 2234)
        (Lib.entryOk_fwd exp_entry_ok) hr (by omega) (by omega)).1
      omega) (by omega) (by rw [e0, ex2_len]; omega)
  exact e2_decl_core hW (by rwa [ex2_len] at hj) (by omega) hregs hc hd

private theorem no_into_2235 : Lib.scanCode (fun pc ins =>
    (!ins.guard.isSome || pc + 1 != 2235) &&
      (!ins.op.isLocal || !(Lib.succs pc ins.op).contains 2235)) kernel.code 0 = true := by
  decide +kernel

private theorem win_fwd0 : Lib.fwdOk packWin [] = true := by decide +kernel

private theorem tau_not_2235 {u v : TState} (h : Tau kernel Assumptions.all L g u v)
    (hv : v.pc = 2235) : False := by
  obtain ⟨ins, hc, -, hk⟩ := Lib.win_cases h
  have := Lib.scanCode_get no_into_2235 hc
  rw [Nat.zero_add] at this
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  rcases hk with ⟨hs, hp, -⟩ | ⟨hl, hp, -⟩
  · have hs' : ins.guard ≠ none := by simpa [Option.isSome_iff_ne_none] using hs
    exact this.1.resolve_left (by simpa using hs') (by omega)
  · rcases this.2 with h2 | h2
    · rw [hl] at h2
      cases h2
    · exact absurd (List.contains_iff_mem.mpr (hv ▸ hp)) (by rw [h2]; simp)

/-- **The row sum added to the received one at pc 2235 is not declined**, when the sums the
shuffle of pc 2234 sends and brings in are numbers. -/
public theorem sum_add_decl {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hR : ∀ k mode sent b c recv ok, X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩ →
      SK.fl.Has recv)
    (hl : Iface.LaneState L X g t) (hpc : t.pc = 2235) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) : execIdealFloat L g t i.op ≠ none := by
  have hin : Lib.inS packWin t.pc = true := by simp only [Lib.inS, packWin, hpc]; simp
  obtain ⟨k, e, t0, hk, -, ⟨s, hes⟩, -, -, hrt, -⟩ :=
    Lib.lane_set win_fwd0 packWin_enter packWin_zero hl hin
  have t0t : t0 = t := by
    rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨u, -, hu⟩
    · exact h.symm
    · exact (tau_not_2235 hu hpc).elim
  obtain ⟨ins, hcs, hnl, hfi⟩ := EventFrame.estep_event_source hes
  have hpost := Lib.post_pc hes
  have h0 : t0.pc = 2235 := by rw [t0t]; exact hpc
  have hs2234 : s.pc = 2234 := by
    have : s.pc = 2234 ∨ s.pc = 2235 := by omega
    rcases this with h | h
    · exact h
    · rw [h, Flow.code_2235] at hcs
      obtain rfl := (Option.some.inj hcs).symm
      simp [Op.isLocal] at hnl
  rw [hs2234, Flow.code_shfl_6] at hcs
  obtain rfl := Option.some.inj hcs
  rw [hs2234] at hfi
  obtain ⟨v, bv, cv, recv, ok, hv, he, ht0⟩ := fires_shfl_src (p := none) hfi
  subst he
  have r1529 : t.regs 1529 = some v := by
    rw [← t0t, ht0]
    simpa [PTX.next, setReg] using hv
  have r1530 : t.regs 1530 = some recv := by
    rw [← t0t, ht0]
    simp [PTX.next, setReg]
  have get : X.get (g, k) = some ⟨2234, .shfl .bfly v bv cv recv ok⟩ := hk
  obtain ⟨-, -, -, hsum⟩ := sent_sum hp hX hf hS h5 get
  have hr := hR k _ _ _ _ _ _ get
  rw [hpc, Flow.code_2235] at hc
  obtain rfl := (Option.some.inj hc).symm
  obtain ⟨x, hx, ⟨a, rfl⟩⟩ := Data.rd_sk (k := .fl) (r := 1529) rfl r1529 hsum
  obtain ⟨y, hy, ⟨b, rfl⟩⟩ := Data.rd_sk (k := .fl) (r := 1530) rfl r1530 hr
  exact Data.ideal_add1 (by simp [Data.arith2]) hx hy (by rw [addEReal_coe]; simp)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
