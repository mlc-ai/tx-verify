-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpPath
import Kernels.InklingRelDecode.Proof.Softmax.Data.SwExp
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.WindowEntry
import Lemmas.Kernel.PostEvent
import Lemmas.Execution.TraceProjection
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFront

/-! # The inputs of the software `exp2` instances are numbers or `-inf`

A state of the lane that the local steps reach from the state after the shuffle of pc 1838, at
the start of instance `i` of the software `exp2`, has the shifted score of the instance in the
register it reads, a number or `-inf` when the window's inputs are typed (`exp_path`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private theorem exp2_core {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hl : Iface.LaneState L X g t) {i : Nat} (hi : i < 16) (hpc : t.pc = swPc i) :
    ∃ x : EReal, readERealOpnd t .f32 (.reg (swX (swPc i))) = some (.ok x) ∧ x ≠ ⊤ := by
  have hp1 : 1839 ≤ t.pc := by simp only [hpc, swPc]; omega
  have hp2 : t.pc < 2234 := by simp only [hpc, swPc]; omega
  obtain ⟨m, sent, recv, vH, V, t0, -, -, -, hE, hV, hAt, ht⟩ := exp_front hp hX hf hS h5 hl hp1 hp2
  obtain ⟨N, hpath⟩ := exp_path (L := L) (g := g) m sent recv vH hE hV
    (n := i) hi.le
  obtain ⟨-, t1, -, a1, q1⟩ := hpath t0 hAt t ht (by rw [hpc])
  obtain ⟨a11, -, -, -, a15⟩ := a1
  have e1 : t.pc = t1.pc := by rw [hpc, a11]
  obtain rfl := Lib.rtg_fwd_unique (L := L) (g := g) (lo := 1839) (hi := 2234)
    (Lib.entryOk_fwd exp_entry_ok) q1
    (by omega) (by omega) e1
  obtain ⟨-, k1, -, k3, -, -⟩ := kE_ok
  have hx : swX (swPc i) ∈ kE1 := by simpa using List.all_eq_true.mp k1 i (by simpa using hi)
  have hxr : swX (swPc i) ∈ xRegs := by
    simpa [xRegs] using List.all_eq_true.mp k3 i (by simpa using hi)
  have hmem := swKs_mem (K := kE1) (fun j hj => swDis_xw hi hj) hx
  have hval := holds_mem a15 (mem_factsFrom (val := swVs (vE1 V) i) hmem)
  rw [swVs_other fun j hj => swDis_xy hi hj] at hval
  obtain ⟨xv, hxv, hxt⟩ := ni_read (vE1_has hE hxr)
  exact ⟨xv, by simp only [readERealOpnd, readReg, hval, pure, Except.pure, hxv], hxt⟩


/-- **The input of a software `exp2` instance** at a state the lane reaches. -/
public theorem exp2_state {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hl : Iface.LaneState L X g t) (hs : Assumptions.emuSites.contains t.pc = true)
    (asg : List (Assumptions.EmuSlot × Nat))
    (hasg : Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) [] = some asg) :
    ∃ x : EReal, readERealOpnd t .f32 (.reg (Assumptions.emuReg asg .x)) = some (.ok x) ∧
      x ≠ ⊤ := by
  obtain ⟨i, hi, hpc⟩ : ∃ i, i < 16 ∧ t.pc = swPc i := by
    simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at hs
    obtain ⟨i, hi, e⟩ := hs
    exact ⟨i, hi, by simp only [swPc]; omega⟩
  have e : asg = Lib.emuAsg t.pc := by simp [Lib.emuAsg, hasg]
  have := exp2_core hp hX hf hS h5 hl hi hpc
  subst e
  rw [hpc] at *
  exact this

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
