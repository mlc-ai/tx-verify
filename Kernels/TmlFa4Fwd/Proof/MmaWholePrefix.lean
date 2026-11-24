-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CountedVisits
public import Kernels.TmlFa4Fwd.Proof.ExitPrefix
public import Kernels.TmlFa4Fwd.Proof.MmaRoleBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem roleRegionsCover {pc : Nat} (hLo : 1907 ≤ pc) (hHi : pc < 2768) :
    ∃ i : Fin 12, (roleRegion i).lo ≤ pc ∧ pc < (roleRegion i).hi := by
  have hAll : (List.range 861).all (fun d =>
      (List.finRange 12).any (fun i =>
        decide ((roleRegion i).lo ≤ 1907 + d ∧ 1907 + d < (roleRegion i).hi))) = true := by
    decide +kernel
  have hD : pc - 1907 ∈ List.range 861 := List.mem_range.mpr (by omega)
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hAll (pc - 1907) hD)
  exact ⟨i, by simpa [Nat.add_sub_of_le hLo] using hi⟩

private theorem regionDestinations (i : Fin 12) :
    1907 ≤ (roleRegion i).lo ∧ (roleRegion i).hi ≤ 2768 ∧
      (roleRegion i).exits.all (fun p => decide ((1907 ≤ p ∧ p ≤ 2768) ∨ p = 3099)) = true := by
  fin_cases i <;> decide

private theorem noNextRoleBranch {pc : Nat} {ins : Instr} (hLo : 1907 ≤ pc)
    (hHi : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    (match ins.op with | .bra d _ => d ≠ 2768 | .brx .. => False | _ => True) := by
  have hAll : ((kernel.code.drop 1907).take 861).all (fun i =>
      match i.op with | .bra d _ => d != 2768 | .brx .. => false | _ => true) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hs : ((kernel.code.drop 1907).take 861)[pc - 1907]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  have hCode := List.all_eq_true.mp hAll ins (List.mem_of_getElem? hs)
  cases ho : ins.op <;> simp_all

private theorem notNextRolePc {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hs : RoleShape s) (he : WStep kernel Assumptions.all l g s e u) :
    u.pc ≠ 2768 := by
  intro hu
  by_cases hLast : s.pc = 2767
  · have hCode := Flow.code_2767
    rw [← hLast] at hCode
    rcases he with ⟨-, ht⟩ | ⟨v, -, hFire⟩
    · have ht' : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← out_eq_core (by omega) hHi]
      have hf : s.fault = none := by
        cases h : s.fault
        · rfl
        · simp [Tau, out, h] at ht'
      have hOut : out kernel [] l g s = .tau {s with pc := 3099} := by
        unfold out
        rw [hf, hCode]
        simp [guardHolds, execLocalA, execLocalRule, execLocal, Op.isLocal, Op.rule, execBranch,
          pure, Except.pure, hf]
      have hu' := Out.tau.inj (ht'.symm.trans hOut)
      rw [hu'] at hu
      cases hu
    · obtain ⟨i, hc, hLoc, _⟩ := estep_event_source hFire
      rw [hCode] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hLoc
  · rcases he with ⟨-, ht⟩ | ⟨v, -, hFire⟩
    · have ht' : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← out_eq_core (by omega) hHi]
      obtain ⟨i, hc⟩ := tau_core_has_code ht'
      rcases tau_core_frame hc ht' with rfl | hFrame
      · change s.pc + 1 = 2768 at hu
        omega
      · have hDest := noNextRoleBranch hLo hHi hc
        have hPc := hFrame.pc
        cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra dst aligned =>
          simp only [ho] at hDest
          exact hDest (hPc.symm.trans hu)
        case brx =>
          rw [ho] at hDest
          contradiction
        all_goals omega
    · obtain ⟨i, hc, hLoc, _⟩ := estep_event_source hFire
      have hAll : ((kernel.code.drop 1907).take 861).all
          (fun i => i.op.isLocal || linearEventOp i.op) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      have hSlice : ((kernel.code.drop 1907).take 861)[s.pc - 1907]? = some i := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
      have hEv : linearEventOp i.op = true := by
        simpa only [hLoc, Bool.false_or] using
          List.all_eq_true.mp hAll i (List.mem_of_getElem? hSlice)
      obtain ⟨_, _, hPc | hSub | hFault⟩ := linearEventProgress hc hEv hs.1 hs.2.1 hFire
      · omega
      · omega
      · omega

private theorem mmaWarpFrame {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (h : WStep kernel Assumptions.all l g s ev u) :
    u.regs 1062 = s.regs 1062 := by
  apply mmaStepReg (by omega) hHi _ h
  intro ins hc
  have hAll : ((kernel.code.drop 1907).take 861).all
      (fun i => !((mmaWrites i.op).contains 1062)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSlice : ((kernel.code.drop 1907).take 861)[s.pc - 1907]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  simpa using List.all_eq_true.mp hAll ins (List.mem_of_getElem? hSlice)

/-- The MMA body stays in its role, or reaches the common return with its warp rank. -/
theorem mmaCutStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (he : WStep kernel Assumptions.all l g s e u)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) :
    (1907 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc ∈ [3099] ∧ u.fault = none) ∧
      (RoleShape u ∧ u.regs 1062 = some (b32 12)) := by
  obtain ⟨i, hL, hU⟩ := roleRegionsCover hLo hHi
  obtain ⟨hState, hShape⟩ := roleRegionStep i hL hU hs.1 he
  have hFrame := (mmaWarpFrame hLo hHi he).trans hs.2
  refine ⟨?_, hShape, hFrame⟩
  obtain ⟨hEntry, hStop, hExits⟩ := regionDestinations i
  rcases hState with ⟨hA, hB⟩ | ⟨hExit, hFault⟩
  · exact .inl ⟨hEntry.trans hA, hB.trans_le hStop⟩
  · have hDst := List.all_eq_true.mp hExits u.pc hExit
    have hNot := notNextRolePc hLo hHi hs.1 he
    simp only [decide_eq_true_eq] at hDst
    rcases hDst with ⟨h1, h2⟩ | h
    · exact .inl ⟨h1, by omega⟩
    · exact .inr ⟨by simp [h], hFault⟩

set_option maxRecDepth 3000 in
/-- The MMA role's entire counted trace includes its transfer to the common return. -/
theorem mmaWholePrefixFromDispatch {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s 174 (startupFacts p l)) :
    es.countP Event.counts ≤ 256 * 2 ^ 32 + 128 * (p.batch + 1) + 1366 := by
  obtain ⟨u, hr, hu⟩ := dispatchWarp12 hp hg hs
  have hGrid : g / l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCta := (Nat.succ_le_of_lt hGrid).trans_lt hp.grid.2.2
  rcases advanceWalkLocals hr hw with he | ⟨tail, _, hCount, hWalk⟩
  · subst es
    simp
  have hs' : RoleShape u :=
    ⟨by rw [hu.2.1]; decide, hu.2.2.1, fun _ => hu.2.1⟩
  have hWarp : u.regs 1062 = some (b32 12) := hu.2.2.2.2.2.2.2.1
  have hB := mmaRolePrefixBound hp hCta hWalk
    (hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2.1, trivial⟩)
  have hCut := cutWalkInterval (cutoff := 9206) (hi := 2768) (exits := [3099]) hWalk
    hu.1.ge (by rw [hu.1]; decide) ⟨hs', hWarp⟩ (by decide) mmaCutStep
  have hAll := countedThroughCode hw
  rw [Decoded.code_length] at hAll
  have hCount' := hCount 9206
  rcases hCut with h | ⟨v, rest, next, he, hf, hShape, hv, hb⟩
  · omega
  · have hPc : v.pc = 3099 := by simpa using he
    have hExit := Epilogue.sharedExitPrefixBound hv hPc hf (.inl rfl) hShape.2
    omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
