-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Softmax

noncomputable section

private def valueIdSetup (block : Fin 4) : Nat := pvPc block 0 - 7

private def valueIdActive (block : Fin 4) (pc : Nat) : Prop :=
  valueIdSetup block < pc ∧ pc ≤ pvPc block 7

private instance (block : Fin 4) (pc : Nat) : Decidable (valueIdActive block pc) :=
  inferInstanceAs (Decidable (valueIdSetup block < pc ∧ pc ≤ pvPc block 7))

private def valueIdCode (block : Fin 4) (pc : Nat) (ins : Instr) : Bool :=
  (!decide (valueIdActive block pc) || !(mmaWrites ins.op).contains (pvSite block).id) &&
  match ins.op with
  | .bra dst _ => !decide (valueIdActive block dst) || decide (valueIdActive block pc)
  | .brx .. => false
  | _ => true

private theorem valueIdCodeAt (block : Fin 4) {pc : Nat} {i : Instr}
    (hPc : 1907 ≤ pc ∧ pc < 2768) (hc : kernel.code[pc]? = some i) :
    valueIdCode block pc i = true := by
  let slice := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hAll : slice.all (fun (ins,pos) => valueIdCode block pos ins) = true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  refine List.all_eq_true.mp hAll (i,pc) (List.mem_of_getElem? (i := pc-1907) ?_)
  dsimp only [slice]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hPc.1,hc]
  rfl

private theorem valueIdDecoded (block : Fin 4) :
    kernel.code[valueIdSetup block]? =
      some ⟨none,.move ⟨.scalar,.int .b 32,[some (pvSite block).id],[.imm 136381584]⟩⟩ := by
  fin_cases block
  · exact Flow.code_2312
  · exact Flow.code_2427
  · exact Flow.code_2563
  · exact Flow.code_2603

private theorem valueIdDefined (block : Fin 4) {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc = valueIdSetup block) (hf : s.fault = none) (h : Tau kernel [] l g s u) :
    u.regs (pvSite block).id = some (b32 0x8210490) := by
  let r := (pvSite block).id
  let v := next (setReg s r (b32 0x8210490))
  have hExec : execLocalA [] l g s (.move ⟨.scalar,.int .b 32,[some r],[.imm 136381584]⟩) =
      .ok v := by
    rw [execLocalA_nil,execLocal_move rfl]
    simp [execMove,readValue,readBits,DType.width,
      Value.bytes,b32,bind,Except.bind,pure,Except.pure,v]
    rfl
  have hOut : out kernel [] l g s = .tau v := by
    simp only [out,hPc,hf,valueIdDecoded block,guardHolds,pure,Except.pure]
    exact congrArg (fun x : Exec TState => match x with
      | .ok s => Out.tau s | .error f => Out.ev (.ub f)) hExec
  obtain rfl := Out.tau.inj (h.symm.trans hOut)
  exact Function.update_self _ _ _

private theorem valueIdStep (block : Fin 4) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hFrame : valueIdActive block s.pc → s.regs (pvSite block).id = some (b32 0x8210490))
    (hw : WStep kernel Assumptions.all l g s e u) :
    valueIdActive block u.pc → u.regs (pvSite block).id = some (b32 0x8210490) := by
  intro hLive
  have keep (hPrior : valueIdActive block s.pc) : u.regs (pvSite block).id =
      some (b32 0x8210490) := by
    refine (mmaStepReg (by omega) hPc.2 (fun ins hc => ?_) hw).trans (hFrame hPrior)
    have hCode := (Bool.and_eq_true_iff.mp (valueIdCodeAt block hPc hc)).1
    simpa [hPrior] using hCode
  have fall (hNext : u.pc = s.pc+1) :
      s.pc = valueIdSetup block ∨ valueIdActive block s.pc := by
    unfold valueIdActive at hLive ⊢
    omega
  rcases hw with ⟨_, ht⟩ | ⟨ev,_,he⟩
  · have htCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hPc.2]
    obtain ⟨i,hc,hf,_⟩ := tauScoreSource ht
    by_cases hDef : s.pc = valueIdSetup block
    · exact valueIdDefined block hDef hf htCore
    apply keep
    rcases tau_core_frame hc htCore with rfl | hLocal
    · exact (fall rfl).resolve_left hDef
    have hNext := hLocal.pc
    have hCode := (Bool.and_eq_true_iff.mp (valueIdCodeAt block hPc hc)).2
    cases ho : i.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hNext
    case bra target uniform =>
      rw [hNext] at hLive
      simpa [ho,hLive] using hCode
    case brx => simp [ho] at hCode
    all_goals exact (fall hNext).resolve_left hDef
  · apply keep
    have hNot : s.pc ≠ valueIdSetup block := by
      intro hEq
      obtain ⟨i,hc,hl,_⟩ := estep_event_source he
      rw [hEq,valueIdDecoded block] at hc
      obtain rfl := Option.some.inj hc
      cases hl
    have heCore : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm,hOut,hFires⟩ := he
      exact ⟨tm,by rwa [← out_eq_core (by omega) hPc.2],hFires⟩
    rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hLive
    · exact (fall h).resolve_left hNot

private theorem valueIdWalk (block : Fin 4) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hFrame : valueIdActive block s.pc → s.regs (pvSite block).id = some (b32 0x8210490))
    (he : e ∈ es) (hLive : valueIdActive block e.pc) (hRange : e.pc < 2768) :
    ∃ t o, t.regs (pvSite block).id = some (b32 0x8210490) ∧
      EStep kernel Assumptions.all l g t e o := by
  induction hw with
  | stop => simp at he
  | tau ht hWalk ih =>
    let step : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl,ht⟩
    obtain ⟨hNext | hExit,hShape'⟩ := mmaCutStep hs.1 hs.2 step hShape
    · exact ih hNext hShape' (valueIdStep block hs hFrame step) he
    · have h := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
        hShape'.2 hWalk _ he
      omega
  | ev hv hWalk ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_,_,hFrame ((estep_source_pc hv) ▸ hLive),hv⟩
    let step : WStep kernel Assumptions.all l g _ (some _) _ := .inr ⟨_,rfl,hv⟩
    obtain ⟨hNext | hExit,hShape'⟩ := mmaCutStep hs.1 hs.2 step hShape
    · exact ih hNext hShape' (valueIdStep block hs hFrame step) he
    · have h := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
        hShape'.2 hWalk _ he
      omega
  | last hv =>
    obtain rfl := List.mem_singleton.mp he
    exact ⟨_,_,hFrame ((estep_source_pc hv) ▸ hLive),hv⟩

/-- Every recorded PV fragment retains the literal instruction descriptor from its own setup. -/
theorem valueInstructionFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (block : Fin 4) (frag : Fin 8)
    {id : EvId} {kind : Kind} (he : X.get id = some ⟨pvPc block frag,kind⟩) :
    ∃ t o, t.regs (pvSite block).id = some (b32 0x8210490) ∧
      EStep kernel Assumptions.all l id.1 t ⟨pvPc block frag,kind⟩ o := by
  obtain ⟨g,index⟩ := id
  have hLow : 2145 ≤ pvPc block frag := by fin_cases block <;> fin_cases frag <;> decide
  have hHigh : pvPc block frag < 2768 := by fin_cases block <;> fin_cases frag <;> decide
  obtain ⟨base,s,visits,hBase,hs,hWalk⟩ := initialMmaTrace hp hX he hLow hHigh
  have hGet : ((X.tr g).drop (base+1))[index-(base+1)]? =
      some ⟨pvPc block frag,kind⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  exact valueIdWalk block hWalk (by rw [hs.1]; decide)
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
    (by
      rw [hs.1]
      intro h
      exact False.elim ((show ¬ valueIdActive block 1908 by fin_cases block <;> decide) h))
    (List.mem_of_getElem? hGet)
    (show valueIdActive block (pvPc block frag) by fin_cases block <;> fin_cases frag <;> decide)
    hHigh

end
end PTX.Kernels.TmlFa4Fwd.Mma
