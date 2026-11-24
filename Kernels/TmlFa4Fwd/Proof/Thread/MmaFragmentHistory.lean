-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRoleReplay
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvCarry
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Flow.Tc
import Lemmas.Flow.TcMmaTs
import Lemmas.Execution.TraceProjection
import Lemmas.Execution.EventFrameBase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue Softmax

private def fragmentPc (isPv : Bool) (block : Fin 4) (frag : Fin 8) : Nat :=
  if isPv then pvPc block frag else qkPc block+frag.val

private def fragmentGuard (isPv : Bool) (block : Fin 4) : Nat :=
  if isPv then (pvSite block).guard else qkGuard block

private theorem fragmentCode (isPv : Bool) (block : Fin 4) (frag : Fin 8) :
    ∃ instr, kernel.code[fragmentPc isPv block frag]? =
      some ⟨some (fragmentGuard isPv block,false),.tcMma instr⟩ := by
  cases isPv
  · exact ⟨_,qkCode block frag⟩
  · exact ⟨_,pvCode block frag⟩

private theorem fragmentBounds (isPv : Bool) (block : Fin 4) (frag : Fin 8) :
    2145 ≤ fragmentPc isPv block frag ∧ fragmentPc isPv block frag < 2768 := by
  cases isPv <;> fin_cases block <;> fin_cases frag <;> decide

private theorem fragmentIncreasing (isPv : Bool) (block : Fin 4) (frag : Fin 7) :
    fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩ <
      fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩ := by
  cases isPv <;> fin_cases block <;> fin_cases frag <;> decide

private def fragmentWindow (a b pc : Nat) : Prop := a < pc ∧ pc ≤ b

private instance (a b pc : Nat) : Decidable (fragmentWindow a b pc) :=
  inferInstanceAs (Decidable (a < pc ∧ pc ≤ b))

private def windowIngressCode (lo hi site : Nat) : Op → Bool
  | .bra target _ => !decide (fragmentWindow lo hi target) || decide (fragmentWindow lo hi site)
  | .brx .. => false
  | _ => true

private def fragmentPathCode (guard lo hi site : Nat) (ins : Instr) : Bool :=
  (!decide (lo ≤ site ∧ site ≤ hi) || !(mmaWrites ins.op).contains guard) &&
    windowIngressCode lo hi site ins.op

private theorem fragmentPathAt (isPv : Bool) (block : Fin 4) (frag : Fin 7)
    {pc : Nat} {ins : Instr} (hLo : 1907 ≤ pc) (hHi : pc < 2768)
    (hc : kernel.code[pc]? = some ins) :
    fragmentPathCode (fragmentGuard isPv block)
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩)
      (fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩) pc ins = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have h : code.all (fun (ins,pc) => fragmentPathCode (fragmentGuard isPv block)
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩)
      (fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩) pc ins) = true := by
    cases isPv <;> fin_cases block <;> fin_cases frag <;>
      set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,pc)
  apply List.mem_of_getElem? (i := pc-1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem holdsMmaGuard (s : TState) {r : Nat}
    (h : guardHolds s (some (r,false)) = .ok true) : s.regs r = some (.pred true) := by
  cases hr : s.regs r with
  | none => simp [guardHolds,readReg,hr,bind,Except.bind] at h
  | some v =>
    cases v <;> simp [guardHolds,readReg,hr,bind,Except.bind,pure,Except.pure,throw] at h ⊢
    assumption

section
variable {l : Launch}

private theorem mmaGuardTrue {g : Nat} {s : TState} {e : Event} {u : Option TState} {guard : Nat}
    {instr : TcMmaInstr} (hc : kernel.code[s.pc]? = some ⟨some (guard,false),.tcMma instr⟩)
    {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hk : e.kind = .tc (.mma d op acc mask)) (he : EStep kernel Assumptions.all l g s e u) :
    s.regs guard = some (.pred true) := by
  obtain ⟨tmpl,hOut,hFire⟩ := he
  have hOk : guardHolds s (some (guard,false)) = .ok true := by
    have hNoFault (f : Fault) (hf : tmpl = .ub f) : False := by
      subst tmpl
      exact Kind.noConfusion (hk.symm.trans (congrArg Event.kind hFire.1))
    cases hFault : s.fault with
    | some f => exact (hNoFault f (by simpa only [out,hFault,Out.ev.injEq] using hOut.symm)).elim
    | none =>
      cases hGuard : guardHolds s (some (guard,false)) with
      | error f =>
        exact (hNoFault f (by simpa only [out,hFault,hc,hGuard,Out.ev.injEq] using hOut.symm)).elim
      | ok yes =>
        cases yes
        · simp [out,hFault,hc,hGuard] at hOut
        · rfl
  exact holdsMmaGuard s hOk

private theorem returningMma {A : List Assumption} {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {instr : TcMmaInstr}
    (hFires : Fires s.pc (eventTmpl A l g s (.tcMma instr)) e (some u)) :
    ∃ d op acc mask, e.kind = .tc (.mma d op acc mask) := by
  have hTemplate (f : Exec Tmpl) (hAll : AllOk
      (fun tm => ∃ d op acc mask t, tm = Tmpl.tc (.mma d op acc mask) t) f)
      (hf : Fires s.pc (ofExec f) e (some u)) :
      ∃ d op acc mask, e.kind = .tc (.mma d op acc mask) := by
    cases f with
    | error f => cases hf.2
    | ok tm =>
      obtain ⟨d,op,acc,mask,_,rfl⟩ := hAll
      exact ⟨d,op,acc,mask,congrArg Event.kind hf.1⟩
  simp only [eventTmpl,tcTmpl,mmaTmpl] at hFires
  split at hFires
  case h_3 => cases hFires.2
  all_goals
    simp only [mmaSmemTmpl,mmaTmemTmpl] at hFires
    apply hTemplate _ _ hFires
    repeat' first | (apply allOk_bind; intro) | (apply allOk_ite) | split
    all_goals first | trivial | exact ⟨_,_,_,_,_,rfl⟩

private theorem returningStepFaultNone {g : Nat} {s u : TState} {ev : Option Event}
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    s.fault = none := by
  rcases hStep with ⟨_,ht⟩ | ⟨_,_,he⟩
  · obtain ⟨_,_,hFault,_⟩ := tauScoreSource ht
    exact hFault
  cases hf : s.fault with
  | none => rfl
  | some f =>
    obtain ⟨tm,hOut,hFire⟩ := he
    simp only [out,hf,Out.ev.injEq] at hOut
    subst tm
    cases hFire.2

private theorem windowEntryStep {g lo hi : Nat} {s u : TState} {ev : Option Event}
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hIngress : ∀ ins, kernel.code[s.pc]? = some ins → windowIngressCode lo hi s.pc ins.op = true)
    (hStep : WStep kernel Assumptions.all l g s ev u) (hNew : fragmentWindow lo hi u.pc) :
    fragmentWindow lo hi s.pc ∨ s.pc = lo := by
  have hFall (h : u.pc = s.pc+1) : fragmentWindow lo hi s.pc ∨ s.pc = lo := by
    have := hNew.1
    have := hNew.2
    by_cases hHead : s.pc = lo
    · exact .inr hHead
    · exact .inl ⟨by omega,by omega⟩
  rcases hStep with ⟨_,ht⟩ | ⟨e,_,he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core (by omega) hPc.2]
    obtain ⟨ins,hc⟩ := tau_core_has_code ht'
    rcases tau_core_frame hc ht' with rfl | h
    · exact hFall rfl
    have hp := h.pc
    have hChecked := hIngress ins hc
    cases ho : ins.op <;> simp only [ho,nextPc,BrxTarget,or_false] at hp
    case bra target aligned =>
      exact .inl (by simpa [windowIngressCode,ho,hp ▸ hNew] using hChecked)
    case brx => simp [windowIngressCode,ho] at hChecked
    all_goals exact hFall hp
  · have he' : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,by rwa [← out_eq_core (by omega) hPc.2],hFire⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hSame | hNext
    · exact .inl (hSame ▸ hNew)
    · exact hFall hNext

private theorem guardedMmaFires {g lo guard : Nat} {s u : TState} {ev : Option Event}
    (hAt : s.pc = lo) (hCode : ∃ instr, kernel.code[lo]? = some ⟨some (guard,false),.tcMma instr⟩)
    (hGuard : s.regs guard = some (.pred true)) (hStep : WStep kernel Assumptions.all l g s ev u) :
    ∃ d op acc mask, ev = some ⟨lo,.tc (.mma d op acc mask)⟩ := by
  obtain ⟨instr,hCode⟩ := hCode
  have hSite : kernel.code[s.pc]? = some ⟨some (guard,false),.tcMma instr⟩ :=
    hAt.symm ▸ hCode
  have hFault := returningStepFaultNone hStep
  rcases hStep with ⟨_,ht⟩ | ⟨e,rfl,he⟩
  · simp [Tau,out,hFault,hSite,guardHolds,readReg,hGuard,bind,Except.bind,pure,
      Except.pure,Op.isLocal] at ht
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hSite] at hCode
  obtain rfl := Option.some.inj hCode.symm
  obtain ⟨d,op,acc,mask,hKind⟩ := returningMma hFire
  have hTag := (estep_source_pc he).trans hAt
  obtain ⟨tag,kind⟩ := e
  change tag = lo at hTag
  change kind = _ at hKind
  subst tag
  subst kind
  exact ⟨d,op,acc,mask,rfl⟩

/-- Steady and tail PV use the two value-ready gates, respectively. -/
def pvReadySite (block : Fin 4) : Fin 4 := if block.val < 2 then 1 else 3

private theorem countReadyAtOtherStep {g : Nat} {s u : TState} {ev : Option Event}
    {history : List Event} {pos : Nat} (site : Fin 4) (hPc : s.pc ≠ (slotWait site).pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) (hGet : ev.isSome = true → history[pos]? = ev)
    :
    (history.take (pos + if ev.isSome then 1 else 0)).countP (readyAtSite site) =
      (history.take pos).countP (readyAtSite site) := by
  rcases hStep with ⟨rfl, _⟩ | ⟨event, rfl, he⟩
  · rfl
  have hLoc : event.pc ≠ (slotWait site).pc := (estep_source_pc he).trans_ne hPc
  have hMark : readyAtSite site event = false := by
    obtain ⟨pc, kind⟩ := event
    cases kind <;> try rfl
    case wait loc parity ok acquire scope =>
      cases ok <;> simp [readyAtSite, hLoc]
  have hEvent := hGet rfl
  change (history.take (pos + 1)).countP (readyAtSite site) = _
  rw [List.take_add_one, hEvent, List.countP_append]
  simp [hMark]

private def FragmentMark (isPv : Bool) (block : Fin 4) (history : List Event)
    (pos lo hi guard : Nat) (s : TState) : Prop :=
  fragmentWindow lo hi s.pc → s.fault = none → s.regs guard = some (.pred true) →
    ∃ k < pos, (isPv = false → k+1 = pos) ∧
      (isPv = true → (history.take k).countP (readyAtSite (pvReadySite block)) =
        (history.take pos).countP (readyAtSite (pvReadySite block))) ∧
      (∀ j e, k < j → j < pos → history[j]? = some e → lo < e.pc ∧ e.pc < hi) ∧
      ∃ d op acc mask, history[k]? = some ⟨lo,.tc (.mma d op acc mask)⟩

private theorem qkAdvancesFromGuard {g : Nat} {s u : TState} {ev : Option Event} (block : Fin 4)
    (step : Fin 8) (hAt : s.pc = qkPc block+step.val)
    (hGuard : s.regs (qkGuard block) = some (.pred true))
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    u.pc = s.pc+1 := by
  have hFault := returningStepFaultNone hStep
  have hRule := qkCode block step
  rcases hStep with ⟨_,ht⟩ | ⟨_,_,he⟩
  · simp [Tau,out,hFault,hAt,hRule,guardHolds,readReg,hGuard,bind,Except.bind,pure,
      Except.pure,Op.isLocal] at ht
  obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source he
  rw [hAt,hRule] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hNext := fires_tcMma (.inr (.inl rfl)) hFires
  exact congrArg TState.pc hNext

private theorem pvAdvancesFromGuard {g : Nat} {s u : TState} {ev : Option Event} (block : Fin 4)
    (step : Fin 8) (hAt : s.pc = pvPc block step)
    (hGuard : s.regs (pvSite block).guard = some (.pred true))
    (hStep : WStep kernel Assumptions.all l g s ev u) : u.pc = s.pc+1 := by
  have hFault := returningStepFaultNone hStep
  have hRule := pvCode block step
  rcases hStep with ⟨_,ht⟩ | ⟨_,_,he⟩
  · simp [Tau,out,hFault,hAt,hRule,guardHolds,readReg,hGuard,bind,Except.bind,pure,
      Except.pure,Op.isLocal] at ht
  obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source he
  rw [hAt,hRule] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hNext := fires_tcMmaTs hFires
  exact congrArg TState.pc hNext

private theorem fragmentMarkStep {g : Nat} {s u : TState} {e : Option Event} {history : List Event}
    {pos : Nat} (isPv : Bool) (block : Fin 4) (frag : Fin 7) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hStep : WStep kernel Assumptions.all l g s e u) (hGet : e.isSome = true → history[pos]? = e)
    (hMarked : FragmentMark isPv block history pos
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩)
      (fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩)
      (fragmentGuard isPv block) s) :
    FragmentMark isPv block history (pos + if e.isSome then 1 else 0)
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩)
      (fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩)
      (fragmentGuard isPv block) u := by
  let loStep : Fin 8 := ⟨frag.val,by have := frag.isLt; omega⟩
  let lo := fragmentPc isPv block loStep
  let hi := fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩
  let guard := fragmentGuard isPv block
  change FragmentMark isPv block history pos lo hi guard s at hMarked
  change FragmentMark isPv block history _ lo hi guard u
  intro hU _ hGuard
  have hChecked {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      fragmentPathCode guard lo hi s.pc ins = true :=
    fragmentPathAt isPv block frag hPc.1 hPc.2 hc
  have hFrame (hHere : lo ≤ s.pc ∧ s.pc ≤ hi) : s.regs guard = some (.pred true) := by
    rw [← hGuard]
    symm
    apply mmaStepReg (by omega) hPc.2 _ hStep
    intro ins hc
    have hNo := (Bool.and_eq_true_iff.mp (hChecked hc)).1
    simpa [hHere] using hNo
  rcases windowEntryStep hPc (fun _ hc => (Bool.and_eq_true_iff.mp (hChecked hc)).2) hStep hU with
    hInside | hHead
  · have hPred := hFrame ⟨hInside.1.le,hInside.2⟩
    obtain ⟨k,hk,_,hCount,hInterval,hK⟩ :=
      hMarked hInside (returningStepFaultNone hStep) hPred
    have hBelow : s.pc < hi := by
      by_contra! hAt
      have hEq : s.pc = hi := le_antisymm hInside.2 hAt
      have hAdvance : u.pc = s.pc+1 := by
        cases isPv
        · exact qkAdvancesFromGuard block ⟨frag.val+1,by have := frag.isLt; omega⟩
            hEq hPred hStep
        · exact pvAdvancesFromGuard block ⟨frag.val+1,by have := frag.isLt; omega⟩
            hEq hPred hStep
      have hEnd := hU.2
      omega
    refine ⟨k, lt_of_lt_of_le hk (Nat.le_add_right ..), ?_, ?_, ?_, hK⟩
    · intro hQk
      subst isPv
      have hSucc : hi = lo+1 := by simp [hi,lo,loStep,fragmentPc,Nat.add_assoc]
      have hS : s.pc = hi := by have := hInside.1; have := hInside.2; omega
      have hU' : u.pc ≤ hi := hU.2
      have hAdv := qkAdvancesFromGuard block ⟨frag.val+1,by have := frag.isLt; omega⟩
        hS hPred hStep
      omega
    · intro hPv
      have hLower : (slotWait (pvReadySite block)).pc ≤ lo := by
        change (slotWait (pvReadySite block)).pc ≤ fragmentPc isPv block loStep
        rw [hPv]
        have hCertified : ∀ (b : Fin 4) (f : Fin 8),
            (slotWait (pvReadySite b)).pc ≤ pvPc b f := by decide
        exact hCertified block loStep
      exact (hCount hPv).trans (countReadyAtOtherStep (pvReadySite block)
        (Nat.ne_of_gt (hLower.trans_lt hInside.1)) hStep hGet).symm
    · intro j event hAfter hBefore he
      by_cases hOld : j < pos
      · exact hInterval j event hAfter hOld he
      cases e with
      | none => simp at hBefore; omega
      | some current =>
        have hIndex : j = pos := by simp at hBefore; omega
        subst j
        have hEvent : current = event := Option.some.inj ((hGet rfl).symm.trans he)
        subst event
        rcases hStep with ⟨hNone,_⟩ | ⟨issued,hTag,hEventStep⟩
        · cases hNone
        obtain rfl := Option.some.inj hTag
        have hPC := estep_source_pc hEventStep
        simpa only [hPC] using And.intro hInside.1 hBelow
  · have hUpper := fragmentIncreasing isPv block frag
    change lo < hi at hUpper
    obtain ⟨d,op,acc,mask,rfl⟩ := guardedMmaFires hHead (fragmentCode isPv block loStep)
      (hFrame ⟨hHead.symm ▸ Nat.le_refl _,hHead.symm ▸ hUpper.le⟩) hStep
    refine ⟨pos,by simp,fun _ => rfl,fun _ => ?_,?_,d,op,acc,mask,hGet rfl⟩
    case refine_2 =>
      intro j e hOld hNew
      simp at hNew
      omega
    have hObserved := hGet rfl
    change (history.take pos).countP _ = (history.take (pos + 1)).countP _
    rw [List.take_add_one, hObserved, List.countP_append]
    simp [readyAtSite]
end

private theorem previousFragmentGet {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (isPv : Bool) (block : Fin 4) (frag : Fin 7)
    {g index d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g,index) = some
      ⟨fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩,.tc (.mma d op acc mask)⟩) :
    ∃ k < index, (isPv = false → k+1 = index) ∧
      (isPv = true → ((X.tr g).take k).countP (readyAtSite (pvReadySite block)) =
        ((X.tr g).take index).countP (readyAtSite (pvReadySite block))) ∧
      (∀ j e, k < j → j < index → X.get (g,j) = some e →
        fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩ < e.pc ∧
          e.pc < fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩) ∧
      ∃ d' op' acc' mask', X.get (g,k) = some
      ⟨fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩,
        .tc (.mma d' op' acc' mask')⟩ := by
  have hStart := fragmentBounds isPv block ⟨frag.val,by have := frag.isLt; omega⟩
  have hTarget := fragmentBounds isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩
  obtain ⟨pos,s,_,hIndex,ht,hWalk⟩ := initialMmaTrace hp hX he hTarget.1 hTarget.2
  have hPc : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  have hMark : FragmentMark isPv block (X.tr g) (pos+1)
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩)
      (fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩)
      (fragmentGuard isPv block) s := by
    intro hw _ _
    have h := hw.1
    rw [ht.1] at h
    omega
  obtain ⟨t,_,hFrame,hStep⟩ := Thread.mmaRoleReplayAt
    (fun cursor s => FragmentMark isPv block (X.tr g) cursor
      (fragmentPc isPv block ⟨frag.val,by have := frag.isLt; omega⟩) _
      (fragmentGuard isPv block) s)
    (by
      intro s u ev pos hLo hHi _ hKnown hStep hActual
      have hGet : ev.isSome = true → (X.tr g)[pos]? = ev := by
        cases ev with
        | none => simp
        | some e => exact fun _ => hActual e rfl
      have h := fragmentMarkStep isPv block frag ⟨hLo,hHi⟩ hStep hGet hKnown
      cases ev <;> simpa using h)
    hPc hShape hMark hWalk hIndex he hTarget.2
  have hSite : t.pc = fragmentPc isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩ :=
    (estep_source_pc hStep).symm
  obtain ⟨instr,hCode⟩ := fragmentCode isPv block ⟨frag.val+1,by have := frag.isLt; omega⟩
  have hc : kernel.code[t.pc]? =
      some ⟨some (fragmentGuard isPv block,false),.tcMma instr⟩ := hSite.symm ▸ hCode
  have hFault : t.fault = none := by
    cases hf : t.fault with
    | none => rfl
    | some f =>
      obtain ⟨tm,hOut,hFire⟩ := hStep
      simp only [out,hf,Out.ev.injEq] at hOut
      subst tm
      exact Kind.noConfusion (congrArg Event.kind hFire.1)
  exact hFrame ⟨hSite.symm ▸ fragmentIncreasing isPv block frag,hSite.symm ▸ Nat.le_refl _⟩
    hFault (mmaGuardTrue hc rfl hStep)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {block : Fin 4} {frag : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
include hp hX

/-- An actual noninitial QK fragment has its previous fragment on the same lane. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.QkInstruction.previousFragmentAdjacent
    (hi : Thread.QkInstruction X i block frag d op acc mask) (hPos : 0 < frag.val) :
    ∃ k, k+1 = i.2 ∧ ∃ d' op' accum' mask',
      Thread.QkInstruction X (i.1,k) block ⟨frag.val-1,by omega⟩ d' op' accum' mask' := by
  let step : Fin 7 := ⟨frag.val-1,by have := frag.isLt; omega⟩
  have hStep : (⟨step.val+1,by have := step.isLt; omega⟩ : Fin 8) = frag :=
    Fin.ext (by change frag.val-1+1 = frag.val; omega)
  have he := hi.decoded
  rw [← hStep] at he
  obtain ⟨g,j⟩ := i
  obtain ⟨k,_,hK,_,_,d',op',acc',mask',hGet⟩ := previousFragmentGet hp hX false block step he
  exact ⟨k,hK rfl,d',op',acc',mask',Thread.QkInstruction.of_decoded hGet⟩

/-- An actual noninitial QK fragment has its previous fragment on the same lane. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.QkInstruction.previousFragment
    (hi : Thread.QkInstruction X i block frag d op acc mask) (hPos : 0 < frag.val) :
    ∃ k < i.2, ∃ d' op' accum' mask',
      Thread.QkInstruction X (i.1,k) block ⟨frag.val-1,by omega⟩ d' op' accum' mask' := by
  obtain ⟨k,hEq,h⟩ := hi.previousFragmentAdjacent hp hX hPos
  exact ⟨k,by omega,h⟩

/-- An actual noninitial PV fragment has its previous fragment on the same lane. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.PvInstruction.previousFragmentSameReadyCount
    (hi : Thread.PvInstruction X i block frag d op acc mask) (hPos : 0 < frag.val) :
    ∃ k < i.2,
      ((X.tr i.1).take k).countP (readyAtSite (pvReadySite block)) =
        ((X.tr i.1).take i.2).countP (readyAtSite (pvReadySite block)) ∧
      ∃ d' op' accum' mask',
      Thread.PvInstruction X (i.1,k) block ⟨frag.val-1,by omega⟩ d' op' accum' mask' := by
  let step : Fin 7 := ⟨frag.val-1,by have := frag.isLt; omega⟩
  have hStep : (⟨step.val+1,by have := step.isLt; omega⟩ : Fin 8) = frag :=
    Fin.ext (by change frag.val-1+1 = frag.val; omega)
  have he := hi.decoded
  rw [← hStep] at he
  obtain ⟨g,j⟩ := i
  obtain ⟨k, hK, _, hCount, _, d', op', acc', mask', hGet⟩ :=
    previousFragmentGet hp hX true block step he
  exact ⟨k, hK, hCount rfl, d', op', acc', mask', Thread.PvInstruction.of_decoded hGet⟩

/-- An actual noninitial PV fragment has its previous fragment on the same lane. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.PvInstruction.previousFragment
    (hi : Thread.PvInstruction X i block frag d op acc mask) (hPos : 0 < frag.val) :
    ∃ k < i.2, ∃ d' op' accum' mask',
      Thread.PvInstruction X (i.1,k) block ⟨frag.val-1,by omega⟩ d' op' accum' mask' := by
  obtain ⟨k, hk, _, hPrev⟩ := hi.previousFragmentSameReadyCount hp hX hPos
  exact ⟨k, hk, hPrev⟩
end

private theorem pvFragmentIntervalExcluded (block : Fin 4) (frag : Fin 7) :
    let lower := pvPc block ⟨frag.val,by have := frag.isLt; omega⟩
    let upper := pvPc block ⟨frag.val+1,by have := frag.isLt; omega⟩
    (∀ (b : Fin 4) (f : Fin 8),
      ¬ (lower < qkPc b+f.val ∧ qkPc b+f.val < upper) ∧
      ¬ (lower < pvPc b f ∧ pvPc b f < upper)) ∧
    (∀ b : Fin 4, ¬ (lower < (commitSite (qkCommitSite b)).pc ∧
      (commitSite (qkCommitSite b)).pc < upper)) ∧
    (∀ gate : Fin 4, ¬ (lower < readyHead gate ∧ readyHead gate < upper)) := by
  fin_cases block <;> fin_cases frag <;> decide

/-- Consecutive actual PV fragments have no intervening MMA, score commit,
or K/V ready on their elected lane, even when a probability poll separates them. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.PvInstruction.previousFragmentNoInterveningIssue
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d : Nat} {block : Fin 4} {frag : Fin 8} {op : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}
    (hi : Thread.PvInstruction X (g,index) block frag d op acc mask) (hPos : 0 < frag.val) :
    ∃ k < index, ∃ d' op' acc' mask',
      Thread.PvInstruction X (g,k) block ⟨frag.val-1,by omega⟩ d' op' acc' mask' ∧
      (∀ {j dst args accum enabled}, k < j → j < index →
        ¬ X.MmaIssue (g,j) dst args accum enabled) ∧
      (∀ {j cta stage spec rank}, k < j → j < index →
        ¬ Thread.Scores.ScoreCommit l X (g,j) cta stage spec rank) ∧
      (∀ {j slot parity}, k < j → j < index →
        ¬ Thread.Mma.ReadyPoll l X g j slot parity true .cta) := by
  let prev : Fin 7 := ⟨frag.val-1,by have := frag.isLt; omega⟩
  have hStep : (⟨prev.val+1,by have := prev.isLt; omega⟩ : Fin 8) = frag :=
    Fin.ext (by change frag.val-1+1 = frag.val; omega)
  have he := hi.decoded
  rw [← hStep] at he
  obtain ⟨k,hK,_,_,hBetween,d',op',acc',mask',hPrev⟩ :=
    previousFragmentGet hp hX true block prev he
  have hSites := pvFragmentIntervalExcluded block prev
  refine ⟨k,hK,d',op',acc',mask',Thread.PvInstruction.of_decoded hPrev,?_,?_,?_⟩
  · intro j dst args accum enabled hAfter hBefore hIssue
    rcases Thread.actualMmaInstruction hX hIssue with ⟨b,f,hQk⟩ | ⟨b,f,hPv⟩
    · exact (hSites.1 b f).1 (hBetween j _ hAfter hBefore hQk.decoded)
    · exact (hSites.1 b f).2 (hBetween j _ hAfter hBefore hPv.decoded)
  · intro j cta stage sp rank hAfter hBefore hScore
    obtain ⟨b,_,hGet⟩ := Thread.Scores.scoreCommitSite hp hX hScore
    exact hSites.2.1 b (hBetween j _ hAfter hBefore hGet)
  · intro j slot parity hAfter hBefore hReady
    have hIssue : X.MmaIssue (g,index) d op acc mask := ⟨_,hi.decoded⟩
    obtain ⟨pc,hGet,hSite⟩ := hReady.useSite hp hX (Thread.mmaIssueElection hp hX hIssue).1
    rcases hSite with ⟨rfl,_⟩ | ⟨rfl,_,_⟩ | ⟨hSite,_⟩
    · exact hSites.2.2 0 (hBetween j _ hAfter hBefore hGet)
    · exact hSites.2.2 2 (hBetween j _ hAfter hBefore hGet)
    · rcases hSite with rfl | rfl
      · exact hSites.2.2 1 (hBetween j _ hAfter hBefore hGet)
      · exact hSites.2.2 3 (hBetween j _ hAfter hBefore hGet)

private def pvCommitWindowTop (steady : Bool) (stage : Fin 2) : Nat :=
  if steady then (if stage = 0 then 2462 else 2519) else 2646

private def pvCommitWindow (steady : Bool) (stage : Fin 2) (site : Nat) : Prop :=
  fragmentWindow (pvPc (Thread.firstPvBlock steady stage) 7) (pvCommitWindowTop steady stage) site

private instance (steady : Bool) (stage : Fin 2) (site : Nat) :
    Decidable (pvCommitWindow steady stage site) :=
  inferInstanceAs (Decidable (fragmentWindow _ _ _))

private theorem pvCommitIngress (steady : Bool) (stage : Fin 2) {site : Nat} {ins : Instr}
    (hLo : 1907 ≤ site) (hHi : site < 2768) (hc : kernel.code[site]? = some ins) :
    windowIngressCode (pvPc (Thread.firstPvBlock steady stage) 7)
      (pvCommitWindowTop steady stage) site ins.op = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have h : code.all (fun (ins,site) =>
      windowIngressCode (pvPc (Thread.firstPvBlock steady stage) 7)
      (pvCommitWindowTop steady stage) site ins.op) = true := by
    cases steady <;> fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,site)
  apply List.mem_of_getElem? (i := site-1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem pvCommitCountInWindow {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} {history : List Event} {index : Nat}
    (steady : Bool) (stage : Fin 2) (hInside : pvCommitWindow steady stage s.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → history[index]? = some e) :
    (history.take (index + ev.toList.length)).countP (readyAtSite (if steady then 1 else 3)) =
      (history.take index).countP (readyAtSite (if steady then 1 else 3)) := by
  let site : Fin 4 := if steady then 1 else 3
  have hBounds : (slotWait site).pc ≤ pvPc (Thread.firstPvBlock steady stage) 7 := by
    cases steady <;> fin_cases stage <;> decide
  have hGet : ev.isSome = true → history[index]? = ev := by
    cases ev with
    | none => simp
    | some e => exact fun _ => hActual e rfl
  have hCount := countReadyAtOtherStep site (Nat.ne_of_gt (hBounds.trans_lt hInside.1))
    hStep hGet
  cases ev <;> exact hCount

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem pvBeforeMatchedCommit (steady : Bool) (stage : Fin 2)
    {g index tag electTag inst leader : Nat} {spec : TcCommit.Spec}
    (he : X.get (g,index) = some ⟨tag,.tc (.commit spec)⟩) (hTag : pvCommitWindow steady stage tag)
    (hElect : X.Elect (g,index-1) electTag (2^32-1) inst leader) (hWinner : laneOf l g = leader) :
    ∃ k < index,
      ((X.tr g).take k).countP (readyAtSite (if steady then 1 else 3)) =
        ((X.tr g).take index).countP (readyAtSite (if steady then 1 else 3)) ∧
      ∃ d op acc mask,
        Thread.PvInstruction X (g,k) (Thread.firstPvBlock steady stage) 7 d op acc mask := by
  let block := Thread.firstPvBlock steady stage
  let mark (pos : Nat) (s : TState) : Prop :=
    pvCommitWindow steady stage s.pc → ∃ k < pos,
      ((X.tr g).take k).countP (readyAtSite (if steady then 1 else 3)) =
        ((X.tr g).take pos).countP (readyAtSite (if steady then 1 else 3)) ∧
      ∃ d op acc mask, Thread.PvInstruction X (g,k) block 7 d op acc mask
  have hLoAudit : ∀ steady stage, 2145 ≤ pvPc (Thread.firstPvBlock steady stage) 7 := by decide
  have hHiAudit : ∀ steady stage, pvCommitWindowTop steady stage < 2768 := by decide
  have hTagLo : 2145 ≤ tag := (hLoAudit steady stage).trans hTag.1.le
  have hTagHi : tag < 2768 := hTag.2.trans_lt (hHiAudit steady stage)
  obtain ⟨pos,s,_,hIndex,ht,hWalk⟩ := initialMmaTrace hp hX he hTagLo hTagHi
  have hPc : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  have hEarly : ∀ (steady : Bool) (stage : Fin 2),
      1908 < pvPc (Thread.firstPvBlock steady stage) 7 := by decide
  have hStart : mark (pos+1) s := by
    intro hWindow
    have h := hWindow.1
    rw [ht.1] at h
    exact (Nat.not_lt_of_ge (hEarly steady stage).le h).elim
  obtain ⟨t,_,hFrame,hStep⟩ := Thread.mmaRoleReplayAt
    (fun cursor s => Thread.PvGateSelection l X g block cursor s ∧ mark cursor s)
    (by
      intro s u ev pos hLo hHi hShape hKnown hStep hActual
      refine ⟨hKnown.1.step ⟨hLo,hHi⟩ hShape.1 hStep hActual,?_⟩
      intro hNew
      rcases windowEntryStep ⟨hLo,hHi⟩ (fun _ hc => pvCommitIngress steady stage hLo hHi hc)
        hStep hNew with hInside | hHead
      · obtain ⟨k, hK, hCount, hPrev⟩ := hKnown.2 hInside
        have hKeep := pvCommitCountInWindow steady stage hInside hStep hActual
        exact ⟨k, hK.trans_le (Nat.le_add_right ..), hCount.trans hKeep.symm, hPrev⟩
      · have hGuard := Thread.PvGateSelection.fragmentGuard hX hKnown.1 7 hHead hElect hWinner
        obtain ⟨d,op,acc,mask,hEv⟩ :=
          guardedMmaFires hHead (fragmentCode true block 7) hGuard hStep
        refine ⟨pos, by simp [hEv], ?_, d, op, acc, mask,
          Thread.PvInstruction.of_decoded (hActual _ hEv)⟩
        rw [hEv]
        change List.countP _ ((X.tr g).take pos) = List.countP _ ((X.tr g).take (pos + 1))
        have hObserved := hActual _ hEv
        change (X.tr g)[pos]? = _ at hObserved
        rw [List.take_add_one, hObserved, List.countP_append]
        simp [readyAtSite])
    hPc hShape ⟨Thread.PvGateSelection.entry block ht.1,hStart⟩
    hWalk hIndex he hTagHi
  have hSite : t.pc = tag := (estep_source_pc hStep).symm
  exact hFrame.2 (hSite.symm ▸ hTag)

/-- Every terminal output commit follows the final PV fragment of either stage.
The commit's issuing lane wins each actual full-mask tail election. -/
theorem finalPvBeforeMatchedOutputCommit (stage : Fin 2) {g index tag electTag inst leader : Nat}
    {spec : TcCommit.Spec} (he : X.get (g,index) = some ⟨tag,.tc (.commit spec)⟩)
    (hTag : tag = 2642 ∨ tag = 2646) (hElect : X.Elect (g,index-1) electTag (2^32-1) inst leader)
    (hWinner : laneOf l g = leader) :
    ∃ k < index, ∃ d op acc mask,
      Thread.PvInstruction X (g,k) (Thread.firstPvBlock false stage) 7 d op acc mask := by
  have hLate : ∀ stage : Fin 2, pvPc (Thread.firstPvBlock false stage) 7 < 2642 := by decide
  have hWindow : pvCommitWindow false stage tag :=
    ⟨by have := hLate stage; omega,by change tag ≤ 2646; omega⟩
  obtain ⟨k, hK, _, hFrag⟩ := pvBeforeMatchedCommit hp hX false stage he hWindow hElect hWinner
  exact ⟨k, hK, hFrag⟩

/-- A real recurring score notification follows the preceding PV fragment of its stage. -/
theorem steadyPvBeforeRecurringScoreCommitWithReady (stage : Fin 2) {g index : Nat}
    {spec : TcCommit.Spec}
    (he : X.get (g,index) = some ⟨if stage = 0 then 2418 else 2519,.tc (.commit spec)⟩) :
    ∃ k < index,
      ((X.tr g).take k).countP (readyAtSite 1) = ((X.tr g).take index).countP (readyAtSite 1) ∧
      ∃ d op acc mask,
      Thread.PvInstruction X (g,k) (Thread.firstPvBlock true stage) 7 d op acc mask := by
  let block : Fin 4 := ⟨stage.val+2,by have := stage.isLt; omega⟩
  have hSite : (if stage = 0 then 2418 else 2519) = (commitSite (qkCommitSite block)).pc := by
    fin_cases stage <;> rfl
  have hGet : X.get (g,index) = some
      ⟨(commitSite (qkCommitSite block)).pc,.tc (.commit spec)⟩ := by
    rw [← hSite]
    exact he
  obtain ⟨_,inst,leader,hElect,hWinner⟩ := scoreCommitLeader hp hX block hGet
  have hWindow : pvCommitWindow true stage (if stage = 0 then 2418 else 2519) := by
    fin_cases stage <;> decide
  exact pvBeforeMatchedCommit hp hX true stage he hWindow hElect hWinner

/-- A real recurring score notification follows the preceding PV fragment of its stage. -/
theorem steadyPvBeforeRecurringScoreCommit (stage : Fin 2) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g,index) = some ⟨if stage = 0 then 2418 else 2519,.tc (.commit spec)⟩) :
    ∃ k < index, ∃ d op acc mask,
      Thread.PvInstruction X (g,k) (Thread.firstPvBlock true stage) 7 d op acc mask := by
  obtain ⟨k,hK,_,hFrag⟩ := steadyPvBeforeRecurringScoreCommitWithReady hp hX stage he
  exact ⟨k,hK,hFrag⟩

/-- A delivered loop or tail value release follows each PV bank and retains the
same ready count from its last fragment. -/
theorem pvLastFragmentBeforeValueRelease (steady : Bool) (stage : Fin 2) {g index : Nat}
    {spec : TcCommit.Spec}
    (he : X.get (g, index) =
      some ⟨(commitSite (releaseCommitSite (if steady then 1 else 3))).pc, .tc (.commit spec)⟩) :
    ∃ k < index,
      ((X.tr g).take k).countP (readyAtSite (if steady then 1 else 3)) =
        ((X.tr g).take index).countP (readyAtSite (if steady then 1 else 3)) ∧
      ∃ d op acc mask, Thread.PvInstruction X (g, k)
        (Thread.firstPvBlock steady stage) 7 d op acc mask := by
  obtain ⟨_, _, _, hElect, hWinner⟩ :=
    readyReleaseLeader hp hX (if steady then 1 else 3) he
  have hWindow : pvCommitWindow steady stage
      (commitSite (releaseCommitSite (if steady then 1 else 3))).pc := by
    cases steady <;> fin_cases stage <;> decide
  exact pvBeforeMatchedCommit hp hX steady stage he hWindow hElect hWinner

omit hp hX in
private def qkCommitWindow (block : Fin 4) (site : Nat) : Prop :=
  fragmentWindow (qkPc block+7) (commitSite (qkCommitSite block)).pc site

omit hp hX in
private theorem qkCommitIngress (block : Fin 4) {site : Nat} {ins : Instr}
    (hLo : 1907 ≤ site) (hHi : site < 2768) (hc : kernel.code[site]? = some ins) :
    windowIngressCode (qkPc block+7) (commitSite (qkCommitSite block)).pc site ins.op = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have h : code.all (fun (ins,site) =>
      windowIngressCode (qkPc block+7) (commitSite (qkCommitSite block)).pc site ins.op) =
        true := by
    fin_cases block <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,site)
  apply List.mem_of_getElem? (i := site-1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

omit hp hX in
private def qkCommitElectionCount (block : Fin 4) (pc : Nat) : Nat :=
  if qkPc block + 8 < pc then 1 else 0

omit hp hX in
private theorem qkCommitClockStep {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (block : Fin 4) (hRole : RoleShape s)
    (hOld : qkCommitWindow block s.pc) (hNew : qkCommitWindow block u.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    qkCommitElectionCount block s.pc + ev.toList.length = qkCommitElectionCount block u.pc := by
  let i := qkCommitSite block
  let election := (electSite (commitElection i)).pc
  let finish := (commitSite i).pc
  have hElect : election = qkPc block + 8 := by fin_cases block <;> decide
  have hFinish : finish = election + 3 := by fin_cases block <;> decide
  have hBounds : 2145 ≤ election ∧ finish < 2768 := by fin_cases block <;> decide
  have hOld' : election ≤ s.pc ∧ s.pc ≤ finish := by
    change qkPc block + 7 < s.pc ∧ s.pc ≤ finish at hOld
    omega
  have hNew' : election ≤ u.pc ∧ u.pc ≤ finish := by
    change qkPc block + 7 < u.pc ∧ u.pc ≤ finish at hNew
    omega
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) (show s.pc < 2768 by omega)
    (l := l) (g := g) (t := s)
  by_cases hAtElect : s.pc = election
  · have hs : At s election [] :=
      ⟨hAtElect, hRole.2.2 (by omega), hRole.2.1, returningStepFaultNone hStep, trivial⟩
    have hOut := electTemplate (l := l) (g := g) (commitElection i) hs
    rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
    · rw [Tau, hOut] at ht
      cases ht
    · obtain ⟨tm, hTm, hFire⟩ := he
      rw [hOut] at hTm
      obtain rfl := Out.ev.inj hTm.symm
      obtain ⟨inst, leader, rfl, hU⟩ := hFire
      obtain rfl := Option.some.inj hU
      have hPc : (electState l g s (commitElection i) leader).pc = s.pc + 1 := by
        change (((electSite (commitElection i)).result.elim s
          (fun r => setReg s r (b32 leader))).pc + 1) = s.pc + 1
        cases (electSite (commitElection i)).result <;> rfl
      simp [qkCommitElectionCount, ← hElect, hAtElect, hPc]
  have hPath : s.pc = election + 1 ∨ s.pc = election + 2 ∨ s.pc = finish := by omega
  have hNoFallBack {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      (match ins.op with
        | .bra dest _ => election < dest
        | .brx .. => False
        | _ => True) := by
    rcases hPath with hNext | hBranch | hCommit
    · have hc' := (gateCode i).1
      change kernel.code[election + 1]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hNext.symm ▸ hc'))
      exact True.intro
    · have hc' := (gateCode i).2
      change kernel.code[election + 2]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hBranch.symm ▸ hc'))
      change election < finish + 1
      omega
    · have hc' := commitCode i
      change kernel.code[finish]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hCommit.symm ▸ hc'))
      exact True.intro
  rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
  · have ht' : Tau kernel [] l g s u := by unfold Tau at ht ⊢; rwa [← hCore]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hAfter : election < u.pc := by
      rcases tau_core_frame hc ht' with rfl | hFrame
      · change election < s.pc + 1
        omega
      have hPc := hFrame.pc
      have hBranch := hNoFallBack hc
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
      case bra target uniform => rw [hop] at hBranch; exact hPc ▸ hBranch
      case brx => rw [hop] at hBranch; exact hBranch.elim
      all_goals omega
    have hBefore : election < s.pc := by omega
    simp [qkCommitElectionCount, ← hElect, hBefore, hAfter]
  · obtain ⟨ins, hc, hLocal, hFire⟩ := estep_event_source he
    rcases hPath with hNext | hBranch | hCommit
    · have hc' := (gateCode i).1
      change kernel.code[election + 1]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hNext.symm ▸ hc'))
      cases hLocal
    · have hc' := (gateCode i).2
      change kernel.code[election + 2]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hBranch.symm ▸ hc'))
      cases hLocal
    · have hc' := commitCode i
      change kernel.code[finish]? = _ at hc'
      obtain rfl := Option.some.inj (hc.symm.trans (hCommit.symm ▸ hc'))
      obtain rfl := fires_tcCommit hFire
      change election ≤ s.pc + 1 ∧ s.pc + 1 ≤ finish at hNew'
      omega

/-- The score election is the one event between the last QK fragment and its score commit. -/
theorem qkLastFragmentAdjacentToScoreCommit (block : Fin 4) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g,index) = some ⟨(commitSite (qkCommitSite block)).pc,.tc (.commit spec)⟩) :
    ∃ k, k + 2 = index ∧ ∃ d op acc mask, Thread.QkInstruction X (g,k) block 7 d op acc mask := by
  let target := (commitSite (qkCommitSite block)).pc
  let mark (pos : Nat) (s : TState) : Prop :=
    qkCommitWindow block s.pc →
      ∃ k, k + 1 + qkCommitElectionCount block s.pc = pos ∧ ∃ d op acc mask,
      Thread.QkInstruction X (g,k) block 7 d op acc mask
  have hBounds : 2145 ≤ target ∧ target < 2768 := by fin_cases block <;> decide
  obtain ⟨_,_,_,hElect,hWinner⟩ := scoreCommitLeader hp hX block he
  obtain ⟨pos,s,_,hIndex,ht,hWalk⟩ := initialMmaTrace hp hX he hBounds.1 hBounds.2
  have hPc : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  have hEarly : ∀ b : Fin 4, 1908 < qkPc b + 7 := by decide
  have hStart : mark (pos+1) s := by
    intro hWindow
    have h := hWindow.1
    rw [ht.1] at h
    exact (Nat.not_lt_of_ge (hEarly block).le h).elim
  obtain ⟨t,_,hFrame,hStep⟩ := Thread.mmaRoleReplayAt
    (fun cursor s => Thread.QkGateSelection l X g block cursor s ∧ mark cursor s)
    (by
      intro s u ev pos hLo hHi hShape hKnown hStep hActual
      refine ⟨hKnown.1.step ⟨hLo,hHi⟩ hShape.1 hStep hActual,?_⟩
      intro hNew
      rcases windowEntryStep ⟨hLo,hHi⟩ (fun _ hc => qkCommitIngress block hLo hHi hc)
        hStep hNew with hInside | hHead
      · obtain ⟨k,hK,hPrev⟩ := hKnown.2 hInside
        have hMove := qkCommitClockStep block hShape.1 hInside hNew hStep
        exact ⟨k, by omega, hPrev⟩
      · have hGuard := Thread.QkGateSelection.fragmentGuard hX hKnown.1 7 hHead hElect hWinner
        obtain ⟨d,op,acc,mask,hEv⟩ :=
          guardedMmaFires hHead (fragmentCode false block 7) hGuard hStep
        refine ⟨pos,?_,d,op,acc,mask,Thread.QkInstruction.of_decoded (hActual _ hEv)⟩
        have hNext := qkAdvancesFromGuard block 7 hHead hGuard hStep
        simp [hEv, qkCommitElectionCount, hNext, hHead])
    hPc hShape ⟨Thread.QkGateSelection.entry block ht.1,hStart⟩
    hWalk hIndex he hBounds.2
  have hSite : t.pc = target := (estep_source_pc hStep).symm
  have hLate : ∀ b : Fin 4, qkPc b + 7 < (commitSite (qkCommitSite b)).pc := by decide
  obtain ⟨k, hRank, hLast⟩ :=
    hFrame.2 ⟨hSite.symm ▸ hLate block, hSite.symm ▸ Nat.le_refl target⟩
  have hLastFlight : qkCommitElectionCount block target = 1 := by fin_cases block <;> decide
  rw [hSite, hLastFlight] at hRank
  exact ⟨k, by omega, hLast⟩

omit hp hX in
private theorem steadyIngressAt (stage : Fin 2) {site : Nat} {ins : Instr}
    (hLo : 1907 ≤ site) (hHi : site < 2768) (hc : kernel.code[site]? = some ins) :
    windowIngressCode (pvPc (Thread.firstPvBlock true stage) 0) Thread.carryMarker site ins.op =
      true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have h : code.all (fun (ins,site) =>
      windowIngressCode (pvPc (Thread.firstPvBlock true stage) 0)
        Thread.carryMarker site ins.op) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,site)
  apply List.mem_of_getElem? (i := site-1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem selectedPvBeforeMarker (stage : Fin 2) {g j elect tag inst leader : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hPc : e.pc = Thread.carryMarker)
    (hElect : X.Elect (g,elect) tag (2^32-1) inst leader) (hWinner : laneOf l g = leader) :
    ∃ k < j, ∃ d op acc mask, Thread.PvInstruction X (g,k)
      (Thread.firstPvBlock true stage) 0 d op acc mask := by
  let block := Thread.firstPvBlock true stage
  let mark (pos : Nat) (s : TState) := fragmentWindow (pvPc block 0) Thread.carryMarker s.pc →
    ∃ k < pos, ∃ d op acc mask, Thread.PvInstruction X (g,k) block 0 d op acc mask
  have hRange : 2145 ≤ e.pc ∧ e.pc < 2768 := by rw [hPc]; decide
  obtain ⟨pos,s,_,hIndex,ht,hWalk⟩ := initialMmaTrace hp hX he hRange.1 hRange.2
  have hBounds : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  have hStart : mark (pos+1) s := by
    intro h
    have hSite := h.1
    rw [ht.1] at hSite
    have hLo := (fragmentBounds true block 0).1
    change 2145 ≤ pvPc block 0 at hLo
    omega
  obtain ⟨t,_,hAt,hStep⟩ := Thread.mmaRoleReplayAt
    (fun pos s => Thread.PvGateSelection l X g block pos s ∧ mark pos s)
    (by
      intro s u ev cursor hLo hHi hFrame hInv hStep hActual
      refine ⟨hInv.1.step ⟨hLo,hHi⟩ hFrame.1 hStep hActual,?_⟩
      intro hNew
      rcases windowEntryStep ⟨hLo,hHi⟩ (fun _ hc => steadyIngressAt stage hLo hHi hc)
        hStep hNew with hInside | hHead
      · obtain ⟨k,hK,hIssue⟩ := hInv.2 hInside
        exact ⟨k,by omega,hIssue⟩
      · have hGuard := hInv.1.firstGuard hX hHead hElect hWinner
        obtain ⟨d,op,acc,mask,rfl⟩ := guardedMmaFires hHead (fragmentCode true block 0)
          hGuard hStep
        exact ⟨cursor,by simp,d,op,acc,mask,Thread.PvInstruction.of_decoded (hActual _ rfl)⟩)
    hBounds hShape ⟨Thread.PvGateSelection.entry block ht.1,hStart⟩ hWalk hIndex he hRange.2
  have hSite : t.pc = Thread.carryMarker := (estep_source_pc hStep).symm.trans hPc
  have hLo : pvPc block 0 < Thread.carryMarker := by
    unfold block
    fin_cases stage <;> decide
  exact hAt.2 ⟨hSite.symm ▸ hLo,hSite.symm ▸ Nat.le_refl _⟩

/-- A carried PV visit has an actual earlier steady PV for the same stage. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.PvInstruction.previousSteadyFragment {i : EvId}
    {block : Fin 4} {frag : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : Thread.PvInstruction X i block frag d op acc mask)
    (hCarry : Thread.PvPriorSteadyVisit X i) :
    ∃ k < i.2, ∃ d' op' acc' mask', Thread.PvInstruction X (i.1,k)
      (Thread.firstPvBlock true (pvSite block).stage) 0 d' op' acc' mask' := by
  obtain ⟨j,hJ,e,hE,hSite⟩ := hCarry.closingEvent
  obtain ⟨_,ordinal,_,_,leader,hElect,hWinner⟩ := Thread.mmaIssueElection hp hX ⟨_,hi.decoded⟩
  obtain ⟨k,hK,hIssue⟩ := selectedPvBeforeMarker hp hX (pvSite block).stage hE hSite hElect hWinner
  exact ⟨k,hK.trans hJ,hIssue⟩

end PTX.Kernels.TmlFa4Fwd.Mma
