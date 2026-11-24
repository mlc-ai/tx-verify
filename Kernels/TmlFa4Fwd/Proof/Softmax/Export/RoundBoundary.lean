-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundOrdinal

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax
variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

def boundary : Site → Bool
  | .ws _ | .fin 0 => true
  | _ => false

private def closing : Site → Bool
  | .pwend _ => true
  | _ => false

private theorem table (lz : Bool) :
    allSites.all (fun s => (nexts lz s).all fun t =>
      !boundary t || s == .wq || closing s) = true := by cases lz <;> decide +kernel

/-- A moving score poll increments credit exactly once. -/
theorem soft_start_poll {i e r v k acc out}
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g,i) = some e)
    (ev : EvS p L g ⟨.ws r,v,k,acc⟩ e)
    (hn : succ p L g ⟨.ws r,v,k,acc⟩ e = some (some out)) (left : out.site ≠ .ws r) :
    Tm.sPolls L X g (Prologue.warpIndex L g/4) (i+1) =
      Tm.sPolls L X g (Prologue.warpIndex L g/4) i + 1 := by
  obtain ⟨ok,kind⟩ := ev.1
  cases ok
  · simp only [succ,kind,Bool.false_eq_true,ite_false,Option.some.injEq] at hn
    exact (left (by cases hn; rfl)).elim
  · obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp he
    unfold Tm.sPolls
    rw [List.take_succ_eq_append_getElem hi,eq,okPolls_snoc]
    simp only [okPoll,sourceWaitSuccess,kind,bl_eq hw,pollOff,Tm.sFull,decide_true,ite_true]

/-- At either boundary of a nonempty prefix of rounds, the preceding completed round supplies
all three running statistics. Failed polls at the boundary preserve them. -/
theorem soft_boundary_previous (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) {u} : ∀ {i d}, i ≤ (X.tr g).length →
    softState p L X g i = some d → boundary d.site = true →
    Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1 →
    ∃ j < i, ∃ r v k acc, softState p L X g j = some ⟨.pwend r,v,k,acc⟩ ∧
      Tm.sPolls L X g (Prologue.warpIndex L g/4) j = u+1 ∧
      d.v.mf = finE (Data.maximum p L g v r) ∧ d.v.mr = (Data.maximum p L g v r).toReal ∧
      d.v.rs = Data.sumAfter p L g v r := by
  intro i
  induction i with
  | zero => intro d _ hs; simp only [softState,Frame.stateAt_zero] at hs; cases hs
  | succ i ih =>
    intro d hi hs enter credit
    obtain ⟨j,e,pr,idx,get,old,hn⟩ := softState_pred hp hi hs
      (fun eq => by rw [eq] at enter; cases enter)
    have idx' : j = i := by omega
    subst j
    have ev := softState_event hp hX get old
    rcases succ_cases hn with ⟨same,keep,_,_⟩ | move
    · have src := same ▸ enter
      have noPoll : okPoll (Tm.sFull L (g/L.block) (Prologue.warpIndex L g/4)) e = false := by
        obtain ⟨s,v,k,acc⟩ := pr
        cases s <;> try cases src
        case ws r =>
          obtain ⟨ok,kind⟩ := ev.1
          cases ok
          · simp only [okPoll,sourceWaitSuccess,kind]
          · simp only [succ,kind,ite_true,Option.some.injEq] at hn
            cases hn; cases same
        case fin =>
          rcases ev.1 with ⟨a,bs,kind⟩ | ⟨f,kind⟩ <;> simp only [okPoll,sourceWaitSuccess,kind]
      have cr : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1 := by
        obtain ⟨hlt,eq⟩ := List.getElem?_eq_some_iff.mp get
        unfold Tm.sPolls at credit ⊢
        simpa only [List.take_succ_eq_append_getElem hlt,eq,okPolls_snoc,noPoll,
          Bool.false_eq_true,ite_false,Nat.add_zero] using credit
      obtain ⟨j,hj,r,v,k,acc,st,c,stats⟩ := ih (by omega) old src cr
      exact ⟨j,by omega,r,v,k,acc,st,c,keep ▸ stats⟩
    · have rule := List.all_eq_true.mp (List.all_eq_true.mp (table (lz L g)) _ (mem_allSites _))
        _ move.1
      simp only [enter,Bool.not_true,Bool.false_or,Bool.or_eq_true,beq_iff_eq] at rule
      rcases rule with wq | endr
      · have zero := wq_credit hp hX hw get old wq
        have step := soft_credit_step hw get ev (by rw [wq]; decide)
        omega
      · obtain ⟨s,v,k,acc⟩ := pr
        cases s <;> try cases endr
        rename_i r
        obtain ⟨ok,kind⟩ := ev.1
        have eq := soft_credit_step hw get ev (by change (192 : Nat) ≠ 80; decide)
        cases ok
        · simp only [succ,kind,Bool.false_eq_true,ite_false,Option.some.injEq] at hn
          cases hn; cases enter
        · simp only [succ,kind,ite_true,Option.some.injEq] at hn
          cases hn
          exact ⟨i,by omega,r,v,k,acc,old,eq.symm.trans credit,Data.afterRound_stats _ _ _ _ _⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Values
