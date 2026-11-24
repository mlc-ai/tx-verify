-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.Invariant
public import Kernels.FlashKdaFwd.Packed.Election
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

def tailJump : Instr := ⟨some (2,false),.bra 1882 false⟩

set_option maxRecDepth 60000 in
private theorem tailSite : Transfers.slice 1880 2 = some [tailJump,Election.stop] := by kernel_rfl

private def guardInstr (pc : Nat) : Instr :=
  if pc = 1414 then Election.tid else if pc = 1415 then Election.laneId else
  if pc = 1416 then Election.zeroLane else if pc = 1417 then Election.guardOp else
  if pc = 1454 then Election.jump else if pc = 1880 then tailJump else Election.stop

private theorem guard_site {pc : Nat} (h : special pc) :
    kernel.code[pc]? = some (guardInstr pc) ∧ (guardInstr pc).op.isLocal = true := by
  have head := Election.sites.2.1
  have main := Election.sites.2.2
  unfold special at h
  rcases h with lo | rfl | rfl | rfl | rfl
  · obtain ⟨lower,upper⟩ := lo
    interval_cases pc <;> constructor
    all_goals first | rfl |
      (first
        | exact fetch (pc := 1414) (i := 0) (by decide) (by decide) head
        | exact fetch (pc := 1414) (i := 1) (by decide) (by decide) head
        | exact fetch (pc := 1414) (i := 2) (by decide) (by decide) head
        | exact fetch (pc := 1414) (i := 3) (by decide) (by decide) head)
  · exact ⟨fetch (pc := 1454) (i := 0) (by decide) (by decide) main,rfl⟩
  · exact ⟨fetch (pc := 1454) (i := 1) (by decide) (by decide) main,rfl⟩
  · exact ⟨fetch (pc := 1880) (i := 0) (by decide) (by decide) tailSite,rfl⟩
  · exact ⟨fetch (pc := 1880) (i := 1) (by decide) (by decide) tailSite,rfl⟩

theorem no_guard_event (base : Nat → Nat → Nat) {L : Launch} {g : Nat} {t u : TState}
    {e : Event} (h : special t.pc) (step : EStep kernel (Prologue.assumptions base) L g t e
      (some u)) : False := by
  obtain ⟨ins,site,nonlocal,_⟩ := EventFrame.estep_event_source step
  obtain ⟨eq,localOp⟩ := guard_site h
  rw [eq] at site
  cases site
  simp [localOp] at nonlocal

private theorem executed {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t u : TState} {i : Instr} (s : Tau K A L g t u) (site : K.code[t.pc]? = some i)
    (guard : guardHolds t i.guard = .ok true) (localOp : i.op.isLocal = true) :
    execLocalA A L g t i.op = .ok u := by
  unfold Tau out at s
  cases f : t.fault <;> simp only [f,site,guard,localOp,↓reduceIte] at s
  · cases h : execLocalA A L g t i.op <;> simp_all
  · cases s

private theorem skipped {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {t u : TState} {i : Instr} (s : Tau K A L g t u) (site : K.code[t.pc]? = some i)
    (guard : guardHolds t i.guard = .ok false) : u = skip t := by
  unfold Tau out at s
  cases f : t.fault <;> simp_all

private theorem thread_exec (base : Nat → Nat → Nat) (L : Launch) (g : Nat) (t : TState)
    (tid : (L.tidOf g).x = 129) :
    execLocalA (Prologue.assumptions base) L g t Election.tid.op =
      .ok (next (setReg t 667 (b32 129))) := by
  change execMove L g t Election.tid.op = _
  simp [Election.tid, execMove, readValue, readBits, sregValue, SReg.width, Dim3.get, tid,
    DType.width, Value.bytes, b32, truncBits, bind, Except.bind, pure, Except.pure]

private theorem lane_exec (base : Nat → Nat → Nat) (L : Launch) (g : Nat) (t : TState)
    (tid : t.regs 667 = some (b32 129)) :
    execLocalA (Prologue.assumptions base) L g t Election.laneId.op =
      .ok (next (setReg t 668 (b32 1))) := by
  change execInt L g t ⟨.and,.int .b 32,false,[some 668],[.reg 667,.imm 31]⟩ = _
  simp [execInt,readBits,readReg,b32,tid,DType.width,truncBits,bind,Except.bind,pure,Except.pure]

private theorem zero_exec (base : Nat → Nat → Nat) (L : Launch) (g : Nat) (t : TState)
    (lane : t.regs 668 = some (b32 1)) :
    execLocalA (Prologue.assumptions base) L g t Election.zeroLane.op =
      .ok (next (setReg t 35 (.pred false))) := by
  change execInt L g t ⟨.setp .eq none,.int .b 32,false,[some 35],[.reg 668,.imm 0]⟩ = _
  simp [execInt,readBits,readReg,b32,lane,DType.width,truncBits,bind,Except.bind,pure,Except.pure]
  rfl

private theorem jump_guard {t : TState} (facts : Facts t) (pc : tested t.pc) :
    guardHolds t (some (2,false)) = .ok false := by
  simp [guardHolds,readReg,facts.check pc,bind,Except.bind,pure,Except.pure]

theorem tau_special (base : Nat → Nat → Nat) {L : Launch} {g : Nat} {t u : TState}
    (tid : (L.tidOf g).x = 129) (facts : Facts t) (h : special t.pc)
    (s : Tau kernel (Prologue.assumptions base) L g t u) : Facts u := by
  obtain ⟨site,localOp⟩ := guard_site h
  rcases h with inside | mainJump | mainStop | endJump | endStop
  · have eqs : t.pc = 1414 ∨ t.pc = 1415 ∨ t.pc = 1416 ∨ t.pc = 1417 := by omega
    rcases eqs with pc | pc | pc | pc
    all_goals rw [pc] at localOp
    all_goals rw [pc] at site
    all_goals have run := executed s (pc ▸ site) (by rfl) localOp
    · have val := Except.ok.inj ((thread_exec base L g t tid).symm.trans run)
      subst u
      constructor <;> simp [next,setReg,pc,allowed,tested,facts.elected]
    · have val := Except.ok.inj ((lane_exec base L g t (facts.threadId pc)).symm.trans run)
      subst u
      constructor <;> simp [next,setReg,pc,allowed,tested,facts.elected]
    · have val := Except.ok.inj ((zero_exec base L g t (facts.laneId pc)).symm.trans run)
      subst u
      constructor <;> simp [next,setReg,pc,allowed,tested,facts.elected]
    · have guard := Election.guarded base L g t false false (facts.laneZero pc) facts.elected
      have val := Except.ok.inj (guard.symm.trans run)
      subst u
      constructor <;> simp [next,setReg,pc,allowed,tested,facts.elected]
  · have flag := jump_guard facts (by simp [tested,mainJump])
    have skipState := skipped s site (by rw [mainJump]; exact flag)
    subst u
    constructor <;> simp [skip,allowed,tested,mainJump,facts.elected,facts.check (by
      simp [mainJump,tested])]
  · have run := executed s site (by rw [mainStop]; rfl) localOp
    rw [mainStop] at run
    exact False.elim (by cases (Election.stop_rule base L g t).symm.trans run)
  · have flag := jump_guard facts (by simp [tested,endJump])
    have skipState := skipped s site (by rw [endJump]; exact flag)
    subst u
    constructor <;> simp [skip,allowed,tested,endJump,facts.elected,facts.check (by
      simp [endJump,tested])]
  · have run := executed s site (by rw [endStop]; rfl) localOp
    rw [endStop] at run
    exact False.elim (by cases (Election.stop_rule base L g t).symm.trans run)

end FlashKda.Packed.ProducerControl
