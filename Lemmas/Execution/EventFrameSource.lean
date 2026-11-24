-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameBase
public import Lemmas.Register.RegisterFrame

@[expose] public section

section
namespace PTX.EventFrame
open PTX
noncomputable section
theorem load_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sp : Space} {nc : Bool} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} :
    ReturnedFrame t.pc (loadTmpl A L g t sp nc w ds base off) := by
  unfold loadTmpl
  split
  · trivial
  · split
    · split
      · exact fun _ => afterLoad_pc _ _ _
      · trivial
    · exact fun _ => afterLoad_pc _ _ _

theorem store_frame {L : Launch} {g : Nat} {t : TState}
    {sp : Space} {w : Nat} {base : Nat} {off : Int} {srcs : List Opnd} :
    ReturnedFrame t.pc (storeTmpl L g t sp w base off srcs) := by
  unfold storeTmpl
  split
  · trivial
  · split
    · trivial
    · split
      · trivial
      · exact afterStore_pc _ _

theorem acquire_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {scope : MbarScope} {sp : Space} {w : Nat} {d base : Nat} {off : Int} :
    ReturnedFrame t.pc (acquireLoadTmpl A L g t scope sp w d base off) := by
  have h := load_frame (A:=A) (L:=L) (g:=g) (t:=t) (sp:=sp) (nc:=false)
    (w:=w) (ds:=[d]) (base:=base) (off:=off)
  unfold acquireLoadTmpl
  split <;> simp_all [ReturnedFrame,CallbackFrame]

theorem release_frame {L : Launch} {g : Nat} {t : TState}
    {scope : MbarScope} {sp : Space} {w : Nat} {base : Nat} {off : Int} {v : Opnd} :
    ReturnedFrame t.pc (releaseStoreTmpl L g t scope sp w base off v) := by
  have h := store_frame (L:=L) (g:=g) (t:=t) (sp:=sp) (w:=w)
    (base:=base) (off:=off) (srcs:=[v])
  unfold releaseStoreTmpl
  split <;> simp_all [ReturnedFrame,CallbackFrame]

theorem bar_frame {L : Launch} {g : Nat} {t : TState} {a : Opnd} {n : Option Opnd}
    {mode : BarMode} : ReturnedFrame t.pc (barTmpl L g t a n mode) := by
  unfold barTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next]

theorem shfl_frame {L : Launch} {g : Nat} {t : TState} {mode : ShflMode}
    {d : Nat} {p : Option Nat} {a b c mask : Opnd} :
    ReturnedFrame t.pc (shflTmpl L g t mode d p a b c mask) := by
  cases p <;> unfold shflTmpl
  all_goals repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem vote_frame {L : Launch} {g : Nat} {t : TState} {d a : Nat} {neg : Bool} {mask : Opnd} :
    ReturnedFrame t.pc (voteTmpl L g t d a neg mask) := by
  unfold voteTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem voteMode_frame {L : Launch} {g : Nat} {t : TState} {mode : VoteMode} {d a : Nat}
    {neg : Bool} {mask : Opnd} : ReturnedFrame t.pc (voteModeTmpl L g t mode d a neg mask) := by
  unfold voteModeTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem redux_frame {L : Launch} {g : Nat} {t : TState} {op : ReduxOp} {signed : Bool}
    {d : Nat} {a mask : Opnd} : ReturnedFrame t.pc (reduxTmpl L g t op signed d a mask) := by
  unfold reduxTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem match_frame {L : Launch} {g : Nat} {t : TState} {all : Bool} {w : Nat}
    {d p : Option Nat} {a mask : Opnd} : ReturnedFrame t.pc (matchTmpl L g t all w d p a mask) := by
  unfold matchTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem activemask_frame {t : TState} {d : Nat} : ReturnedFrame t.pc (activemaskTmpl t d) := by
  simp [activemaskTmpl,ReturnedFrame,CallbackFrame,next,setReg]

theorem elect_frame {L : Launch} {g : Nat} {t : TState} {d : Option Nat}
    {p : Nat} {mask : Opnd} : ReturnedFrame t.pc (electTmpl L g t d p mask) := by
  cases d <;> unfold electTmpl
  all_goals repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next,setReg]

theorem warpBar_frame {L : Launch} {g : Nat} {t : TState} {mask : Opnd} :
    ReturnedFrame t.pc (warpBarTmpl L g t mask) := by
  unfold warpBarTmpl
  repeat' split
  all_goals simp [ReturnedFrame,CallbackFrame,next]

theorem afterAccessLoad_pc (t : TState) (ext : MemExt) (w : Nat) (ds : List Nat)
    (bs : List (Option Byte)) :
    (afterAccessLoad t ext w ds bs).pc = t.pc ∨ (afterAccessLoad t ext w ds bs).pc = t.pc + 1 := by
  unfold afterAccessLoad
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem access_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {a : MemAccess} :
    ReturnedFrame t.pc (accessTmpl A L g t a) := by
  unfold accessTmpl bulkInitTmpl
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact fun _ => afterAccessLoad_pc _ _ _ _ _
    | exact afterStore_pc _ _
    | exact Or.inr rfl

theorem afterAtom_pc (t : TState) (ds : List (Option Nat)) (k n : Nat)
    (old : List (Option Byte)) :
    (afterAtom t ds k n old).pc = t.pc ∨ (afterAtom t ds k n old).pc = t.pc + 1 := by
  unfold afterAtom
  dsimp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (rw [setRegs_pc]; exact Or.inr rfl)

theorem atom_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {a : MemAccess} :
    ReturnedFrame t.pc (atomTmpl A L g t a) := by
  unfold atomTmpl
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | (intro v
       refine ⟨?_, fun _ => ?_⟩
       · exact afterAtom_pc t a.dsts _ _ v
       · exact afterAtom_pc t a.dsts _ _ v)

theorem mem_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {a : MemAccess} :
    ReturnedFrame t.pc (memTmpl A L g t a) := by
  unfold memTmpl
  split
  · split
    · exact acquire_frame
    · exact load_frame
    · exact release_frame
    · exact store_frame
    · exact access_frame
  · exact atom_frame
  · split
    · exact access_frame
    · exact True.intro

theorem warp_frame {L : Launch} {g : Nat} {t : TState} {w : WarpInstr} :
    ReturnedFrame t.pc (warpTmpl L g t w) := by
  unfold warpTmpl
  split
  · exact shfl_frame
  · exact vote_frame
  · exact voteMode_frame
  · exact redux_frame
  · exact match_frame
  · exact activemask_frame
  · exact elect_frame
  · exact warpBar_frame
  · exact True.intro

theorem setMaxNReg_frame {t : TState} {inc : Bool} {n : Nat} :
    ReturnedFrame t.pc (SetMaxNReg.tmpl t inc n) := by
  unfold SetMaxNReg.tmpl
  split <;> simp [ReturnedFrame,CallbackFrame,next]


end
end PTX.EventFrame
end

section
namespace PTX.EventFrame
open PTX
noncomputable section
/-- The tensor-load case on its own: a fault or one copy issue (`tensorTmpl_cpTensor_cases`). -/
theorem cpTensor_frame_case {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd}
    {cs : List Opnd} {mc : Option (Nat × Opnd)} {lm : TensorMode} {policy : Option Opnd} :
    ReturnedFrame t.pc
      (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff mc lm policy)) := by
  rcases tensorTmpl_cpTensor_cases (L := L) (g := g) (t := t) (ca := ca) (grp := grp) (dst := dst)
      (off := off) (map := map) (cs := cs) (mb := mb) (moff := moff) (mc := mc)
      (policy := policy) with
    ⟨f, hf⟩ | ⟨a, s, u, hf, hregs, hpc⟩
  · rw [hf]; exact True.intro
  · rw [hf]; exact hpc

theorem tensor_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tensorTmpl L g t op) := by
  cases op
  case cpTensor => exact cpTensor_frame_case
  all_goals trivial

theorem tensorStore_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tensorStoreTmpl L g t op) := by
  cases op <;> simp only [tensorStoreTmpl]
  all_goals first
    | trivial
    | exact Or.inr rfl
    | apply ofExec_frame
  all_goals repeat' first

    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (apply allOk_bind; intro v)

theorem tensorPrefetch_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tensorPrefetchTmpl L g t op) := by
  cases op <;> simp only [tensorPrefetchTmpl]
  all_goals first | trivial | apply ofExec_frame
  all_goals repeat' first
    | exact True.intro
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (apply allOk_bind; intro v)
    | split

theorem clc_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (clcTmpl L g t op) := by
  cases op <;> simp only [clcTmpl]
  all_goals first | trivial | apply ofExec_frame
  all_goals repeat' first
    | exact True.intro
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (apply allOk_bind; intro v)

    | split

theorem tcCommit_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tcCommitTmpl L g t op) := by
  cases op <;> simp only [tcCommitTmpl]
  all_goals first | trivial | apply ofExec_frame
  all_goals repeat' first
    | exact True.intro
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (apply allOk_bind; intro v)

    | split


end
end PTX.EventFrame
end

section
namespace PTX.EventFrame
open PTX
noncomputable section
theorem mma_frame {L : Launch} {g : Nat} {t : TState} {m : TcMmaInstr} :
    ReturnedFrame t.pc (mmaTmpl L g t m) := by
  unfold mmaTmpl
  split
  next => exact ofExec_frame (by
    all_goals repeat' first
      | exact True.intro
      | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
      | (apply allOk_bind; intro v)
      | split)
  next => exact ofExec_frame (by
    all_goals repeat' first
      | exact True.intro
      | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
      | (apply allOk_bind; intro v)
      | split)
  next => trivial

/-- A `tcgen05.ld` result only sets registers and a fault: it keeps the program counter. -/
theorem ldResult_pc (t : TState) (ds : List Nat) (r : Option TcLdRed) (vals : List Value) :
    (ldResult t ds r vals).pc = t.pc := by
  cases r with
  | none => simp [ldResult, setRegs_pc]
  | some r =>
    unfold ldResult
    repeat' split
    all_goals exact setRegs_pc t ds _

theorem tc_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tcTmpl L g t op) := by
  unfold tcTmpl
  split
  all_goals first | trivial | exact Or.inr rfl | exact mma_frame | apply ofExec_frame
  all_goals repeat' first
    | exact True.intro
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (change t.pc=t.pc ∨ t.pc=t.pc+1; exact Or.inl rfl)
    | (simpa only [setRegs_pc,next] using (Or.inr rfl : t.pc+1=t.pc ∨ t.pc+1=t.pc+1))
    | (apply allOk_bind; intro v)
    | intro v
    | (simp only [ldResult_pc, next])
    | split

theorem tma_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tmaTmpl L g t op) := by
  unfold tmaTmpl
  split
  all_goals first | trivial | exact Or.inr rfl | apply ofExec_frame
  all_goals repeat' first
    | exact True.intro
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (cases ‹Option Nat› <;> exact Or.inr rfl)
    | (apply allOk_bind; intro v)
    | intro v
    | (dsimp only; split)
    | (exact Or.inl rfl)
    | split

theorem tcLd_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (tcLdTmpl A L g t op) := by
  unfold tcLdTmpl
  split
  · split
    · have h := tc_frame (L := L) (g := g) (t := t) (op := op)
      generalize tcTmpl L g t op = m at h ⊢
      cases m <;> first | exact h | exact fun _ => Or.inl rfl
    · exact Or.inr rfl
  · exact tc_frame

theorem tcSt_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta : Nat} {ss : List Opnd} {sh : TcShape} :
    ReturnedFrame t.pc (tcStTmpl A L g t ta ss sh) := by
  unfold tcStTmpl
  split
  · split
    · split
      · exact .inl rfl
      · trivial
    · exact tc_frame
  · exact tc_frame

/-- A matrix event only sets registers and a fault, or advances once: it keeps a returning
thread at the current instruction or at the next one. -/
theorem afterMatrix_pc (t : TState) (w : Nat) (ds : List Nat) (recv : List (Option Byte)) :
    (afterMatrix t w ds recv).pc = t.pc ∨ (afterMatrix t w ds recv).pc = t.pc + 1 := by
  unfold afterMatrix
  dsimp only
  repeat' split
  all_goals simp [next, setRegs_pc]

theorem matrix_frame {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr} :
    ReturnedFrame t.pc (matrixTmpl L g t i) := by
  unfold matrixTmpl
  split
  · split
    · unfold matrixMoveTmpl
      dsimp only
      split
      · split
        · split
          · trivial
          · intro v
            dsimp only
            repeat' split
            all_goals first | exact Or.inl rfl | exact Or.inr rfl
        · split
          · trivial
          · exact Or.inr rfl
      · split
        · split
          · trivial
          · intro v
            dsimp only
            repeat' split
            all_goals exact Or.inl rfl
        · intro v
          exact afterMatrix_pc _ _ _ _
    · split
      · trivial
      · exact fun _ => afterMatrix_pc _ _ _ _
    · split
      · trivial
      · exact fun _ => afterMatrix_pc _ _ _ _
    · trivial
  · trivial

theorem cpAsync_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (cpAsyncTmpl L g t op) := by
  cases op <;> simp only [cpAsyncTmpl]
  all_goals first
    | trivial
    | exact Or.inr rfl
    | apply ofExec_frame
    | split
  all_goals repeat' first
    | exact True.intro
    | simp_all
    | (change t.pc+1=t.pc ∨ t.pc+1=t.pc+1; exact Or.inr rfl)
    | (change t.pc=t.pc ∨ t.pc=t.pc+1; exact Or.inl rfl)
    | (apply allOk_bind; intro v)
    | split

theorem asyncStore_frame {L : Launch} {g : Nat} {t : TState} {s : AsyncStore} :
    ReturnedFrame t.pc (asyncStoreTmpl L g t s) := by
  unfold asyncStoreTmpl
  apply ofExec_frame
  repeat' first
    | split
    | (apply allOk_bind; intro v)
    | (dsimp only; split)
    | (exact Or.inr rfl)

theorem fence_frame {L : Launch} {g : Nat} {t : TState} {op : Op} :
    ReturnedFrame t.pc (fenceTmpl L g t op) := by
  cases op <;> simp only [fenceTmpl]
  all_goals repeat' first
    | trivial
    | exact Or.inr rfl
    | split

theorem widen_frame {A : List Assumption} {pc : Nat} {site : Nat} {m : Tmpl}
    (h : ReturnedFrame pc m) : ReturnedFrame pc (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope =>
      cases release <;> cases scope <;> exact h
    case wait m parity k acquire scope =>
      cases acquire <;> cases scope <;> exact h
  · exact h


end
end PTX.EventFrame
end

section
namespace PTX.EventFrame
open PTX PTX.Proof
noncomputable section
/-- A read of the changing special registers runs the instruction's local rule on the read
values, which the thread's state after it records: the frame of an integer, move or conversion
instruction's local rule, which is no branch, keeps the position in the instruction or advances
it once. -/
theorem localSreg_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op}
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c)
    (hloc : ∀ t op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    ReturnedFrame t.pc (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl] <;> first
    | exact True.intro
    | (unfold sregTmpl
       intro vs
       dsimp only
       cases h : execLocalA A L g t (op.withSregValues vs) with
       | error f => exact Or.inl rfl
       | ok u =>
         rcases (hloc _ _ _ h).pc with hpc | hpc
         · rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
             exact Or.inr (by simpa [Op.withSregValues, nextPc] using hpc)
         · rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
             exact absurd hpc (by simp [Op.withSregValues, BrxTarget]))

/-- Every returning callback remains at the current instruction or advances
exactly once. Error callbacks retain their fault and position. A read of the changing special
registers continues at the state its local rule produces, so under that rule's frame it keeps the
position or advances once. -/
theorem eventTmpl_return_frame {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hloc : ∀ t op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    ReturnedFrame t.pc (eventTmpl A L g t op) := by
  cases op <;> simp only [eventTmpl]
  case mem => exact mem_frame
  case warp => exact warp_frame
  case matrix => exact matrix_frame
  case barSync | barSyncN | barArrive => exact bar_frame
  case cluster => exact Or.inr rfl
  case setMaxReg => exact setMaxNReg_frame
  case cpTensor => exact tensor_frame
  case prefetchTensor | prefetchBulk => exact tensorPrefetch_frame
  case cpAsync | cpAsyncCommit | cpAsyncWait | cpAsyncArrive => exact cpAsync_frame
  case asyncStore => exact asyncStore_frame
  case cpTensorStore | bulkCommit | bulkWait => exact tensorStore_frame
  case clcTryCancel | clcQuery => exact clc_frame
  case fence => exact fence_frame
  case mbarInit | mbarInval | fenceMbarInit | mbarArrive | mbarWait | cpBulk =>
    exact widen_frame tma_frame
  case tcCommit => exact tcCommit_frame
  case tcLd => exact tcLd_frame
  case tcSt => exact tcSt_frame
  case tcAlloc | tcDealloc | tcRelinquish | tcMma | tcFenceBefore | tcFenceAfter |
      tcWaitLd | tcWaitSt | tcCp | tcShift => exact tc_frame
  case int i =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame (.inl ⟨i, rfl⟩) hloc
  case move m =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame (.inr (.inl ⟨m, rfl⟩)) hloc
  case cvt c =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame (.inr (.inr ⟨c, rfl⟩)) hloc
  all_goals exact True.intro

/-- Event labels retain the exact source position, including exiting and
faulting events with no continuation. -/
theorem fires_source_pc {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hf : Fires pc m e o) : e.pc=pc := by
  cases m <;> simp only [Fires] at hf <;> aesop

/-- Instantiating any returning callback preserves its structural frame. -/
theorem callbackFrame_fires {P : TState → Prop} {pc : Nat} {m : Tmpl}
    {e : Event} {u : TState} (hm : CallbackFrame P m)
    (hf : Fires pc m e (some u)) : P u := by
  cases m <;> simp only [CallbackFrame,Fires] at hm hf <;> aesop

theorem estep_source_pc {K : Kernel} {A : List Assumption} {L : Launch}
    {g : Nat} {t : TState} {e : Event} {o : Option TState}
    (he : EStep K A L g t e o) : e.pc=t.pc := by
  obtain ⟨m,_,hf⟩ := he
  exact fires_source_pc hf

/-- A returned source event originates in the actual nonlocal instruction;
local failures and pending UB are retained as terminating cases instead. -/
theorem estep_event_source {K : Kernel} {A : List Assumption} {L : Launch}
    {g : Nat} {t u : TState} {e : Event}
    (he : EStep K A L g t e (some u)) :
    ∃ ins, K.code[t.pc]?=some ins ∧ ins.op.isLocal=false ∧
      Fires t.pc (eventTmpl A L g t ins.op) e (some u) := by
  obtain ⟨m,ho,hfire⟩ := he
  unfold out at ho
  split at ho
  · cases ho
    exact nomatch hfire.2
  · split at ho
    · cases ho
      exact nomatch hfire.2
    · rename_i ins hc
      split at ho
      · cases ho
        exact nomatch hfire.2
      · cases ho
      · split at ho
        · split at ho
          · cases ho
          · cases ho
            exact nomatch hfire.2
        · rename_i hlocal
          cases ho
          exact ⟨ins,hc,Bool.eq_false_iff.mpr hlocal,hfire⟩

/-- No safety, initialized-read, numerical profile or kernel-specific premise
is needed for the source position of a returning event. -/
theorem estep_return_pc {K : Kernel} {A : List Assumption} {L : Launch}
    {g : Nat} {t u : TState} {e : Event}
    (he : EStep K A L g t e (some u))
    (hloc : ∀ t op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    e.pc=t.pc ∧ (u.pc=t.pc ∨ u.pc=t.pc+1) := by
  obtain ⟨ins,_,_,hf⟩ := estep_event_source he
  exact ⟨estep_source_pc he,callbackFrame_fires (eventTmpl_return_frame hloc) hf⟩


end
end PTX.EventFrame
end
