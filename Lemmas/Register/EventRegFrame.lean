-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # Register frames of event steps

`LocalFrame` (`Lemmas/Register/RegisterFrame.lean`) says that a local step writes only the
registers of `writesRegs`. This file states the same for an event step (`EStep`): the thread's
state after the event differs from the state before it at most in the registers the instruction
writes as its destinations (`eventWrites`). `estep_regsKept` is the statement for a step of a
thread; `eventTmpl_regsKept` the one for every returning callback of an event template. -/

namespace PTX.EventFrame
open PTX PTX.Proof

noncomputable section

/-- The registers an event instruction writes: the destinations of `writesRegs`, the destinations
of a matrix load, the predicate of an `mbarrier.try_wait`, the state register of an
`mbarrier.arrive` (which the model clears), and the destinations and the reduction register of a
`tcgen05.ld`. -/
def eventWrites : Op → List Nat
  | .matrix m => m.dsts
  | .mbarWait d .. => [d]
  | .mbarArrive _ _ _ _ _ _ _ s => s.toList
  | .tcLd ds _ _ red => ds ++ (red.map (·.dst)).toList
  | op => writesRegs op

/-- `u` has the registers of `t` outside `W`. -/
def RegsKept (W : List Nat) (t u : TState) : Prop := ∀ r, r ∉ W → u.regs r = t.regs r

theorem RegsKept.refl {W : List Nat} {t : TState} : RegsKept W t t := fun _ _ => rfl

theorem setRegs_regs_of_not_mem {t : TState} {ds : List Nat} {vs : List Value} {r : Nat}
    (h : r ∉ ds) : (setRegs t ds vs).regs r = t.regs r := by
  induction ds generalizing t vs with
  | nil => cases vs <;> rfl
  | cons d ds ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [setRegs]
      rw [ih (fun hm => h (List.mem_cons_of_mem _ hm))]
      simp only [setReg]
      exact Function.update_of_ne (fun e => h (by subst e; exact List.mem_cons_self)) _ _

/-- Closes a goal `RegsKept W t u` for a continuation that writes registers of `W` only. -/
local macro "kept" : tactic => `(tactic| first
  | exact True.intro
  | (intro r hr; rfl)
  | (intro r hr
     simp_all [setReg, next, setRegs_regs_of_not_mem, Function.update_apply, mbarStateDest]))

theorem afterLoad_kept {W : List Nat} {t : TState} {ds : List Nat} (h : ∀ d ∈ ds, d ∈ W)
    (bs : List (Option Byte)) : RegsKept W t (afterLoad t ds bs) := by
  intro r hr
  unfold afterLoad
  split
  · rfl
  · split
    · rfl
    · exact setRegs_regs_of_not_mem (fun hm => hr (h _ hm))

theorem afterAccessLoad_kept {W : List Nat} {t : TState} {ext : MemExt} {w : Nat} {ds : List Nat}
    (h : ∀ d ∈ ds, d ∈ W) (bs : List (Option Byte)) :
    RegsKept W t (afterAccessLoad t ext w ds bs) := by
  intro r hr
  unfold afterAccessLoad
  split
  · rfl
  · split
    · rfl
    · exact setRegs_regs_of_not_mem (fun hm => hr (h _ hm))

theorem afterAtom_kept {W : List Nat} {t : TState} {ds : List (Option Nat)} {k n : Nat}
    (h : ∀ d ∈ ds.filterMap id, d ∈ W) (old : List (Option Byte)) :
    RegsKept W t (afterAtom t ds k n old) := by
  intro r hr
  unfold afterAtom
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rfl
      · split
        · exact setRegs_regs_of_not_mem (fun hm => hr (h _ hm))
        · rfl

theorem ldResult_kept {W : List Nat} {t : TState} {ds : List Nat} {red : Option TcLdRed}
    (h : ∀ d ∈ ds, d ∈ W) (hr : ∀ x ∈ red, x.dst ∈ W) (vals : List Value) :
    RegsKept W t (ldResult (next t) ds red vals) := by
  intro r hrW
  have hds : r ∉ ds := fun hm => hrW (h _ hm)
  cases red with
  | none => exact setRegs_regs_of_not_mem hds
  | some x =>
    cases hx : x.reduce vals with
    | ok v =>
      simp only [ldResult, hx, setReg]
      rw [Function.update_of_ne (fun e => hrW (by subst e; exact hr x rfl))]
      exact setRegs_regs_of_not_mem hds
    | error f =>
      simp only [ldResult, hx]
      exact setRegs_regs_of_not_mem hds

theorem afterMatrix_kept {W : List Nat} {t : TState} {w : Nat} {ds : List Nat}
    (h : ∀ d ∈ ds, d ∈ W) (recv : List (Option Byte)) :
    RegsKept W t (afterMatrix t w ds recv) := by
  intro r hr
  unfold afterMatrix
  dsimp only
  split
  · split
    · exact setRegs_regs_of_not_mem (t := { t with sub := 0, acc := [] })
        (fun hm => hr (h _ hm))
    · rfl
  · rfl

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

theorem load_kept {W : List Nat} {sp : Space} {nc : Bool} {w : Nat} {ds : List Nat} {base : Nat}
    {off : Int} (h : ∀ d ∈ ds, d ∈ W) :
    CallbackFrame (RegsKept W t) (loadTmpl A L g t sp nc w ds base off) := by
  unfold loadTmpl
  split
  · trivial
  · split
    · split
      · exact afterLoad_kept h
      · trivial
    · exact afterLoad_kept h

theorem store_kept {W : List Nat} {sp : Space} {w base : Nat} {off : Int} {srcs : List Opnd} :
    CallbackFrame (RegsKept W t) (storeTmpl L g t sp w base off srcs) := by
  unfold storeTmpl
  repeat' split
  all_goals first | trivial | (intro r hr; unfold afterStore; split <;> rfl)

theorem access_kept {W : List Nat} {a : MemAccess} (h : ∀ d ∈ a.regs, d ∈ W) :
    CallbackFrame (RegsKept W t) (accessTmpl A L g t a) := by
  unfold accessTmpl bulkInitTmpl
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact afterAccessLoad_kept h
    | (intro r hr; unfold afterStore; split <;> rfl)
    | (intro r hr; rfl)

theorem atom_kept {W : List Nat} {a : MemAccess} (h : ∀ d ∈ a.regs, d ∈ W) :
    CallbackFrame (RegsKept W t) (atomTmpl A L g t a) := by
  unfold atomTmpl
  dsimp only
  split
  · trivial
  · intro v
    exact ⟨afterAtom_kept h v, fun _ r hr => afterAtom_kept h v r hr⟩

theorem acquire_kept {W : List Nat} {scope : MbarScope} {sp : Space} {w d base : Nat}
    {off : Int} (hd : d ∈ W) :
    CallbackFrame (RegsKept W t) (acquireLoadTmpl A L g t scope sp w d base off) := by
  have h := load_kept (A := A) (L := L) (g := g) (t := t) (sp := sp) (nc := false) (w := w)
    (base := base) (off := off) (W := W) (ds := [d]) (by simp [hd])
  unfold acquireLoadTmpl
  split
  · rename_i heq
    rw [heq] at h
    exact h
  · exact h

theorem release_kept {W : List Nat} {scope : MbarScope} {sp : Space} {w base : Nat}
    {off : Int} {v : Opnd} :
    CallbackFrame (RegsKept W t) (releaseStoreTmpl L g t scope sp w base off v) := by
  have h := store_kept (W := W) (L := L) (g := g) (t := t) (sp := sp) (w := w) (base := base)
    (off := off) (srcs := [v])
  unfold releaseStoreTmpl
  split
  · rename_i heq
    rw [heq] at h
    exact h
  · exact h

theorem mem_kept {a : MemAccess} :
    CallbackFrame (RegsKept a.regs t) (memTmpl A L g t a) := by
  have hds : ∀ d ∈ a.regs, d ∈ a.regs := fun _ h => h
  unfold memTmpl
  split
  · split
    · rename_i d _ _ hr
      exact acquire_kept (by simp [hr])
    · exact load_kept hds
    · exact release_kept
    · exact store_kept
    · exact access_kept hds
  · exact atom_kept hds
  · split
    · exact access_kept hds
    · trivial

theorem head_join_mem {p : List (Option Nat)} {x : Nat} (h : p.head?.join = some x) :
    x ∈ p.filterMap id := by
  cases p with
  | nil => cases h
  | cons a p =>
    simp only [List.head?_cons, Option.join_some] at h
    simp [h]

theorem mbarStateDest_kept {W : List Nat} {s : Option Nat} (h : ∀ d ∈ s.toList, d ∈ W) :
    RegsKept W t (next (mbarStateDest t s)) := by
  intro r hr
  cases s with
  | none => rfl
  | some d =>
    simp only [mbarStateDest, next]
    exact Function.update_of_ne (fun e => hr (by subst e; exact h _ (by simp))) _ _

/-- Closes the goals of a template whose returning states are the state before with at most the
registers of `W` set. -/
local macro "kept_close" : tactic => `(tactic|
  (simp_all [setReg, next, setRegs_regs_of_not_mem, Function.update_apply, writesRegs,
    eventWrites, Option.join_eq_some_iff, List.head?_eq_some_iff]; done))

/-- Closes the goals of a template whose returning states are the state before with at most the
registers of `W` set. -/
local macro "kept_all" : tactic => `(tactic| all_goals repeat' first
  | exact True.intro
  | (intro r hr; rfl)
  | (intro r hr; kept_close)
  | (intro v r hr; kept_close)
  | (intro v b r hr; kept_close)
  | (exact mbarStateDest_kept (by simp [eventWrites]))
  | (apply ofExec_frame)
  | (apply allOk_bind; intro v)
  | (apply allOk_ite)
  | (intro hr; kept_close)
  | intro v
  | (dsimp only; split)
  | split
  | rfl
  | kept_close)

/-- Closes a returning state of a template with a second destination from the tail of the
destination list (`p.head?.join`), named by the last hypothesis. -/
local macro "kept_join" : tactic => `(tactic|
  (rename_i hj
   have hm := head_join_mem hj
   simp only [writesRegs, next, setReg, Function.update_apply] at *
   split_ifs <;> simp_all))

theorem warp_kept {w : WarpInstr} :
    CallbackFrame (RegsKept (writesRegs (.warp w)) t) (warpTmpl L g t w) := by
  unfold warpTmpl
  split
  · unfold shflTmpl
    kept_all
    all_goals kept_join
  · unfold voteTmpl
    kept_all
  · unfold voteModeTmpl
    kept_all
  · unfold reduxTmpl
    kept_all
  · unfold matchTmpl
    kept_all
    all_goals first
      | (rename_i hj _ _ _
         have hm := head_join_mem hj
         simp only [writesRegs, next, setReg, Function.update_apply] at *
         split_ifs <;> simp_all)
      | (rename_i hj _ _
         have hm := head_join_mem hj
         simp only [writesRegs, next, setReg, Function.update_apply] at *
         split_ifs <;> simp_all)
  · unfold activemaskTmpl
    kept_all
  · unfold electTmpl
    kept_all
  · unfold warpBarTmpl
    kept_all
  · exact True.intro

theorem bar_kept {W : List Nat} {a : Opnd} {n : Option Opnd} {mode : BarMode} :
    CallbackFrame (RegsKept W t) (barTmpl L g t a n mode) := by
  unfold barTmpl
  kept_all

theorem setMaxNReg_kept {W : List Nat} {inc : Bool} {n : Nat} :
    CallbackFrame (RegsKept W t) (SetMaxNReg.tmpl t inc n) := by
  unfold SetMaxNReg.tmpl
  kept_all

theorem tensor_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (tensorTmpl L g t op) := by
  cases op
  case cpTensor ca grp dst off map cs mb moff mc lm policy =>
    rcases tensorTmpl_cpTensor_cases (L := L) (g := g) (t := t) (ca := ca) (grp := grp)
      (dst := dst) (off := off) (map := map) (cs := cs) (mb := mb) (moff := moff) (mc := mc)
      (lm := lm) (policy := policy) with ⟨f, hf⟩ | ⟨a, s, u, hf, hregs, -⟩
    · rw [hf]; exact True.intro
    · rw [hf]; intro r _; exact congrFun hregs r
  all_goals exact True.intro

theorem tensorStore_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (tensorStoreTmpl L g t op) := by
  cases op <;> simp only [tensorStoreTmpl]
  kept_all

theorem tensorPrefetch_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (tensorPrefetchTmpl L g t op) := by
  cases op <;> simp only [tensorPrefetchTmpl]
  kept_all

theorem clc_kept {op : Op} :
    CallbackFrame (RegsKept (writesRegs op) t) (clcTmpl L g t op) := by
  cases op <;> simp only [clcTmpl]
  kept_all

theorem tcCommit_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (tcCommitTmpl L g t op) := by
  cases op <;> simp only [tcCommitTmpl]
  kept_all

theorem mma_kept {W : List Nat} {m : TcMmaInstr} :
    CallbackFrame (RegsKept W t) (mmaTmpl L g t m) := by
  unfold mmaTmpl
  kept_all

theorem cpAsync_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (cpAsyncTmpl L g t op) := by
  cases op <;> simp only [cpAsyncTmpl]
  all_goals first | exact True.intro | (intro r hr; rfl) | apply ofExec_frame | split
  all_goals repeat' first
    | exact True.intro
    | (intro r hr; rfl)
    | simp_all
    | (apply allOk_bind; intro v)
    | split

theorem asyncStore_kept {W : List Nat} {s : AsyncStore} :
    CallbackFrame (RegsKept W t) (asyncStoreTmpl L g t s) := by
  unfold asyncStoreTmpl
  kept_all

theorem fence_kept {W : List Nat} {op : Op} :
    CallbackFrame (RegsKept W t) (fenceTmpl L g t op) := by
  cases op <;> simp only [fenceTmpl]
  kept_all

theorem tma_kept {op : Op} :
    CallbackFrame (RegsKept (eventWrites op) t) (tmaTmpl L g t op) := by
  unfold tmaTmpl
  split
  all_goals simp only [eventWrites, writesRegs]
  kept_all

theorem tc_kept {op : Op} :
    CallbackFrame (RegsKept (eventWrites op) t) (tcTmpl L g t op) := by
  unfold tcTmpl
  split
  all_goals first | exact mma_kept | simp only [eventWrites, writesRegs]
  all_goals repeat' first
    | (intro v; exact ldResult_kept (by simp_all) (by simp_all) _)
    | (intro r hr; rfl)
    | exact True.intro
    | (apply ofExec_frame)
    | (apply allOk_bind; intro v)
    | split

theorem tcLd_kept {op : Op} :
    CallbackFrame (RegsKept (eventWrites op) t) (tcLdTmpl A L g t op) := by
  unfold tcLdTmpl
  split
  · split
    · have h := tc_kept (L := L) (g := g) (t := t) (op := op)
      generalize tcTmpl L g t op = m at h ⊢
      cases m <;> exact h
    · intro r hr; rfl
  · exact tc_kept

theorem tcSt_kept {ta : Nat} {ss : List Opnd} {sh : TcShape} :
    CallbackFrame (RegsKept (eventWrites (.tcSt ta ss sh)) t) (tcStTmpl A L g t ta ss sh) := by
  unfold tcStTmpl
  split
  · split
    · split
      · intro r hr; rfl
      · exact True.intro
    · exact tc_kept (t := { t with sub := 0 })
  · exact tc_kept

theorem widen_kept {W : List Nat} {site : Nat} {m : Tmpl} (h : CallbackFrame (RegsKept W t) m) :
    CallbackFrame (RegsKept W t) (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope =>
      cases release <;> cases scope <;> exact h
    case wait m parity k acquire scope =>
      cases acquire <;> cases scope <;> exact h
  · exact h

theorem matrix_kept {i : MatrixInstr} :
    CallbackFrame (RegsKept i.dsts t) (matrixTmpl L g t i) := by
  unfold matrixTmpl
  split
  · split
    · unfold matrixMoveTmpl
      dsimp only
      split
      · split
        · split
          · trivial
          · intro v r hr
            dsimp only
            repeat' split
            all_goals rfl
        · split
          · trivial
          · intro r hr; rfl
      · split
        · split
          · trivial
          · intro v r hr
            dsimp only
            repeat' split
            all_goals rfl
        · exact afterMatrix_kept (by simp_all)
    · split
      · trivial
      · exact afterMatrix_kept (by simp_all)
    · split
      · trivial
      · exact afterMatrix_kept (by simp_all)
    · trivial
  · trivial

/-- A read of changing special registers continues at the local rule of the values read; under a
frame of that rule the registers outside the instruction's destinations are kept. -/
theorem localSreg_kept {W : List Nat} {r : RuleId} {op : Op}
    (hsreg : ∀ vs u, execLocalA A L g t (op.withSregValues vs) = .ok u → RegsKept W t u) :
    CallbackFrame (RegsKept W t) (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl] <;> first
    | exact True.intro
    | (unfold sregTmpl
       intro vs
       dsimp only
       cases h : execLocalA A L g t (op.withSregValues vs) with
       | error f => intro r hr; rfl
       | ok u => exact hsreg vs u h)

/-- **Every returning callback of an event template writes only the instruction's destination
registers** (`eventWrites`), when the local rule that a read of changing special registers runs
(an integer, move or conversion instruction) does. -/
theorem eventTmpl_regsKept {op : Op}
    (hsreg : ((∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c) →
      ∀ vs u, execLocalA A L g t (op.withSregValues vs) = .ok u →
        RegsKept (eventWrites op) t u) :
    CallbackFrame (RegsKept (eventWrites op) t) (eventTmpl A L g t op) := by
  cases op <;> simp only [eventTmpl]
  case mem => exact mem_kept
  case warp => exact warp_kept
  case matrix => exact matrix_kept
  case barSync | barSyncN | barArrive => exact bar_kept
  case cluster => intro r hr; rfl
  case setMaxReg => exact setMaxNReg_kept
  case cpTensor => exact tensor_kept
  case prefetchTensor | prefetchBulk => exact tensorPrefetch_kept
  case cpAsync | cpAsyncCommit | cpAsyncWait | cpAsyncArrive => exact cpAsync_kept
  case asyncStore => exact asyncStore_kept
  case cpTensorStore | bulkCommit | bulkWait => exact tensorStore_kept
  case clcTryCancel | clcQuery => exact clc_kept
  case fence => exact fence_kept
  case mbarInit | mbarInval | fenceMbarInit | mbarArrive | mbarWait | cpBulk =>
    exact widen_kept tma_kept
  case tcCommit => exact tcCommit_kept
  case tcLd => exact tcLd_kept
  case tcSt => exact tcSt_kept
  case tcAlloc | tcDealloc | tcRelinquish | tcMma | tcFenceBefore | tcFenceAfter |
      tcWaitLd | tcWaitSt | tcCp | tcShift => exact tc_kept
  case int i =>
    split
    · exact localSreg_kept (hsreg (.inl ⟨i, rfl⟩))
    · exact True.intro
  case move m =>
    split
    · exact localSreg_kept (hsreg (.inr (.inl ⟨m, rfl⟩)))
    · exact True.intro
  case cvt c =>
    split
    · exact localSreg_kept (hsreg (.inr (.inr ⟨c, rfl⟩)))
    · exact True.intro
  all_goals exact True.intro

/-- **An event step writes only the instruction's destination registers** (`eventWrites`): a
register outside them has the same value after the event as before, when the local rule that a
read of changing special registers runs keeps that frame. -/
theorem estep_regsKept {K : Kernel} {e : Event} {u : TState} {ins : Instr}
    (he : EStep K A L g t e (some u)) (hc : K.code[t.pc]? = some ins)
    (hsreg : ((∃ i, ins.op = .int i) ∨ (∃ m, ins.op = .move m) ∨ ∃ c, ins.op = .cvt c) →
      ∀ vs u, execLocalA A L g t (ins.op.withSregValues vs) = .ok u →
        RegsKept (eventWrites ins.op) t u) :
    RegsKept (eventWrites ins.op) t u := by
  obtain ⟨ins', hc', -, hfire⟩ := estep_event_source he
  rw [hc] at hc'
  cases hc'
  exact callbackFrame_fires (eventTmpl_regsKept hsreg) hfire

/-- A local step of the instruction at `t.pc` writes only the registers its local rule writes: a
false guard skips it and keeps every register. -/
theorem tau_regsKept {K : Kernel} {u : TState} {ins : Instr} {W : List Nat}
    (ht : Tau K A L g t u) (hc : K.code[t.pc]? = some ins)
    (hloc : ∀ u, execLocalA A L g t ins.op = .ok u → RegsKept W t u) : RegsKept W t u := by
  unfold Tau out at ht
  cases hf : t.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf, hc] at ht
    cases hg : guardHolds t ins.guard with
    | error f => simp [hg] at ht
    | ok b =>
      cases b with
      | false =>
        simp only [hg, Out.tau.injEq] at ht
        subst ht
        intro r hr; rfl
      | true =>
        simp only [hg] at ht
        split at ht
        · split at ht
          · rename_i t1 hex
            simp only [Out.tau.injEq] at ht
            subst ht
            exact hloc _ hex
          · cases ht
        · cases ht

end

end PTX.EventFrame
