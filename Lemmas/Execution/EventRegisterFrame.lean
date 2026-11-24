-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.EventCont

@[expose] public section

/-! # Register preservation by returning memory and synchronization events -/

namespace PTX.EventFrame

open PTX PTX.Proof PTX.Flow

/-- Whether the returning instruction's destination registers are known to omit `r`. -/
def preservesReg (r : Nat) : Op → Bool
  | .mem a => decide (r ∉ a.regs ∧ r ∉ a.dsts.filterMap id)
  | .warp w => match w.kind, w.dsts with
    | .vote .., [some d] => r != d
    | .elect, [d, some p] => decide (r ∉ d.toList ∧ r ≠ p)
    | _, _ => false
  | .mbarWait d .. => r != d
  | .mbarArrive _ _ _ _ _ _ _ dst => decide (r ∉ dst.toList)
  | .tcLd ds _ _ red => decide (r ∉ ds ∧ r ∉ (red.map (·.dst)).toList)
  | .barSync .. | .barSyncN .. | .barArrive .. | .fence .. | .fenceMbarInit
  | .tcFenceBefore | .tcFenceAfter | .tcWaitLd | .tcWaitSt | .tcSt .. | .setMaxReg ..
  | .cpTensorStore .. | .tcDealloc .. | .bulkCommit | .bulkWait .. | .ret | .exit => true
  | .int _ | .move _ | .cvt _ => false
  | _ => false

private theorem load_preserves {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sp : Space} {nc : Bool} {w base r : Nat} {ds : List Nat} {off : Int} (hr : r ∉ ds) :
    CallbackFrame (fun u => u.regs r = t.regs r) (loadTmpl A L g t sp nc w ds base off) := by
  unfold loadTmpl
  split
  · trivial
  · split
    · split <;> try trivial
      intro bs
      unfold afterLoad
      repeat' split
      all_goals first | rfl | exact setRegs_other _ _ _ _ hr
    · intro bs
      unfold afterLoad
      repeat' split
      all_goals first | rfl | exact setRegs_other _ _ _ _ hr

private theorem store_preserves {L : Launch} {g : Nat} {t : TState}
    {sp : Space} {w base r : Nat} {ss : List Opnd} {off : Int} :
    CallbackFrame (fun u => u.regs r = t.regs r) (storeTmpl L g t sp w base off ss) := by
  unfold storeTmpl
  repeat' split
  all_goals first | trivial | (unfold afterStore; split <;> rfl)

private theorem access_preserves {A : List Assumption} {L : Launch} {g r : Nat}
    {t : TState} {a : MemAccess} (hr : r ∉ a.regs) :
    CallbackFrame (fun u => u.regs r = t.regs r) (accessTmpl A L g t a) := by
  have hLoad (bs : List (Option Byte)) :
      (afterAccessLoad t a.ext a.elem.width a.regs bs).regs r = t.regs r := by
    unfold afterAccessLoad
    repeat' split
    all_goals first | rfl | exact setRegs_other _ _ _ _ hr
  unfold accessTmpl bulkInitTmpl
  dsimp only
  repeat' split
  all_goals first | exact hLoad | trivial | (unfold afterStore; split <;> rfl)

private theorem atom_preserves {A : List Assumption} {L : Launch} {g r : Nat}
    {t : TState} {a : MemAccess} (hr : r ∉ a.dsts.filterMap id) :
    CallbackFrame (fun u => u.regs r = t.regs r) (atomTmpl A L g t a) := by
  have hAtom (k n : Nat) (bs : List (Option Byte)) :
      (afterAtom t a.dsts k n bs).regs r = t.regs r := by
    unfold afterAtom
    dsimp only
    repeat' split
    all_goals first | rfl | exact setRegs_other _ _ _ _ hr
  unfold atomTmpl
  dsimp only
  repeat' split
  all_goals first | trivial | exact fun bs => ⟨hAtom _ _ bs, fun _ => hAtom _ _ bs⟩

private theorem acquire_preserves {A : List Assumption} {L : Launch} {g r d w base : Nat}
    {t : TState} {scope : MbarScope} {sp : Space} {off : Int} (hr : r ∉ [d]) :
    CallbackFrame (fun u => u.regs r = t.regs r)
      (acquireLoadTmpl A L g t scope sp w d base off) := by
  unfold acquireLoadTmpl
  have h := load_preserves (A := A) (L := L) (g := g) (t := t) (w := w) (sp := sp)
    (base := base) (off := off) (nc := false) hr
  generalize loadTmpl A L g t sp false w [d] base off = m at h ⊢
  cases m <;> exact h

private theorem release_preserves {L : Launch} {g r w base : Nat}
    {t : TState} {scope : MbarScope} {sp : Space} {off : Int} {v : Opnd} :
    CallbackFrame (fun u => u.regs r = t.regs r)
      (releaseStoreTmpl L g t scope sp w base off v) := by
  unfold releaseStoreTmpl
  have h := store_preserves (L := L) (g := g) (t := t) (r := r) (ss := [v])
    (w := w) (sp := sp) (base := base) (off := off)
  generalize storeTmpl L g t sp w base off [v] = m at h ⊢
  cases m <;> exact h

private theorem mem_preserves {A : List Assumption} {L : Launch} {g r : Nat}
    {t : TState} {a : MemAccess} (hr : r ∉ a.regs) (hd : r ∉ a.dsts.filterMap id) :
    CallbackFrame (fun u => u.regs r = t.regs r) (memTmpl A L g t a) := by
  unfold memTmpl
  split
  · split
    · rename_i _ _ _ _ ha
      rw [ha] at hr
      exact acquire_preserves hr
    · exact load_preserves hr
    · exact release_preserves
    · exact store_preserves
    · exact access_preserves hr
  · exact atom_preserves hd
  · split
    · exact access_preserves hr
    · trivial

private theorem widen_preserves {A : List Assumption} {pc r : Nat} {t : TState} {m : Tmpl}
    (h : CallbackFrame (fun u => u.regs r = t.regs r) m) :
    CallbackFrame (fun u => u.regs r = t.regs r) (widenMbarScope A pc m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope =>
      cases release <;> cases scope <;> exact h
    case wait m parity k acquire scope =>
      cases acquire <;> cases scope <;> exact h
  · exact h

private theorem ldResult_preserves {t : TState} {ds : List Nat} {red : Option TcLdRed}
    {r : Nat} (hr : r ∉ ds) (hd : r ∉ (red.map (·.dst)).toList) (vs : List Value) :
    (ldResult t ds red vs).regs r = t.regs r := by
  cases red with
  | none => exact setRegs_other _ _ _ _ hr
  | some red =>
    have hn : r ≠ red.dst := by simpa using hd
    cases h : red.reduce vs <;> simp only [ldResult, h]
    · exact setRegs_other _ _ _ _ hr
    · change Function.update (setRegs t ds vs).regs red.dst _ r = t.regs r
      rw [Function.update_of_ne hn]
      exact setRegs_other _ _ _ _ hr

private theorem tcLd_preserves {A : List Assumption} {L : Launch} {g r addr : Nat}
    {t : TState} {ds : List Nat} {shape : TcShape} {red : Option TcLdRed}
    (hr : r ∉ ds) (hd : r ∉ (red.map (·.dst)).toList) :
    CallbackFrame (fun u => u.regs r = t.regs r) (tcLdTmpl A L g t (.tcLd ds addr shape red)) := by
  have h : CallbackFrame (fun u => u.regs r = t.regs r)
      (tcTmpl L g t (.tcLd ds addr shape red)) := by
    cases shape <;> simp only [tcTmpl] <;> apply ofExec_frame <;>
      repeat' first
      | (apply allOk_bind; intro _)
      | (intro vs; exact ldResult_preserves hr hd _)
      | split
  unfold tcLdTmpl
  split
  · split
    · generalize tcTmpl L g t (.tcLd ds addr shape red) = m at h ⊢
      cases m <;> exact h
    · rfl
  · exact h

private theorem warp_preserves {L : Launch} {g r : Nat} {t : TState} {w : WarpInstr}
    (h : preservesReg r (.warp w) = true) :
    CallbackFrame (fun u => u.regs r = t.regs r) (warpTmpl L g t w) := by
  cases w with
  | mk kind ty dsts srcs mask =>
    cases kind <;> simp only [preservesReg] at h
    all_goals try contradiction
    case vote mode neg =>
      cases dsts with
      | nil => cases h
      | cons dst rest =>
        cases rest with
        | cons => cases dst <;> cases h
        | nil =>
          cases dst with
          | none => cases h
          | some d =>
            have hn : r ≠ d := by simpa [bne_iff_ne] using h
            unfold warpTmpl
            split
            all_goals try trivial
            all_goals simp_all only [List.cons.injEq, Option.some.injEq, and_true]
            all_goals
              first | unfold voteTmpl | unfold voteModeTmpl
              repeat' split
              all_goals first | trivial | (intro v; exact Function.update_of_ne hn _ _)

    case elect =>
      cases dsts with
      | nil => cases h
      | cons d tail =>
        cases tail with
        | nil => cases d <;> cases h
        | cons p rest =>
          cases rest with
          | cons => cases p <;> cases h
          | nil =>
            cases p with
            | none => cases h
            | some p =>
              have hn : r ∉ d.toList ∧ r ≠ p := of_decide_eq_true h
              unfold warpTmpl
              split <;> try trivial
              all_goals simp_all only [List.cons.injEq, Option.some.injEq, and_true]
              all_goals
                unfold electTmpl
                repeat' split
                all_goals first
                  | trivial
                  | (intro leader
                     simp_all [next, setReg, Function.update_of_ne])


/-- A supported instruction preserves every register outside its destinations in all
possible returning callbacks, including executions that return a pending fault. -/
theorem eventTmpl_preserves_reg {A : List Assumption} {L : Launch} {g r : Nat}
    {t : TState} {op : Op} (hr : preservesReg r op = true) :
    CallbackFrame (fun u => u.regs r = t.regs r) (eventTmpl A L g t op) := by
  cases op <;> simp only [preservesReg, decide_eq_true_eq, bne_iff_ne, eventTmpl] at hr ⊢
  all_goals try contradiction
  case mem => exact mem_preserves hr.1 hr.2
  case warp => exact warp_preserves hr
  case mbarWait d base off parity acq scope =>
    apply widen_preserves
    simp only [tmaTmpl]
    apply ofExec_frame
    apply allOk_bind
    intro _
    apply allOk_bind
    intro _ ok
    exact Function.update_of_ne hr _ _
  case mbarArrive base off tx n remote release scope dst =>
    apply widen_preserves
    simp only [tmaTmpl]
    apply ofExec_frame
    cases remote <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      repeat' (apply allOk_bind; intro _)
    all_goals
      cases dst with
      | none => rfl
      | some d =>
        have hn : r ≠ d := by simpa using hr
        exact Function.update_of_ne hn _ _
  case tcLd => exact tcLd_preserves hr.1 hr.2
  case barSync | barSyncN | barArrive =>
    unfold barTmpl
    repeat' split
    all_goals trivial
  case fence =>
    simp only [fenceTmpl]
    repeat' split
    all_goals trivial
  case fenceMbarInit => exact widen_preserves rfl
  case setMaxReg =>
    unfold SetMaxNReg.tmpl
    split <;> trivial
  case tcWaitLd | tcWaitSt =>
    simp only [tcTmpl]
    apply ofExec_frame
    split <;> trivial
  case tcSt addr srcs shape =>
    have core (u : TState) (hu : u.regs = t.regs) :
        CallbackFrame (fun v => v.regs r = t.regs r) (tcTmpl L g u (.tcSt addr srcs shape)) := by
      cases shape <;> simp only [tcTmpl] <;> apply ofExec_frame <;>
        repeat' first
        | exact True.intro
        | (apply allOk_bind; intro _)
        | split
        | exact hu ▸ rfl
    unfold tcStTmpl
    split
    · split
      · split
        · rfl
        · trivial
      · exact core _ rfl
    · exact core _ rfl
  case cpTensorStore =>
    simp only [tensorStoreTmpl]
    apply ofExec_frame
    apply allOk_bind
    intro pair
    cases pair
    rfl
  case tcDealloc =>
    simp only [tcTmpl]
    apply ofExec_frame
    repeat' first
    | exact True.intro
    | (apply allOk_bind; intro _)
    | split
    | rfl
  case bulkCommit | bulkWait =>
    simp [tensorStoreTmpl, CallbackFrame, next]
  all_goals trivial

end PTX.EventFrame
