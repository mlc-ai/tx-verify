-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Fire
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.SpinsAtLoop
public import Lemmas.Flow.WarpUniform
public import Lemmas.Flow.ElectActor
public import Lemmas.Order.WaitOrderObject

@[expose] public section

/-! # A kernel's polls: spin loops, no release writes, warp-uniform and ordered polls

A proof tool for the static and per-site poll facts of a kernel.

* **Wait loops.** `waitLoop code pc` checks that a poll at `pc` heads the loop
  `L: mbarrier.try_wait p, [b], par; @p bra DONE; bra L;` with `p` neither the address nor the
  parity register. The branches may or may not be `.uni` (FA4's PV waits use plain `bra`). A
  kernel whose every position passes (`Kernel.waitLoopsOk`, one `decide +kernel` on the code)
  spins at every position (`SpinsAt.of_waitLoops`).
* **No release writes.** `releaseOp` lists the instructions whose events may write with release
  semantics: the release stores. A write fired by any other instruction does not release
  (`fires_write_release`); a kernel without them, followed by sound site machines, has no
  releasing write event (`Frame.write_no_release`).
* **Warp-uniform polls.** A kernel whose polls are at per-site objects (`At g pc m`) that depend
  on the thread only through its warp polls one object per position in a warp
  (`PollObjUniform.of_at`).
* **Ordered polls.** Two threads of a warp that both lead an election with one mask are one
  thread (`Leads.eq`). So when every pair of distinct lanes of a warp polling one object at one
  position whose next position no assumption selects with `uniPoll` either both lead an election
  of one mask or are ordered, the polls are ordered (`PollOrdered.of_cases`): the leading case is
  vacuous. -/

namespace PTX

open PTX.Flow PTX.Proof

noncomputable section

/-! ## Wait loops -/

/-- The instruction at `pc`, if a poll, heads a spinning wait loop `L: mbarrier.try_wait p, [b],
par; @!p bra DONE; bra L;` that leaves the loop; `p` is neither the address nor the parity
register. -/
def waitLoop (code : List Instr) (pc : Nat) : Bool :=
  match code[pc]? with
  | some ⟨none, .mbarWait p b _ par _ _⟩ =>
    (match code[pc + 1]? with
      | some ⟨some (p', false), .bra ex _⟩ => p' == p && (ex < pc || pc + 2 < ex)
      | _ => false) &&
    (match code[pc + 2]? with
      | some ⟨none, .bra l _⟩ => l == pc
      | _ => false) &&
    b != p && par != .reg p
  | some ⟨some _, .mbarWait ..⟩ => false
  | _ => true

/-- Every poll of the kernel heads a wait loop, and no branch of the kernel enters the loop after
its poll. -/
def Kernel.waitLoopsOk (K : Kernel) : Bool :=
  (List.range K.code.length).all fun pc =>
    waitLoop K.code pc && !K.targeted (pc + 1) && !K.targeted (pc + 2)

/-- The wait loop at a poll: the poll's `@!p bra` exits the loop at `ex`, a plain branch closes
it, and `p` is neither the address nor the parity register. -/
theorem waitLoop_facts {K : Kernel} {pc p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hw : waitLoop K.code pc = true)
    (hc : K.code[pc]? = some { op := .mbarWait p base off par acq sc }) :
    ∃ ex uni l' uni2, K.code[pc + 1]? = some { guard := some (p, false), op := .bra ex uni } ∧
      K.code[pc + 2]? = some { guard := none, op := .bra l' uni2 } ∧ l' = pc ∧
      (ex < pc ∨ pc + 2 < ex) ∧ base ≠ p ∧ par ≠ .reg p := by
  unfold waitLoop at hw
  rw [hc] at hw
  dsimp only at hw
  split at hw
  · rename_i p' ex uni heq1
    split at hw
    · rename_i l' uni2 heq2
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hw
      obtain ⟨⟨⟨⟨hpe, hex⟩, hle⟩, hb⟩, hpar⟩ := hw
      have hpe : p' = p := beq_iff_eq.mp hpe
      have hle : l' = pc := beq_iff_eq.mp hle
      subst hpe
      exact ⟨ex, uni, l', uni2, heq1, heq2, hle, hex, hb, hpar⟩
    · simp at hw
  · simp at hw

/-- **The poll that heads a wait loop heads a canonical spin shape**, exiting to the loop's exit. -/
theorem spinExit?_of_waitLoop {K : Kernel} {pc p base : Nat} {off : Int} {par : Opnd}
    {acq : Bool} {sc : MbarScope} (hw : waitLoop K.code pc = true)
    (hc : K.code[pc]? = some { op := .mbarWait p base off par acq sc })
    (htg1 : K.targeted (pc + 1) = false) (htg2 : K.targeted (pc + 2) = false) :
    ∃ exit, K.spinExit? pc = some exit := by
  obtain ⟨ex, uni, l', uni2, h1, h2, hl, hex, hb, hpar⟩ := waitLoop_facts hw hc
  refine ⟨ex, ?_⟩
  unfold Kernel.spinExit?
  rw [Kernel.pollDst_of_code hc hb hpar, h1, h2]
  simp [hl, hex, htg1, htg2]

/-- **A poll that heads a wait loop heads a canonical spin**, exiting to the loop's exit, once its
predicate is read nowhere but in the loop's branch (`Kernel.SpinPred`). -/
theorem canonicalSpin_of_waitLoop {K : Kernel} {pc p base : Nat} {off : Int} {par : Opnd}
    {acq : Bool} {sc : MbarScope} (hw : waitLoop K.code pc = true)
    (hc : K.code[pc]? = some { op := .mbarWait p base off par acq sc })
    (htg1 : K.targeted (pc + 1) = false) (htg2 : K.targeted (pc + 2) = false)
    (hpred : K.SpinPred p) : ∃ exit, K.CanonicalSpin pc exit := by
  obtain ⟨ex, hex⟩ := spinExit?_of_waitLoop hw hc htg1 htg2
  obtain ⟨-, -, -, -, -, -, -, -, hb, hpar⟩ := waitLoop_facts hw hc
  exact ⟨ex, hex, p, Kernel.pollDst_of_code hc hb hpar, hpred⟩

/-- **Every poll of a kernel whose polls head wait loops is a canonical spin**, when each poll's
predicate is read nowhere but in its loop's branch. -/
theorem canonicalSpin_of_waitLoops {K : Kernel} (hK : K.waitLoopsOk = true)
    (hpred : ∀ pc p, K.pollReg pc = some p → K.SpinPred p)
    {pc p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[pc]? = some { op := .mbarWait p base off par acq sc }) :
    ∃ exit, K.CanonicalSpin pc exit := by
  have hlt := (List.getElem?_eq_some_iff.mp hc).1
  have hw := List.all_eq_true.mp hK pc (List.mem_range.mpr hlt)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨hw, ht1⟩, ht2⟩ := hw
  refine canonicalSpin_of_waitLoop hw hc ht1 ht2 ?_
  have hp : K.pollReg pc = some p := by simp only [Kernel.pollReg, hc]
  exact hpred pc p hp

/-! ## Release writes -/

/-- Instructions whose events may write with release semantics: release stores. Every other
instruction either writes nothing (`writeOp`, `eventTmpl_notWrite`) or writes without release. -/
def releaseOp : Op → Bool
  | .mem a => match a.kind, a.sem with
    | .store, .release | .store, .acqRel => true
    | _, _ => false
  | _ => false

/-- `st.bulk` writes without release. -/
theorem bulkInitTmpl_noRelease {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {acc : Acc}
    {bs : List Byte} {u : TState} (h : bulkInitTmpl L g t a = .write acc bs u) :
    acc.release = false := by
  unfold bulkInitTmpl at h
  dsimp only at h
  split at h
  · cases h
  · rename_i loc n hloc
    simp only [Tmpl.write.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    rfl

/-- A load is no write. -/
theorem loadTmpl_notWrite {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {sp : Space}
    {nc : Bool} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {acc : Acc}
    {bs : List Byte} {u : TState} :
    loadTmpl A L g t sp nc w ds base off = .write acc bs u → False := by
  simp only [loadTmpl]
  intro h
  repeat' first | split at h | cases h

/-- An acquire load is no write. -/
theorem acquireLoadTmpl_notWrite {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sc : MbarScope} {sp : Space} {w d base : Nat} {off : Int} {acc : Acc} {bs : List Byte}
    {u : TState} :
    acquireLoadTmpl A L g t sc sp w d base off = .write acc bs u → False := by
  intro h
  generalize h' : loadTmpl A L g t sp false w [d] base off = m at h
  cases m <;> simp_all only [acquireLoadTmpl] <;> first
    | exact loadTmpl_notWrite h'
    | cases h

/-- A weak store writes without release. -/
theorem storeTmpl_noRelease {L : Launch} {g : Nat} {t : TState} {sp : Space} {w base : Nat}
    {off : Int} {srcs : List Opnd} {acc : Acc} {bs : List Byte} {u : TState}
    (h : storeTmpl L g t sp w base off srcs = .write acc bs u) : acc.release = false := by
  rcases Flow.storeTmpl_opEv (L := L) (g := g) (t := t) (sp := sp) (w := w) (base := base)
    (off := off) (srcs := srcs) with ⟨f, h'⟩ | ⟨r, bs', u', h', hr⟩ <;> rw [h'] at h <;> cases h
  exact hr

/-- The write of an access that `accessLoc` locates releases only for a `.release` or `.acq_rel`
store. -/
theorem accessTmpl_write_release {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {acc : Acc} {bs : List Byte} {u : TState}
    (h : accessTmpl A L g t a = .write acc bs u) (hr : acc.release = true) :
    a.kind = .store ∧ (a.sem = .release ∨ a.sem = .acqRel) := by
  unfold accessTmpl at h
  split at h
  · -- `st.bulk`
    have h1 := bulkInitTmpl_noRelease h
    rw [h1] at hr
    cases hr
  · -- a load reads
    repeat' first | split at h | cases h
  · -- a store writes the footprint of `accessAcc`
    rename_i hk
    refine ⟨hk, ?_⟩
    split at h
    · cases h
    · rename_i acc0 hacc
      split at h
      · cases h
      · dsimp only at h
        split at h
        · cases h
        · rename_i v hv
          simp only [Tmpl.write.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          obtain ⟨acc1, he, -, hrel, -⟩ := accessAcc_semAcc hacc
          rw [← he] at hr
          exact (MemAccess.semAcc_release a acc1 hrel).mp hr
  · cases h

/-- A write of an access located by `accessLoc` releases only if the instruction is a store.
`releaseOp` says it is none. -/
theorem accessTmpl_noRelease {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {acc : Acc} {bs : List Byte} {u : TState}
    (h : accessTmpl A L g t a = .write acc bs u) (hop : releaseOp (.mem a) = false) :
    acc.release = false := by
  cases hr : acc.release
  · rfl
  · obtain ⟨hk, hs⟩ := accessTmpl_write_release h hr
    rcases hs with hs | hs <;> simp [releaseOp, hk, hs] at hop

/-- A `stmatrix` writes without release. -/
theorem matrixTmpl_noRelease {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr} {acc : Acc}
    {bs : List Byte} {u : TState} (h : matrixTmpl L g t i = .write acc bs u) :
    acc.release = false := by
  unfold matrixTmpl at h
  repeat' first
    | dsimp only at h
    | unfold matrixMoveTmpl at h
    | split at h
    | (simp only [Tmpl.write.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl)
    | cases h

/-- A write fired by an instruction outside `releaseOp` has no release semantics. -/
theorem fires_write_release {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hop : releaseOp op = false) {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) :
    a.release = false := by
  rcases Flow.fires_write_tmpl (show Fires pc (eventTmpl A L g t op) ⟨e.pc, .wr a bs⟩ o by
      obtain ⟨epc, ek⟩ := e; simp only at hk; subst hk; exact hf) with ⟨t', hw⟩ | ⟨u, -, ha⟩
  swap; · rw [ha]
  by_cases hwop : writeOp op = true
  swap
  · -- an instruction that writes nothing
    have hnw := eventTmpl_notWrite (A := A) (L := L) (g := g) (t := t) (op := op)
      (by simpa using hwop)
    rw [hw] at hnw
    exact hnw.elim
  cases op <;> simp only [releaseOp, writeOp, Bool.false_eq_true] at hop hwop
  case mem ma =>
    simp only [eventTmpl, memTmpl] at hw
    split at hw
    · -- an access whose location the instruction fixes
      split at hw
      · exact (acquireLoadTmpl_notWrite hw).elim
      · exact (loadTmpl_notWrite hw).elim
      · -- a release store is in `releaseOp`
        exfalso
        have h1 : ma.kind = MemKind.store := by assumption
        have h2 : ma.sem = Sem.release := by assumption
        simp [h1, h2] at hop
      · exact storeTmpl_noRelease hw
      · exact accessTmpl_noRelease hw hop
    · -- an atomic rule read-modify-writes, it never writes
      unfold atomTmpl at hw
      repeat' first | dsimp only at hw | split at hw | cases hw
    · -- a dynamic access writes with the access's memory semantics
      split at hw
      · exact accessTmpl_noRelease hw hop
      · cases hw
  case matrix i => exact matrixTmpl_noRelease hw
  case tcAlloc group base off nc =>
    simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hw
    repeat' (first | split at hw | (simp [ofExec] at hw))

/-- **No write event of a kernel without `releaseOp` instructions releases**, when sound site
machines follow its threads. -/
theorem Frame.write_no_release {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
    {X : Execution} {C : (g : Nat) → Flow.Code K A L g} (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (ht : Frame.Tracked C X)
    (hK : K.code.all (fun ins => !releaseOp ins.op) = true)
    {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get e = some ⟨pc, .wr a bs⟩) :
    a.release = false := by
  obtain ⟨g, k⟩ := e
  rcases Frame.fired hC hX he with ⟨σ, -, hσ, -⟩ | ⟨-, hub⟩
  · cases σ with
    | none => exact absurd hσ (ht g k (Frame.lt_of_get hX he))
    | some d =>
      obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site hC hX he hσ
      have hop := List.all_eq_true.mp hK ins (List.mem_of_getElem? hc)
      simp only [Bool.not_eq_true'] at hop
      exact fires_write_release hfire hop rfl
  · obtain ⟨pc', f, hf⟩ := hub
    cases hf

/-! ## Warp-uniform and ordered polls -/

section Polls
variable {L : Launch} {X : Execution}

/-- **Polls at per-site objects that depend on the thread only through its warp are
warp-uniform.** `At g pc m`: thread `g` may poll object `m` at position `pc`. -/
theorem PollObjUniform.of_at (At : Nat → Nat → Loc → Prop)
    (hat : ∀ {g k pc m p ok acq sc}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ → At g pc m)
    (huniq : ∀ {g h pc m m'}, SameWarp L g h → At g pc m → At h pc m' → m = m') :
    PollObjUniform L X :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hw he he' => huniq hw (hat hg he) (hat hh he')

/-- Thread `g` went on as the leader of an election with mask `mask`. -/
def Leads (L : Launch) (X : Execution) (mask g : Nat) : Prop :=
  ∃ j pc inst, X.Elect (g, j) pc mask inst (laneOf L g)

/-- **Two threads of a warp that lead elections with one mask are one thread.** -/
theorem Leads.eq (hok : ElectOk L X) {mask g h : Nat} (hw : SameWarp L g h)
    (hg : Leads L X mask g) (hh : Leads L X mask h) : g = h := by
  obtain ⟨j, pc, inst, he⟩ := hg
  obtain ⟨j', pc', inst', he'⟩ := hh
  exact selected_elect_thread_unique hok he he' hw rfl rfl

/-- **Polls are ordered** when every two distinct lanes of a warp polling one object at one
position whose next position no assumption selects with `uniPoll` either both lead an election of
one mask, which cannot be, or are ordered. -/
theorem PollOrdered.of_cases {K : Kernel} {A : List Assumption} (hok : ElectOk L X)
    (h : ∀ g h k k' pc m p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads → g ≠ h →
      SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      X.get (h, k') = some ⟨pc, .wait m p' ok' acq' sc'⟩ → A.any (·.uniPoll (pc + 1)) = false →
      (∃ mask, Leads L X mask g ∧ Leads L X mask h) ∨
        (∃ a, k < a ∧ DepBefore L K X (g, a) (h, k')) ∨ (∃ a, k' < a ∧ DepBefore L K X (h, a)
            (g, k)) ) :
    PollOrdered L K A X := by
  intro g h' k k' pc m p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hp
  rcases h g h' k k' pc m p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hp with
    ⟨mask, hl, hl'⟩ | hord
  · exact (hgh (Leads.eq hok hw hl hl')).elim
  · exact hord

end Polls

end
end PTX
