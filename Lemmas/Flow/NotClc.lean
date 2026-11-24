-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # Instructions that fire no event of a kind

A proof tool. An instruction other than `clusterlaunchcontrol.try_cancel` fires no
cancellation request, so it leaves every count of requests unchanged. -/

namespace PTX.Flow

/-- A template that issues no cancellation request. -/
def NotClc : Tmpl → Prop
  | .clcIssue .. => False
  | _ => True

/-- Whether an instruction is a cancellation request. -/
def clcOp : Op → Bool
  | .clcTryCancel .. => true
  | _ => false

theorem widen_notClc {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotClc m) :
    NotClc (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notClc {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotClc r) :
    NotClc (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction that is not a cancellation request fires none. -/
theorem eventTmpl_notClc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : clcOp op = false) : NotClc (eventTmpl A L g t op) := by
  cases op <;> simp only [clcOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notClc
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notClc)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notClc)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- An event of an instruction that is not a cancellation request is no request on any
barrier. -/
theorem clcIssuesTo_of_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} {m : Loc} (hop : clcOp op = false)
    (hf : Fires pc (eventTmpl A L g t op) e o) : clcIssuesTo m e = false := by
  have hm := eventTmpl_notClc (A := A) (L := L) (g := g) (t := t) hop
  obtain ⟨epc, ek⟩ := e
  cases ek <;> simp only [clcIssuesTo]
  rename_i sp tg
  exfalso
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotClc] at hm <;>
    simp only [Fires] at hf <;> aesop

/-- A multicast cancellation request targets the CTAs of the requesting thread's cluster. -/
theorem fires_clcIssue_targets {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst mb : Nat} {doff moff : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.clcTryCancel true dst doff mb moff)) e o) :
    ∀ sp targets, e.kind = .clcIssue sp targets →
      ∀ c ∈ targets, c < L.grid ∧ L.clusterOfCta c = L.clusterOfCta (g / L.block) := by
  intro sp targets hk c hc
  simp only [eventTmpl, clcTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hd : effAddr L g t .shared dst doff with
  | error f =>
    simp only [hd, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok d =>
    cases hm : mbarLoc L g t mb moff with
    | error f =>
      simp only [hd, hm, ofExec, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok m =>
      simp only [hd, hm] at hf
      split at hf
      · simp only [ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk
        simpa using hc
      · simp only [ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk

/-- A cancellation request names the response buffer and the barrier its operands give. -/
theorem fires_clcIssue_spec {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mc : Bool} {dst mb : Nat} {doff moff : Int} {pc : Nat} {e : Event} {o : Option TState}
    {d m : Loc} (hd : effAddr L g t .shared dst doff = .ok d) (hm : mbarLoc L g t mb moff = .ok m)
    (hf : Fires pc (eventTmpl A L g t (.clcTryCancel mc dst doff mb moff)) e o) :
    ∀ sp targets, e.kind = .clcIssue sp targets → sp.response = d ∧ sp.mbar = m := by
  intro sp targets hk
  simp only [eventTmpl, clcTmpl, bind, Except.bind, pure, Except.pure, hd, hm] at hf
  split at hf
  · simp only [ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    exact ⟨rfl, rfl⟩
  · simp only [ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk

/-- A template that queries no response. -/
def NotQuery : Tmpl → Prop
  | .clcQuery .. => False
  | _ => True

/-- Whether an instruction queries a response. -/
def queryOp : Op → Bool
  | .clcQuery .. => true
  | _ => false

theorem widen_notQuery {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotQuery m) :
    NotQuery (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notQuery {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotQuery r) :
    NotQuery (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction that is not a query fires none. -/
theorem eventTmpl_notQuery {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : queryOp op = false) : NotQuery (eventTmpl A L g t op) := by
  cases op <;> simp only [queryOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notQuery
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notQuery)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notQuery)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A query event is fired by a query instruction. -/
theorem fires_query_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {q : ClcQuery} {r : ClcResponse} (hk : e.kind = .clcQuery q r) : queryOp op = true := by
  cases hq : queryOp op
  · exfalso
    have hm := eventTmpl_notQuery (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotQuery] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A query reports the response held in its source register. -/
theorem fires_clcQuery_value {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {q : ClcQuery} {dst src : Nat} {pc : Nat} {e : Event} {o : Option TState}
    {r0 : ClcResponse} (hr : t.regs src = some (.clc r0))
    (hf : Fires pc (eventTmpl A L g t (.clcQuery q dst (.reg src))) e o) :
    ∀ q' r, e.kind = .clcQuery q' r → r = r0 := by
  intro q' r hk
  simp only [eventTmpl, clcTmpl, readValue, readReg, hr, bind, Except.bind, pure,
    Except.pure] at hf
  split at hf
  · simp only [ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  · simp only [ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    rfl

/-- A load without `.nc` fires a read or an undefined behaviour. -/
theorem fires_ldAcquire_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) (hk : a.kind = .load := by rfl)
    (hnc : a.nc = false := by rfl) :
    (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
  have hl : ∀ {sp base ds} {m : Tmpl}, (m = loadTmpl A L g t sp false a.elem.width ds base
      a.addr.off ∨ m = acquireLoadTmpl A L g t (a.scope.getD .cta) sp a.elem.width
      (ds.headD 0) base a.addr.off) → Fires pc m e o →
      (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
    intro sp base ds m hm hf
    rcases hm with rfl | rfl
    all_goals simp only [acquireLoadTmpl, loadTmpl, Bool.false_eq_true, ↓reduceIte] at hf
    all_goals repeat' split at hf
    all_goals (try simp only [Fires] at hf)
    all_goals first
      | exact .inr ⟨_, by rw [hf.1]⟩
      | (obtain ⟨bs, -, he, -⟩ := hf; exact .inl ⟨_, bs, by rw [he]⟩)
  have hacc : Fires pc (accessTmpl A L g t a) e o →
      (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
    intro hf
    rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
      ⟨r, k, hn, -⟩
    · rw [h] at hf
      simp only [Fires] at hf
      exact .inr ⟨_, by rw [hf.1]⟩
    · rw [h] at hf
      obtain ⟨bs, -, he, -⟩ := hf
      exact .inl ⟨_, bs, by rw [he]⟩
    · simp [hnc] at hn
  simp only [eventTmpl, memTmpl] at hf
  split at hf
  · split at hf
    · exact hl (ds := [_]) (.inr rfl) hf
    · rw [hnc] at hf
      exact hl (.inl rfl) hf
    · simp_all
    · simp_all
    · exact hacc hf
  · -- a load has no read-modify-write operation, so the atomic rule faults
    have ho : a.kind.atomOp? = none := by rw [hk]; rfl
    simp only [atomTmpl, ho, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, by rw [hf.1]⟩
  · split at hf
    · exact hacc hf
    · simp only [Fires] at hf
      exact .inr ⟨_, by rw [hf.1]⟩

/-- A 128-bit acquire load from a shared address reads the 16 bytes there. -/
theorem fires_ldAcquire128 {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {d base bw : Nat} {pc : Nat} {e : Event} {o : Option TState} {loc : Loc}
    (hd : effAddr L g t .shared base 0 = .ok loc) (hsub : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hr : a.rule = some .threadAccess := by rfl) (hs : a.locSpace? = some .shared := by rfl)
    (hb : a.addr.base = .reg base bw := by rfl) (hk : a.kind = .load := by rfl)
    (hsem : a.sem = .acquire := by rfl) (hregs : a.regs = [d] := by rfl)
    (hw : a.elem.width = 128 := by rfl) (hoff : a.addr.off = 0 := by rfl) :
    ∀ a bs, e.kind = .rd a bs → a.loc = loc ∧ a.size = 16 := by
  intro a' bs hk'
  simp only [eventTmpl, memTmpl_acquire hr hs hb hk hsem hregs, hw, hoff] at hf
  simp only [acquireLoadTmpl, loadTmpl, hd, hsub, bind, Except.bind] at hf
  cases helem : elemAcc loc (128 / 8) [d].length 0 with
  | error f =>
    simp only [helem, Fires] at hf
    rw [hf.1] at hk'
    cases hk'
  | ok a'' =>
    simp only [helem, Bool.false_eq_true, ↓reduceIte, Fires] at hf
    obtain ⟨bs', -, he, -⟩ := hf
    rw [he] at hk'
    cases hk'
    unfold elemAcc at helem
    split_ifs at helem
    all_goals cases helem
    all_goals refine ⟨?_, rfl⟩
    all_goals change loc.at (128 / 8 * 0) = loc
    all_goals simp only [Loc.at, Nat.mul_zero, Nat.add_zero]

/-- A template that exits nothing. -/
def NotExit : Tmpl → Prop
  | .exit => False
  | _ => True

theorem widen_notExit {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotExit m) :
    NotExit (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notExit {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotExit r) :
    NotExit (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than `ret` and `exit` exits nothing. -/
theorem eventTmpl_notExit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : op ≠ .ret) (hx : op ≠ .exit) : NotExit (eventTmpl A L g t op) := by
  cases op
  case ret => exact absurd rfl hop
  case exit => exact absurd rfl hx
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notExit
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notExit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notExit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- An exit event is fired by a `ret` or an `exit` instruction. -/
theorem fires_exit_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hk : e.kind = .exit) : op = .ret ∨ op = .exit := by
  by_contra hq
  rw [not_or] at hq
  have hm := eventTmpl_notExit (A := A) (L := L) (g := g) (t := t) hq.1 hq.2
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotExit] at hm <;>
    simp only [Fires] at hf <;> aesop

/-- A template that fires no barrier arrival. -/
def NotBar : Tmpl → Prop
  | .bar .. => False
  | _ => True

theorem widen_notBar {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotBar m) :
    NotBar (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notBar {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBar r) :
    NotBar (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a named barrier. -/
def barOp : Op → Bool
  | .barSync .. | .barSyncN .. | .barArrive .. => true
  | _ => false

/-- An instruction that is not a named barrier fires no arrival. -/
theorem eventTmpl_notBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : barOp op = false) : NotBar (eventTmpl A L g t op) := by
  cases op <;> simp only [barOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBar
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A barrier arrival is fired by a named barrier instruction. -/
theorem fires_bar_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {id : Nat} {c : Option Nat} {m : BarMode} (hk : e.kind = .bar id c m) : barOp op = true := by
  cases hq : barOp op
  · exfalso
    have hm := eventTmpl_notBar (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBar] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A template that fires no bulk commit. -/
def NotBulkCommit : Tmpl → Prop
  | .bulkCommit .. => False
  | _ => True

theorem widen_notBulkCommit {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotBulkCommit m) :
    NotBulkCommit (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notBulkCommit {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBulkCommit r) :
    NotBulkCommit (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a bulk commit. -/
def bulkCommitOp : Op → Bool
  | .bulkCommit => true
  | _ => false

/-- An instruction other than a bulk commit commits nothing. -/
theorem eventTmpl_notBulkCommit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : bulkCommitOp op = false) : NotBulkCommit (eventTmpl A L g t op) := by
  cases op <;> simp only [bulkCommitOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBulkCommit
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkCommit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkCommit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A bulk commit event is fired by a bulk commit instruction. -/
theorem fires_bulkCommit_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hk : e.kind = .bulkCommit) : bulkCommitOp op = true := by
  cases hq : bulkCommitOp op
  · exfalso
    have hm := eventTmpl_notBulkCommit (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBulkCommit] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A template that fires no write. -/
def NotWrite : Tmpl → Prop
  | .write .. | .tcAllocStore .. => False
  | _ => True

theorem widen_notWrite {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotWrite m) :
    NotWrite (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notWrite {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotWrite r) :
    NotWrite (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction stores: a memory instruction other than a load, `stmatrix`, or a
Tensor Memory allocation (which stores the allocated address). -/
def writeOp : Op → Bool
  | .mem a => match a.kind with
    | .load => false
    | _ => true
  | .matrix m => match m.op with
    | .move mv => mv.store
    | _ => false
  | .tcAlloc .. => true
  | _ => false

/-- An instruction that does not store writes nothing. -/
theorem eventTmpl_notWrite {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : writeOp op = false) : NotWrite (eventTmpl A L g t op) := by
  cases op
  case mem a =>
    simp only [writeOp] at hop
    split at hop
    · rename_i hk
      have hacc : NotWrite (accessTmpl A L g t a) := by
        rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
          ⟨r, k, -, h⟩ <;> rw [h] <;> trivial
      simp only [eventTmpl, memTmpl]
      split
      · split
        · simp only [acquireLoadTmpl, loadTmpl]; repeat' first | trivial | split
        · simp only [loadTmpl]; repeat' first | trivial | split
        · simp_all
        · simp_all
        · exact hacc
      · -- a load has no read-modify-write operation, so the atomic rule faults
        have ho : a.kind.atomOp? = none := by rw [hk]; rfl
        simp only [atomTmpl, ho, throw, throwThe, MonadExceptOf.throw]
        trivial
      · split
        · exact hacc
        · trivial
    · contradiction
  case matrix m =>
    simp only [writeOp] at hop
    simp only [eventTmpl, matrixTmpl, matrixMoveTmpl]
    repeat' first
      | trivial
      | split
      | (exfalso; simp_all)
  all_goals simp only [writeOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notWrite
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWrite)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [warpTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWrite)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A write is fired by a store instruction. -/
theorem fires_write_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) : writeOp op = true := by
  cases hq : writeOp op
  · exfalso
    have hm := eventTmpl_notWrite (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotWrite] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A template that fires no tensor store. -/
def NotTensorStore : Tmpl → Prop
  | .tensorStore .. => False
  | _ => True

theorem widen_notTensorStore {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTensorStore m) :
    NotTensorStore (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTensorStore {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTensorStore r) :
    NotTensorStore (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a tensor store. -/
def tensorStoreOp : Op → Bool
  | .cpTensorStore .. => true
  | _ => false

/-- An instruction other than a tensor store issues none. -/
theorem eventTmpl_notTensorStore {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tensorStoreOp op = false) : NotTensorStore (eventTmpl A L g t op) := by
  cases op <;> simp only [tensorStoreOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTensorStore
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTensorStore)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTensorStore)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A tensor store issue is fired by a tensor store instruction. -/
theorem fires_tensorStore_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {sp : TensorStore.Spec} (hk : e.kind = .tensorStore a sp) : tensorStoreOp op = true :=
      by
  cases hq : tensorStoreOp op
  · exfalso
    have hm := eventTmpl_notTensorStore (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTensorStore] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A template that fires no bulk wait. -/
def NotBulkWait : Tmpl → Prop
  | .bulkWait .. => False
  | _ => True

theorem widen_notBulkWait {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotBulkWait m) :
    NotBulkWait (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notBulkWait {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBulkWait r) :
    NotBulkWait (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a bulk wait. -/
def bulkWaitOp : Op → Bool
  | .bulkWait .. => true
  | _ => false

/-- An instruction other than a bulk wait waits for no group. -/
theorem eventTmpl_notBulkWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : bulkWaitOp op = false) : NotBulkWait (eventTmpl A L g t op) := by
  cases op <;> simp only [bulkWaitOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBulkWait
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkWait)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkWait)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A bulk wait is fired by a bulk wait instruction. -/
theorem fires_bulkWait_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : BulkGroup.WaitMode} {r : Nat} (hk : e.kind = .bulkWait m r) : bulkWaitOp op = true := by
  cases hq : bulkWaitOp op
  · exfalso
    have hm := eventTmpl_notBulkWait (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBulkWait] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- A template that fires no cluster barrier event. -/
def NotCluster : Tmpl → Prop
  | .cluster .. => False
  | _ => True

theorem widen_notCluster {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotCluster m) :
    NotCluster (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notCluster {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotCluster r) :
    NotCluster (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a cluster barrier operation. -/
def clusterOp : Op → Bool
  | .cluster .. => true
  | _ => false

/-- An instruction other than a cluster barrier operation fires no cluster barrier event. -/
theorem eventTmpl_notCluster {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : clusterOp op = false) : NotCluster (eventTmpl A L g t op) := by
  cases op <;> simp only [clusterOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notCluster
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notCluster)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notCluster)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A cluster barrier event is fired by that cluster barrier operation. -/
theorem fires_cluster_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {cop : ClusterOp} (hk : e.kind = .cluster cop) : op = .cluster cop := by
  cases hq : clusterOp op
  · exfalso
    have hm := eventTmpl_notCluster (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotCluster] at hm <;>
      simp only [Fires] at hf <;> aesop
  · cases op <;> simp only [clusterOp, Bool.false_eq_true] at hq
    rename_i cop'
    simp only [eventTmpl, Fires] at hf
    rw [hf.1] at hk
    cases hk
    rfl

end PTX.Flow
