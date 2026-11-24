-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Resource
public import Lemmas.Execution.EventFrameBase

@[expose] public section

/-! # The event an instruction fires

A proof tool. The template of an event instruction is its undefined behaviour or an event of the
instruction's own class (`OpTmpl`, `eventTmpl_opTmpl`): a return exits, a fence fences, an
mbarrier instruction makes its object operation, a load reads (with acquire semantics only for
`ld.acquire`), a store writes without release semantics, a `tcgen05` instruction makes its
Tensor Core operation, a copy instruction issues its copy. The allocation `tcgen05.alloc` fires
its request at its first sub-step and the store of its address after it. A thread's next event
is then known from the instruction at its site alone. -/

namespace PTX.Flow
open PTX

/-- A cancellation request of thread `g`: its response and mbarrier are in its own CTA's shared
memory, and its targets are its cluster's CTAs (multicast) or its own CTA. -/
def CancelSpec (L : Launch) (g : Nat) (s : Clc.Spec) (ts : List Nat) : Prop :=
  s.response.space = .shared ∧ s.response.cta = g / L.block ∧ s.mbar.space = .shared ∧
    s.mbar.cta = g / L.block ∧
    ts = if s.multicast then
      (List.range L.grid).filter (fun c => L.clusterOfCta c == L.clusterOfCta (g / L.block))
    else [g / L.block]

/-- The events an event instruction of thread `g` fires, apart from undefined behaviour.
Instructions without a class here are unconstrained. -/
def OpEv (L : Launch) (g : Nat) : Op → Tmpl → Prop
  | .ret, m | .exit, m => m = .exit
  | .mem a, m => match a.kind, a.sem, a.nc with
    | .load, .weak, false => ∃ r k, m = .read r k ∧ r.acquire = false
    | .load, .acquire, false => ∃ r k, m = .read r k
    | .store, .weak, _ => ∃ r bs t, m = .write r bs t ∧ r.release = false
    | _, _, _ => True
  | .fence (.proxy k o _), m => ∃ t, m = .fenceProxy k (o.map (·.2)) t
  | .fenceMbarInit, m => ∃ t, m = .fenceMbarInit t
  | .mbarInit .., m => ∃ l c t, m = .mbInit l c t
  | .mbarInval .., m => ∃ l t, m = .mbInval l t
  | .mbarArrive .., m => ∃ l tx t c r s, m = .arrive l tx t c r s
  | .mbarWait .., m => ∃ l p k a s, m = .wait l p k a s
  | .clcQuery .., m => ∃ q r t, m = .clcQuery q r t
  | .clcTryCancel .., m => ∃ s ts t, m = .clcIssue s ts t ∧ CancelSpec L g s ts
  | .bulkCommit, m => ∃ t, m = .bulkCommit t
  | .bulkWait .., m => ∃ md n t, m = .bulkWait md n t
  | .cpTensor .., m => ∃ a s t, m = .tensorIssue a s t
  | .cpTensorStore .., m => ∃ a s t, m = .tensorStore a s t
  | .tcCommit .., m => ∃ s t, m = .tc (.commit s) t
  | .tcMma .., m => ∃ d s acc ms t, m = .tc (.mma d s acc ms) t
  | .tcLd .., m => (∃ a n sh k, m = .tcLd a n sh k) ∨ ∃ t, m = .tc .waitLd t
  | .tcWaitLd, m => ∃ t, m = .tc .waitLd t
  | .tcAlloc .., m =>
    (∃ grp dst n t, m = .tc (.resource grp (some dst) (.alloc n)) t) ∨ ∃ dst t, m =
      .tcAllocStore dst t
  | .tcDealloc .., m | .tcRelinquish .., m =>
    ∃ grp act t, m = .tc (.resource grp none act) t ∧ ∀ n, act ≠ .alloc n
  | .cluster op, m => ∃ t, m = .cluster op t
  | .barSync .., m | .barSyncN .., m => ∃ id t c, m = .bar id t c .sync
  | .barArrive .., m => ∃ id t c, m = .bar id t c .arrive
  | .setMaxReg .., m => ∃ inc n t, m = .setMaxReg inc n t
  | .warp w, m => match w.kind with
    | .barWarp => ∃ mask t, m = .warpBar mask t
    | .elect => ∃ mask k, m = .elect mask k
    | .shfl _ => ∃ md a b c k, m = .shfl md a b c k
    | .vote .ballot _ => ∃ mask a k, m = .vote mask a k
    | _ => True
  | _, _ => True

/-- The template of an event instruction: its undefined behaviour or an event of its class. -/
def OpTmpl (L : Launch) (g : Nat) (op : Op) (m : Tmpl) : Prop := (∃ f, m = .ub f) ∨ OpEv L g op m

/-- An element access has neither acquire nor release semantics. -/
theorem bind_elemAcc {r : Exec Loc} {n c j : Nat} {a : Acc}
    (h : (r >>= fun loc => elemAcc loc n c j) = .ok a) : a.release = false ∧ a.acquire = false := by
  cases r with
  | error f => cases h
  | ok loc =>
    change elemAcc loc n c j = .ok a at h
    unfold elemAcc at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩

theorem ofExec_opTmpl {L : Launch} {g : Nat} {op : Op} {r : Exec Tmpl}
    (h : PTX.EventFrame.AllOk (OpTmpl L g op) r) : OpTmpl L g op (ofExec r) := by
  cases r with
  | error f => exact .inl ⟨f, rfl⟩
  | ok m => exact h

/-- An event of the class of `op` under a changed mbarrier scope stays of that class. -/
theorem opEv_scope {L : Launch} {g : Nat} {op : Op} {m m' : Tmpl}
    (hm : (∃ l tx t c sc sc', m = .arrive l tx t c true sc ∧ m' = .arrive l tx t c true sc') ∨
      ∃ l p k sc sc', m = .wait l p k true sc ∧ m' = .wait l p k true sc')
    (h : OpEv L g op m) : OpEv L g op m' := by
  rcases hm with ⟨l, tx, t, c, sc, sc', rfl, rfl⟩ | ⟨l, p, k, sc, sc', rfl, rfl⟩ <;>
    cases op <;> (try cases ‹Bool›) <;> simp only [OpEv] at h ⊢ <;> (try split at h) <;>
    first
      | trivial
      | exact ⟨_, _, _, _, _, _, rfl⟩
      | exact ⟨_, _, _, _, _, rfl⟩
      | simp at h

theorem widen_opTmpl {A : List Assumption} {L : Launch} {g : Nat} {op : Op} {site : Nat} {m : Tmpl}
    (h : OpTmpl L g op m) : OpTmpl L g op (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · split
    · rcases h with ⟨f, hf⟩ | h
      · cases hf
      · exact .inr (opEv_scope (.inl ⟨_, _, _, _, _, _, rfl, rfl⟩) h)
    · rcases h with ⟨f, hf⟩ | h
      · cases hf
      · exact .inr (opEv_scope (.inr ⟨_, _, _, _, _, rfl, rfl⟩) h)
    · exact h
  · exact h

/-- A `.shared::cluster` address (a non-generic symbolic pointer) is no `.shared::cta` operand. -/
theorem readSharedAddress_cta_ptr {L : Launch} {g : Nat} {t : TState} {r w w' issuer cta : Nat}
    {gen : Bool} {o : BitVec 64} {loc : Loc}
    (hv : readReg t r = .ok (.ptr w gen (.shared issuer cta) o)) :
    readSharedAddress L g t w' false false (.reg r) ≠ .ok loc := by
  intro hr
  unfold readSharedAddress at hr
  have hv' : readValue L g t w' (.reg r) = .ok (.ptr w gen (.shared issuer cta) o) := hv
  simp only [bind, Except.bind, hv', Bool.false_eq_true, or_self, ite_false] at hr
  split_ifs at hr

/-- A thread's own shared memory address is in its own CTA. -/
theorem effAddr_shared {L : Launch} {g : Nat} {t : TState} {base : Nat} {off : Int} {loc : Loc}
    (h : effAddr L g t .shared base off = .ok loc) :
    loc.space = .shared ∧ loc.cta = g / L.block := by
  simp only [effAddr, sharedEffAddr, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · rename_i w gen cta o
      split at h
      · cases h
      · rename_i loc' hr
        exact (readSharedAddress_cta_ptr hv hr).elim
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩

/-- A load without `.nc` is undefined behaviour or a read without acquire semantics. -/
theorem loadTmpl_opEv {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {sp : Space}
    {w : Nat} {ds : List Nat} {base : Nat} {off : Int} :
    (∃ f, loadTmpl A L g t sp false w ds base off = .ub f) ∨
      ∃ r k, loadTmpl A L g t sp false w ds base off = .read r k ∧ r.acquire = false := by
  unfold loadTmpl
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, rfl, (bind_elemAcc ‹_›).2⟩

/-- An acquire load is undefined behaviour or a read. -/
theorem acquireLoadTmpl_opEv {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sc : MbarScope} {sp : Space} {w d base : Nat} {off : Int} :
    (∃ f, acquireLoadTmpl A L g t sc sp w d base off = .ub f) ∨
      ∃ r k, acquireLoadTmpl A L g t sc sp w d base off = .read r k := by
  unfold acquireLoadTmpl
  rcases loadTmpl_opEv (A := A) (L := L) (g := g) (t := t) (sp := sp) (w := w) (ds := [d])
    (base := base) (off := off) with ⟨f, h⟩ | ⟨r, k, h, -⟩ <;> rw [h]
  · exact .inl ⟨f, rfl⟩
  · exact .inr ⟨_, _, rfl⟩

/-- A store is undefined behaviour or a write without release semantics. -/
theorem storeTmpl_opEv {L : Launch} {g : Nat} {t : TState} {sp : Space} {w base : Nat}
    {off : Int} {srcs : List Opnd} :
    (∃ f, storeTmpl L g t sp w base off srcs = .ub f) ∨
      ∃ r bs u, storeTmpl L g t sp w base off srcs = .write r bs u ∧ r.release = false := by
  unfold storeTmpl
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i r hr
    repeat' split
    all_goals first
      | exact .inl ⟨_, rfl⟩
      | exact .inr ⟨_, _, _, rfl, (bind_elemAcc hr).1⟩

/-- Run the template's rule: undefined behaviour or the event closes each branch. -/
local macro "tmpl_steps" closer:tactic : tactic => `(tactic|
  repeat' first
    | (left; exact ⟨_, rfl⟩)
    | (right; $closer; done)
    | (change OpTmpl _ _; right; $closer; done)
    | exact trivial
    | contradiction
    | (apply ofExec_opTmpl)
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split)

/-- A memory instruction with the atomic rule read-modifies-writes one element. -/
theorem rule_atomic_kind {a : MemAccess} (hr : a.rule = some .threadAtomic) :
    (∃ op, a.kind = .rmw op) ∨ ∃ op, a.kind = .reduce op := by
  cases hk : a.kind
  case load =>
    cases hs : a.space
    · simp only [MemAccess.rule, hk, hs] at hr
      split_ifs at hr
      all_goals cases hr
    · cases hv : ‹StateSpace› <;> simp only [MemAccess.rule, hk, hs, hv] at hr
      all_goals (split_ifs at hr; all_goals cases hr)
  case store =>
    simp only [MemAccess.rule, hk] at hr
    split_ifs at hr
    all_goals cases hr
  case bulkInit =>
    simp only [MemAccess.rule, hk] at hr
    split_ifs at hr
    all_goals cases hr
  case rmw op => exact .inl ⟨op, rfl⟩
  case reduce op => exact .inr ⟨op, rfl⟩
  all_goals (simp only [MemAccess.rule, hk] at hr; cases hr)

/-- Every event instruction's template is of its class. -/
theorem eventTmpl_opTmpl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} (op : Op) :
    OpTmpl L g op (eventTmpl A L g t op) := by
  cases op
  case ret => exact .inr rfl
  case exit => exact .inr rfl
  case mem a =>
    simp only [eventTmpl, memTmpl]
    split
    · rename_i sp base w _ _ _
      split
      · rename_i d hk hs _
        rcases acquireLoadTmpl_opEv (A := A) (L := L) (g := g) (t := t) (sc := a.scope.getD .cta)
          (sp := sp) (w := a.elem.width) (d := d) (base := base) (off := a.addr.off) with
          ⟨f, h⟩ | ⟨r, k, h⟩ <;> rw [h]
        · exact .inl ⟨f, rfl⟩
        · right; simp only [OpEv, hk, hs]; split <;> first | trivial | exact ⟨_, _, rfl⟩
      · rename_i hk _
        cases hn : a.nc
        · rcases loadTmpl_opEv (A := A) (L := L) (g := g) (t := t) (sp := sp)
            (w := a.elem.width) (ds := a.regs) (base := base) (off := a.addr.off) with
            ⟨f, h⟩ | ⟨r, k, h, hr⟩ <;> rw [h]
          · exact .inl ⟨f, rfl⟩
          · right; simp only [OpEv, hk, hn]
            split <;> first | trivial | exact ⟨_, _, rfl, hr⟩ | exact ⟨_, _, rfl⟩
        · exact .inr (by simp only [OpEv, hk, hn]; try (split <;> simp_all))
      · rename_i v hk hs _
        exact .inr (by simp only [OpEv, hk, hs])
      · rename_i hk _
        rcases storeTmpl_opEv (L := L) (g := g) (t := t) (sp := sp) (w := a.elem.width)
          (base := base) (off := a.addr.off) (srcs := a.srcs) with
          ⟨f, h⟩ | ⟨r, bs, u, h, hr⟩ <;> rw [h]
        · exact .inl ⟨f, rfl⟩
        · right; simp only [OpEv, hk]
          split <;> first | trivial | exact ⟨_, _, _, rfl, hr⟩
      · -- a st.bulk, a strong store or a store or load of another shape
        cases hk : a.kind
        case load =>
          rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ |
            ⟨r, hn, hrel, h⟩ | ⟨r, k, hn, h⟩ <;> rw [h]
          · exact .inl ⟨f, rfl⟩
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hn, hs]
            all_goals first
              | exact ⟨_, _, rfl⟩
              | (refine ⟨_, _, rfl, ?_⟩; simpa [hs] using hrel)
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hn, hs]
        case store =>
          rcases accessTmpl_store (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ |
            ⟨r, bs, hrel, h⟩ <;> rw [h]
          · exact .inl ⟨f, rfl⟩
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hs]
            all_goals first
              | (refine ⟨_, _, _, rfl, ?_⟩; simpa [hs] using hrel)
        all_goals exact .inr (by simp only [OpEv, hk])
    · -- an atomic read-modify-write
      have hr : a.rule = some .threadAtomic := by assumption
      simp only [atomTmpl]
      split
      · exact .inl ⟨_, rfl⟩
      rcases rule_atomic_kind hr with ⟨op, hk⟩ | ⟨op, hk⟩
      · right; simp only [OpEv, hk]
      · right; simp only [OpEv, hk]
    · -- a located access
      split
      · cases hk : a.kind
        case load =>
          rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ |
            ⟨r, hn, hrel, h⟩ | ⟨r, k, hn, h⟩ <;> rw [h]
          · exact .inl ⟨f, rfl⟩
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hn, hs]
            all_goals first
              | exact ⟨_, _, rfl⟩
              | (refine ⟨_, _, rfl, ?_⟩; simpa [hs] using hrel)
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hn, hs]
        case store =>
          rcases accessTmpl_store (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ |
            ⟨r, bs, hrel, h⟩ <;> rw [h]
          · exact .inl ⟨f, rfl⟩
          · right
            cases hs : a.sem <;> simp only [OpEv, hk, hs]
            all_goals first
              | (refine ⟨_, _, _, rfl, ?_⟩; simpa [hs] using hrel)
        all_goals exact .inr (by simp only [OpEv, hk])
      · exact .inl ⟨_, rfl⟩
  case warp w =>
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    simp only [eventTmpl, warpTmpl]
    split
    · simp only [OpTmpl, OpEv, shflTmpl]; tmpl_steps exact ⟨_, _, _, _, _, rfl⟩
    · simp only [OpTmpl, OpEv, voteTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
    all_goals first
      | exact .inl ⟨_, rfl⟩
      | (simp only [OpTmpl, OpEv, electTmpl]; tmpl_steps exact ⟨_, _, rfl⟩; done)
      | (simp only [OpTmpl, OpEv, warpBarTmpl]; tmpl_steps exact ⟨_, _, rfl⟩; done)
      | (right; simp only [OpEv]; try (split <;> first | trivial | simp_all))
  case fence f =>
    cases f with
    | thread _ _ => exact .inr trivial
    | proxy k _ a =>
      cases a with
      | none => exact .inr ⟨_, rfl⟩
      | some _ =>
        simp only [eventTmpl, fenceTmpl]
        split
        · exact .inl ⟨_, rfl⟩
        · split <;> first | exact .inr ⟨_, rfl⟩ | exact .inl ⟨_, rfl⟩
  case fenceMbarInit => exact widen_opTmpl (.inr ⟨_, rfl⟩)
  case mbarInit =>
    apply widen_opTmpl
    simp only [tmaTmpl]
    tmpl_steps exact ⟨_, _, _, rfl⟩
  case mbarInval =>
    apply widen_opTmpl
    simp only [tmaTmpl]
    tmpl_steps exact ⟨_, _, rfl⟩
  case mbarArrive =>
    apply widen_opTmpl
    simp only [tmaTmpl]
    tmpl_steps exact ⟨_, _, _, _, _, _, rfl⟩
  case mbarWait =>
    apply widen_opTmpl
    simp only [tmaTmpl]
    tmpl_steps exact ⟨_, _, _, _, _, rfl⟩
  case clcQuery => simp only [eventTmpl, clcTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  case clcTryCancel multicast dst off mb moff =>
    simp only [eventTmpl, clcTmpl]
    apply ofExec_opTmpl
    cases hd : effAddr L g t .shared dst off with
    | error f => exact trivial
    | ok d =>
      cases hm : mbarLoc L g t mb moff with
      | error f => simp [bind, Except.bind, PTX.EventFrame.AllOk]
      | ok l =>
        obtain ⟨hds, hdc⟩ := effAddr_shared hd
        obtain ⟨hls, hlc⟩ := mbarLoc_local hm
        simp only [bind, Except.bind]
        split
        · exact .inr ⟨_, _, _, rfl, hds, hdc, hls, hlc, rfl⟩
        · exact trivial
  case bulkCommit => exact .inr ⟨_, rfl⟩
  case bulkWait => exact .inr ⟨_, _, _, rfl⟩
  case cpTensor =>
    simp only [eventTmpl, tensorTmpl, tensorMulticast]
    tmpl_steps exact ⟨_, _, _, rfl⟩
  case cpTensorStore => simp only [eventTmpl, tensorStoreTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  case tcCommit => simp only [eventTmpl, tcCommitTmpl]; tmpl_steps exact ⟨_, _, rfl⟩
  case tcMma => simp only [eventTmpl, tcTmpl, mmaTmpl]; tmpl_steps exact ⟨_, _, _, _, _, rfl⟩
  case tcLd =>
    simp only [eventTmpl]
    refine tcLdTmpl_pres ?_ (fun _ => .inr (.inr ⟨_, rfl⟩)) ?_
    · intro m pc h
      cases m with
      | tcLd a n sh k => exact .inr (.inl ⟨_, _, _, _, rfl⟩)
      | _ => exact h
    · simp only [tcTmpl]; tmpl_steps exact .inl ⟨_, _, _, _, rfl⟩
  case tcWaitLd => simp only [eventTmpl, tcTmpl]; tmpl_steps exact ⟨_, rfl⟩
  case tcAlloc =>
    simp only [eventTmpl, tcTmpl]
    tmpl_steps first
      | exact .inl ⟨_, _, _, _, rfl⟩
      | exact .inr ⟨_, _, rfl⟩
  case tcDealloc =>
    simp only [eventTmpl, tcTmpl]
    tmpl_steps exact ⟨_, _, _, rfl, fun _ h => by cases h⟩
  case tcRelinquish =>
    simp only [eventTmpl, tcTmpl]
    tmpl_steps exact ⟨_, _, _, rfl, fun _ h => by cases h⟩
  case cluster => exact .inr ⟨_, rfl⟩
  case barSync => simp only [eventTmpl, barTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  case barSyncN => simp only [eventTmpl, barTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  case barArrive => simp only [eventTmpl, barTmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  case setMaxReg => simp only [eventTmpl, SetMaxNReg.tmpl]; tmpl_steps exact ⟨_, _, _, rfl⟩
  all_goals exact .inr trivial

/-- The allocation's template after its first sub-step is not the allocation. -/
theorem eventTmpl_alloc_sub {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {grp : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} (hs : t.sub ≠ 0) :
    NotResource (eventTmpl A L g t (.tcAlloc grp base off nc)) := by
  simp only [eventTmpl, tcTmpl, hs, ite_false]
  apply ofExec_notResource
  repeat' first
    | exact trivial
    | (apply PTX.EventFrame.allOk_bind; intro _)
    | split

end PTX.Flow
