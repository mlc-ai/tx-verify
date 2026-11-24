-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext
public import Lemmas.Flow.Fire
public import Lemmas.Flow.Resource

@[expose] public section

/-! # A thread fires the event of its site's kind (`NextFacts.fire`)

The instruction at each site is one its kind accepts (`kindOp`, decided site by site for every
role: `site_kindOp`). A thread whose run ends in a state of its machine reaches, by local steps, a
concrete state of it whose template is the event of the instruction at its site (`Frame.end_at`):
undefined behaviour or an event of the instruction's class (`eventTmpl_opTmpl`, with the
`tcgen05.st` and `tcgen05.wait::st` templates here), so of the site's kind (`kindTmpl_of`). The
allocation instruction fires the request at the MMA warp's allocation site (sub-step 0) and the
store of its address at the write site (sub-step 1) (`alloc_site`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- Decide a fact of each site with the kernel, its parameters reverted. -/
macro "site_decide_k" : tactic => `(tactic| (
  all_goals (try cases ‹Loader.UseK›)
  all_goals (try cases ‹Correction.Gen›)
  all_goals (repeat' (first | revert ‹Fin _› | revert ‹Bool›))
  all_goals decide +kernel))

/-- The instructions at a site of each kind. -/
def kindOp : NextKind → Op → Bool
  | .wait, .mbarWait .. => true
  | .warp, .warp ⟨.shfl _, _, _, _, _⟩ | .warp, .warp ⟨.elect, _, _, _, _⟩
  | .warp, .warp ⟨.barWarp, _, _, _, _⟩ | .warp, .warp ⟨.vote .ballot _, _, _, _, _⟩ => true
  | .cluster, .cluster _ => true
  | .bar, .barSync .. | .bar, .barSyncN .. | .bar, .barArrive .. => true
  | .reg, .setMaxReg .. => true
  | .tmem, .tcAlloc .. | .tmem, .tcDealloc .. | .tmem, .tcRelinquish .. => true
  | .init, .mbarInit .. => true
  | .arrive, .mbarArrive .. => true
  | .tensorLoad, .cpTensor .. => true
  | .tensorStore, .cpTensorStore .. => true
  | .mma, .tcMma .. => true
  | .commit, .tcCommit .. => true
  | .bulkWait, .bulkWait .. => true
  | .tcLoad, .tcLd .. | .tcLoad, .tcWaitLd => true
  | .tcStore, .tcSt .. | .tcStore, .tcWaitSt => true
  | .read, .mem a => a.kind == .load && a.space != some .param && !a.nc &&
      (a.sem == .weak || a.sem == .acquire)
  | .quiet, .fence (.proxy (.async (some (.shared .cta))) none none) | .quiet, .fenceMbarInit
  | .quiet, .bulkCommit => true
  | .store, .mem a => a.kind == .store && a.sem == .weak
  | .allocStore, .tcAlloc .. => true
  | .exit, .ret | .exit, .exit => true
  | _, _ => false

/-- Whether the instruction at `pc` is one kind `k` accepts. -/
def siteOk (k : NextKind) (pc : Nat) : Bool :=
  (kernel.code[pc]?).any fun ins => kindOp k ins.op

theorem prologue_sites (s : Prologue.Site) : siteOk (prologueKind s) s.pc = true := by
  cases s <;> site_decide_k

theorem idle_sites (s : Idle.Site) : siteOk (idleKind s) s.pc = true := by
  cases s <;> site_decide_k

theorem loader_sites (s : Loader.Site) : siteOk (loaderKind s) s.pc = true := by
  cases s <;> site_decide_k

theorem mma_sites (s : Mma.Site) : siteOk (mmaKind s) s.pc = true := by
  cases s <;> site_decide_k

theorem store_sites (s : Store.Site) : siteOk (storeKind s) s.pc = true := by
  cases s <;> site_decide_k

set_option maxHeartbeats 2000000 in
theorem softmax_sites (s : Softmax.Site) : siteOk (softmaxKind s) s.pc = true := by
  cases s <;> site_decide_k

set_option maxHeartbeats 2000000 in
theorem corr_sites (s : Correction.Site) : siteOk (corrKind s) s.pc = true := by
  cases s <;> site_decide_k

/-- **The instruction at a state's site is one its kind accepts.** -/
theorem site_kindOp {L : Launch} {g : Nat} (d : ThreadD) {ins : Instr}
    (hc : kernel.code[(code L g).pc d]? = some ins) : kindOp (nextKind d) ins.op = true := by
  have h : siteOk (nextKind d) ((code L g).pc d) = true := by
    rcases d with p | (s | l | m | s | s | c)
    · exact prologue_sites p.site
    · exact idle_sites s.site
    · exact loader_sites l.site
    · exact mma_sites m.site
    · exact store_sites s.site
    · exact softmax_sites s.site
    · exact corr_sites c.site
  simpa [siteOk, hc] using h

/-- The allocation instruction. -/
def allocOp : Op → Bool
  | .tcAlloc .. => true
  | _ => false

theorem not_alloc_of {k : NextKind} {op : Op} (hk : kindOp k op = true)
    (hne : k ≠ .tmem) (hne' : k ≠ .allocStore) : allocOp op = false := by
  cases k <;> cases op <;> simp_all [kindOp, allocOp]

/-- **The allocation instruction is at the MMA warp's allocation and write sites only.** -/
theorem alloc_site {L : Launch} {g : Nat} {d : ThreadD} {ins : Instr}
    (hc : kernel.code[(code L g).pc d]? = some ins) (ha : allocOp ins.op = true) :
    ∃ m : Mma.D, d = .inr (.mma m) ∧ (m.site = .alloc ∨ m.site = .allocWrite) := by
  have hk := site_kindOp d hc
  have hkind : nextKind d = .tmem ∨ nextKind d = .allocStore := by
    by_contra h
    push Not at h
    rw [not_alloc_of hk h.1 h.2] at ha
    cases ha
  rcases d with p | (s | l | m | s | s | c)
  · obtain ⟨s⟩ := p
    cases s <;> simp [nextKind, prologueKind] at hkind
  · obtain ⟨s⟩ := s
    cases s <;> simp [nextKind, idleKind] at hkind
  · cases hs : l.site <;> simp [nextKind, loaderKind, hs] at hkind
  · -- relinquish and deallocation sites are `tcRelinquish` and `tcDealloc`
    refine ⟨m, rfl, ?_⟩
    have hc' : kernel.code[m.site.pc]? = some ins := hc
    cases hs : m.site <;> simp [nextKind, mmaKind, hs] at hkind
    all_goals (try simp)
    · have hx : (kernel.code[Flow.tmemRelinquish_0]?).all (fun i => !allocOp i.op) = true := by
        decide +kernel
      simp [hs, Mma.Site.pc] at hc'
      simp [hc', ha] at hx
    · have hx : (kernel.code[Flow.tmemDealloc_0]?).all (fun i => !allocOp i.op) = true := by
        decide +kernel
      simp [hs, Mma.Site.pc] at hc'
      simp [hc', ha] at hx
  · cases hs : s.site <;> simp [nextKind, storeKind, hs] at hkind
  · cases hs : s.site <;> simp [nextKind, softmaxKind, hs] at hkind
  · cases hs : c.site <;> simp [nextKind, corrKind, hs] at hkind

/-- The `tcgen05.st` template: undefined behaviour or the store. -/
theorem eventTmpl_tcSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ta : Nat}
    {ss : List Opnd} {sh : TcShape} (hwait : A.any (·.tcStWaitLd t.pc) = false := by hooks_off) :
    (∃ f, eventTmpl A L g t (.tcSt ta ss sh) = .ub f) ∨
      ∃ a vs u, eventTmpl A L g t (.tcSt ta ss sh) = .tc (.st a vs sh) u := by
  rw [eventTmpl_tcSt_noWait hwait]
  simp only [tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  repeat' (first | split | simp [ofExec] | simp_all)

/-- The `tcgen05.wait::st` template: undefined behaviour or the wait. -/
theorem eventTmpl_tcWaitSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState} :
    (∃ f, eventTmpl A L g t .tcWaitSt = .ub f) ∨
      ∃ u, eventTmpl A L g t .tcWaitSt = .tc .waitSt u := by
  simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  repeat' (first | split | simp [ofExec])

/-- The fence a quiet site accepts is `fence.proxy.async.shared::cta`. -/
theorem kindOp_quiet_fence {f : FenceInstr} (h : kindOp .quiet (.fence f) = true) :
    f = .proxy (.async (some (.shared .cta))) none none := by
  revert h
  unfold kindOp
  split <;> simp_all

/-- **The template at a concrete state of a machine state is undefined behaviour or of the
state's kind.** -/
theorem tmpl_kind {L : Launch} {g : Nat} {d : ThreadD} {t1 : TState} {ins : Instr}
    (hat : (code L g).AtD d t1) (hc : kernel.code[(code L g).pc d]? = some ins) :
    (∃ f, eventTmpl asms L g t1 ins.op = .ub f) ∨
      KindTmpl (nextKind d) (eventTmpl asms L g t1 ins.op) := by
  have hk := site_kindOp d hc
  generalize hop : ins.op = op at hk
  by_cases ha : allocOp op = true
  · obtain ⟨m, rfl, hs⟩ := alloc_site hc (hop ▸ ha)
    cases op <;> simp only [allocOp, Bool.false_eq_true] at ha
    rename_i grp b o nc
    have hsub : t1.sub = m.site.sub := hat.2.1
    rcases hs with hs | hs
    · have h := tmemTmpl_alloc (A := asms) (L := L) (g := g) (group := grp) (base := b) (off := o)
        (nc := nc) (t := t1) (by rw [hsub, hs]; rfl)
      rcases eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t1)
        (.tcAlloc grp b o nc) with hub | hev
      · exact .inl hub
      · right
        simp only [nextKind, mmaKind, hs]
        rcases hev with ⟨grp', dst, n, u, hm⟩ | ⟨dst, u, hm⟩
        · exact ⟨grp', some dst, .alloc n, u, hm⟩
        · rw [hm] at h; exact h.elim
    · rcases eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t1)
        (.tcAlloc grp b o nc) with hub | hev
      · exact .inl hub
      · right
        simp only [nextKind, mmaKind, hs]
        rcases hev with ⟨grp', dst, n, u, hm⟩ | ⟨dst, u, hm⟩
        · have h := eventTmpl_alloc_sub (A := asms) (L := L) (g := g) (grp := grp) (base := b)
            (off := o) (nc := nc) (t := t1) (by rw [hsub, hs]; decide)
          rw [hm] at h; exact h.elim
        · exact ⟨dst, u, hm⟩
  · rcases eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t1) op with hub | hev
    · exact .inl hub
    generalize nextKind d = k at hk ⊢
    cases k <;> cases op <;> simp only [kindOp, allocOp, Bool.false_eq_true] at hk ha
    case tcStore.tcSt ta ss sh =>
      rcases eventTmpl_tcSt (A := asms) (L := L) (g := g) (t := t1) (ta := ta) (ss := ss)
        (sh := sh) with h | ⟨a, vs, u, h⟩
      · exact .inl h
      · exact .inr (.inl ⟨a, vs, sh, u, h⟩)
    case tcStore.tcWaitSt =>
      rcases eventTmpl_tcWaitSt (A := asms) (L := L) (g := g) (t := t1) with h | ⟨u, h⟩
      · exact .inl h
      · exact .inr (.inr ⟨u, h⟩)
    case read.mem a =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hk
      obtain ⟨⟨⟨hk1, -⟩, hnc⟩, hsem⟩ := hk
      simp only [OpEv, hk1, hnc] at hev
      rcases hsem with hs | hs <;> simp only [hs] at hev
      · obtain ⟨r, k, h, -⟩ := hev
        exact .inr ⟨r, k, h⟩
      · exact .inr hev
    case store.mem a =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      simp only [OpEv, hk.1, hk.2] at hev
      exact .inr hev
    case warp.warp w =>
      rcases w with ⟨kind, ty, dsts, srcs, mask⟩
      cases kind <;> (try cases ‹VoteMode›) <;> simp only [Bool.false_eq_true] at hk <;>
        simp only [OpEv] at hev
      · exact .inr (.inl hev)
      · exact .inr (.inr (.inr (.inr hev)))
      · exact .inr (.inr (.inl hev))
      · exact .inr (.inr (.inr (.inl hev)))
    case tmem.tcDealloc =>
      obtain ⟨grp, act, u, h, -⟩ := hev
      exact .inr ⟨grp, none, act, u, h⟩
    case tmem.tcRelinquish =>
      obtain ⟨grp, act, u, h, -⟩ := hev
      exact .inr ⟨grp, none, act, u, h⟩
    case bar.barSync =>
      obtain ⟨id, u, c, h⟩ := hev
      exact .inr ⟨id, u, c, _, h⟩
    case bar.barSyncN =>
      obtain ⟨id, u, c, h⟩ := hev
      exact .inr ⟨id, u, c, _, h⟩
    case bar.barArrive =>
      obtain ⟨id, u, c, h⟩ := hev
      exact .inr ⟨id, u, c, _, h⟩
    case quiet.fence f =>
      obtain rfl := kindOp_quiet_fence hk
      exact .inr (.inl (by simpa [OpEv] using hev))
    case tmem.tcAlloc => exact absurd ha (by simp)
    case allocStore.tcAlloc => exact absurd ha (by simp)
    all_goals right
    all_goals simp only [KindTmpl]
    all_goals first
      | exact hev
      | exact .inr hev
      | exact .inr (.inl hev)
      | exact .inr (.inr hev)
      | exact ⟨_, hev⟩

/-- **A thread whose run ends in a machine state fires the event of its site's kind.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.NextFacts_fire {P : Params} {L : Launch}
    {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0) :
    ∀ {g : Nat} {d : ThreadD} {t : TState}, g < L.threads →
      Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
      Run kernel asms L g {} (X.tr g) (some t) → ∃ t1 m,
        Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧ (code L g).AtD d t1 ∧
        out kernel asms L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl (nextKind d) m) := by
  intro g d t hg hσ hr
  obtain ⟨t1, ins, hl, hat, -, hc, hout⟩ :=
    Frame.end_at (C := code L) (fun _ hg => sound hpre hg) hg hr hσ
  exact ⟨t1, _, hl, hat, hout, tmpl_kind hat hc⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
