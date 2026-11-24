-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Kinds

@[expose] public section

/-!
# A thread fires the event of its site's kind

A thread whose run ends in a state of its machine reaches, by local steps, a concrete state of it
whose template is the event of the instruction at the state's site (`Frame.end_at`): undefined
behaviour or an event of the instruction's class (`Flow.eventTmpl_opTmpl`), so of the state's kind
(`tmpl_kind`). `fire` is that fact for the machines of the launch; it needs the soundness of the
machines and nothing else.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

/-- The fence a quiet site accepts is `fence.proxy.async.shared::cta`. -/
theorem opKind_quiet_fence {f : FenceInstr} (h : opKind (.fence f) ≠ .other) :
    f = .proxy (.async (some (.shared .cta))) none none := by
  revert h
  unfold opKind
  split <;> simp_all

variable {L : Launch} {g : Nat} {Q : Params}

/-- **The template at a concrete state of a machine state is undefined behaviour or of the
state's kind.** -/
theorem tmpl_kind {s : TSt} {t1 : TState} {ins : Instr}
    (hat : (threadCode L g Q).AtD s t1) (hc : kernel.code[TSt.pc s]? = some ins)
    (hk : opKind ins.op ≠ .other) :
    (∃ f, eventTmpl asms L g t1 ins.op = .ub f) ∨
      KindTmpl (nextKind s) (eventTmpl asms L g t1 ins.op) := by
  have hnk : nextKind s = opKindSub ins.op (TSt.sub s) := by simp [nextKind, hc]
  have hsub : t1.sub = TSt.sub s := hat.2.1
  rw [hnk]
  generalize ins.op = op at hk ⊢
  rcases eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t1) op with hub | hev
  · exact .inl hub
  cases op
  case mbarWait => exact .inr hev
  case warp w =>
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    cases kind <;> (try cases ‹VoteMode›) <;> first
      | exact absurd rfl hk
      | (simp only [OpEv] at hev
         simp only [opKindSub, opKind, KindTmpl]
         first
          | exact .inr (.inl hev)
          | exact .inr (.inr (.inl hev))
          | exact .inr (.inr (.inr (.inl hev)))
          | exact .inr (.inr (.inr (.inr hev))))
  case barSync => obtain ⟨id, u, c, h⟩ := hev; exact .inr ⟨id, u, c, _, h⟩
  case barSyncN => obtain ⟨id, u, c, h⟩ := hev; exact .inr ⟨id, u, c, _, h⟩
  case barArrive => obtain ⟨id, u, c, h⟩ := hev; exact .inr ⟨id, u, c, _, h⟩
  case setMaxReg => exact .inr hev
  case tcAlloc grp b o nc =>
    simp only [OpEv] at hev
    by_cases h0 : TSt.sub s = 0
    · have h := tmemTmpl_alloc (A := asms) (L := L) (g := g) (group := grp) (base := b)
        (off := o) (nc := nc) (t := t1) (by rw [hsub, h0])
      simp only [opKindSub, h0, ↓reduceIte, KindTmpl]
      rcases hev with ⟨grp', dst, n, u, hm⟩ | ⟨dst, u, hm⟩
      · exact .inr ⟨grp', some dst, .alloc n, u, hm⟩
      · rw [hm] at h; exact h.elim
    · have h := eventTmpl_alloc_sub (A := asms) (L := L) (g := g) (grp := grp) (base := b)
        (off := o) (nc := nc) (t := t1) (by rw [hsub]; exact h0)
      simp only [opKindSub, h0, ↓reduceIte, KindTmpl]
      rcases hev with ⟨grp', dst, n, u, hm⟩ | ⟨dst, u, hm⟩
      · rw [hm] at h; exact h.elim
      · exact .inr ⟨dst, u, hm⟩
  case tcDealloc =>
    simp only [OpEv] at hev
    obtain ⟨grp, act, u, h, -⟩ := hev
    exact .inr ⟨grp, none, act, u, h⟩
  case tcRelinquish =>
    simp only [OpEv] at hev
    obtain ⟨grp, act, u, h, -⟩ := hev
    exact .inr ⟨grp, none, act, u, h⟩
  case mbarInit => exact .inr hev
  case mbarArrive => exact .inr hev
  case cpTensor => exact .inr hev
  case tcMma => exact .inr hev
  case tcCommit => exact .inr hev
  case tcLd => exact .inr hev
  case tcWaitLd => exact .inr (.inr hev)
  case tcSt ta ss sh =>
    rcases eventTmpl_tcSt (A := asms) (L := L) (g := g) (t := t1) (ta := ta) (ss := ss)
      (sh := sh) rfl with h | ⟨a, vs, u, h⟩
    · exact .inl h
    · exact .inr (.inl ⟨a, vs, sh, u, h⟩)
  case tcWaitSt =>
    rcases eventTmpl_tcWaitSt (A := asms) (L := L) (g := g) (t := t1) with h | ⟨u, h⟩
    · exact .inl h
    · exact .inr (.inr ⟨u, h⟩)
  case mem a =>
    by_cases hr : (a.kind == MemKind.load && a.space != some StateSpace.param && !a.nc &&
        (a.sem == Sem.weak || a.sem == Sem.acquire)) = true
    · have hk' : opKindSub (.mem a) (TSt.sub s) = .read := by
        simp only [opKindSub, opKind, hr, ↓reduceIte]
      rw [hk']
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hr
      obtain ⟨⟨⟨hk1, -⟩, hnc⟩, hsem⟩ := hr
      simp only [OpEv, hk1, hnc] at hev
      rcases hsem with hs | hs <;> simp only [hs] at hev
      · obtain ⟨r, k, h, -⟩ := hev
        exact .inr ⟨r, k, h⟩
      · obtain ⟨r, k, h⟩ := hev
        exact .inr ⟨r, k, h⟩
    · by_cases hw : (a.kind == MemKind.store && a.sem == Sem.weak) = true
      · have hk' : opKindSub (.mem a) (TSt.sub s) = .store := by
          simp [opKindSub, opKind, hr, hw]
        rw [hk']
        simp only [Bool.and_eq_true, beq_iff_eq] at hw
        simp only [OpEv, hw.1, hw.2] at hev
        exact .inr hev
      · exfalso
        apply hk
        simp [opKind, hr, hw]
  case fence f =>
    obtain rfl := opKind_quiet_fence hk
    simp only [OpEv, opKindSub, opKind, KindTmpl] at hev ⊢
    exact .inr (.inl (by simpa using hev))
  case fenceMbarInit => exact .inr (.inr (.inl hev))
  case bulkCommit => exact .inr (.inr (.inr hev))
  case ret => exact .inr hev
  case exit => exact .inr hev
  all_goals exact absurd rfl hk

/-- **The instruction at a state's site has a kind**: a machine state's site is a non-local
instruction (`Code.StepAt.site`), and every non-local instruction of the program has a kind. -/
theorem kind_ne_other (hS : (threadCode L g Q).Sound) {s : TSt}
    (hinv : (threadCode L g Q).inv s) {ins : Instr} (hc : kernel.code[TSt.pc s]? = some ins) :
    opKind ins.op ≠ .other := by
  obtain ⟨ins', hc', hl, -⟩ := (hS.steps s).site hinv
  have hc'' : kernel.code[TSt.pc s]? = some ins' := hc'
  rw [hc] at hc''
  cases hc''
  have := List.all_eq_true.mp kernel_kinds ins (List.mem_of_getElem? hc)
  simpa [hl] using this

variable {X : Execution}

/-- **A thread whose run ends in a machine state fires the event of its site's kind**: by local
steps it reaches a concrete state of the machine state whose template is undefined behaviour or
of the kind. -/
theorem fire (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {s : TSt} {t : TState}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L Q) X g (X.tr g).length = some (some s))
    (hr : Run kernel asms L g {} (X.tr g) (some t)) : ∃ t1 m,
      Relation.ReflTransGen (Tau kernel asms L g) t t1 ∧ (threadCode L g Q).AtD s t1 ∧
      out kernel asms L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl (nextKind s) m) := by
  obtain ⟨t1, ins, hl, hat, hinv, hc, hout⟩ :=
    Frame.end_at (C := code L Q) hS hg hr hσ
  exact ⟨t1, _, hl, hat, hout, tmpl_kind hat hc (kind_ne_other (hS g hg) hinv hc)⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
