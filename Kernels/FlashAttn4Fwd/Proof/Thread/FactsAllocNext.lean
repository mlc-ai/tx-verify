-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsSite

@[expose] public section

/-! # After an allocation request (`NextFacts.alloc_next`)

An allocation request fires at a state of the paired Tensor Memory kind (`tmpl_kind`: every other
kind's templates fire no request), so at the MMA warp's allocation site: the relinquishment and
deallocation instructions request no allocation. From there the machine continues at the address
store on lane 0 and at the start barrier on the other lanes (`Mma.next`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A relinquishment or a deallocation instruction. -/
def freeOp : Op → Bool
  | .tcRelinquish _ | .tcDealloc .. => true
  | _ => false

/-- A template of a kind other than the paired Tensor Memory operations fires no allocation
request. -/
theorem not_alloc_of_kind {k : NextKind} {m : Tmpl} {pc pc' : Nat} {grp : CtaGroup}
    {dst : Option Loc} {n : Nat} {o : Option TState}
    (hK : (∃ f, m = .ub f) ∨ KindTmpl k m)
    (hf : Fires pc m ⟨pc', .tc (.resource grp dst (.alloc n))⟩ o) : k = .tmem := by
  rcases hK with ⟨f, rfl⟩ | hK
  · simp [Fires] at hf
  cases k <;> simp only [KindTmpl] at hK
  case tmem => rfl
  all_goals exfalso
  all_goals try casesm* _ ∨ _, ∃ _, _, _ ∧ _
  all_goals subst_vars
  all_goals simp [Fires] at hf

/-- After a lane-0 allocation, the role advances to the second event of the same instruction. -/
theorem alloc_after (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    {g j site : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {d : ThreadD}
    (he : X.get (g, j) = some ⟨site, .tc (.resource grp dst (.alloc n))⟩)
    (hσ : Frame.stateAt (code L) X g (j + 1) = some (some d)) :
    (∃ m : Mma.D, d = .inr (.mma m) ∧ m.site = .allocWrite ∧ m.site.pc = site) ∨
      laneOf L g ≠ 0 := by
  have hst := Frame.stateAt_succ (C := code L) he
  cases hσ0 : Frame.stateAt (code L) X g j with
  | none => rw [hst, hσ0] at hσ; cases hσ
  | some σ =>
    cases σ with
    | none => rw [hst, hσ0] at hσ; cases hσ
    | some d0 =>
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
        Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ0
      have hk := not_alloc_of_kind (tmpl_kind hat hc) hf
      have hnext : (code L g).next d0 ⟨site, .tc (.resource grp dst (.alloc n))⟩ =
          some (some d) := by
        rw [hst, hσ0] at hσ; exact hσ
      rcases d0 with p | (s | l | m | s | s | c)
      · obtain ⟨s⟩ := p; cases s <;> simp [nextKind, prologueKind] at hk
      · obtain ⟨s⟩ := s; cases s <;> simp [nextKind, idleKind] at hk
      · cases hs : l.site <;> simp [nextKind, loaderKind, hs] at hk
      · have hc' : kernel.code[m.site.pc]? = some ins := hc
        have htag : site = m.site.pc := EventFrame.fires_source_pc hf
        cases hs : m.site <;> simp [nextKind, mmaKind, hs] at hk
        · -- the allocation site
          simp only [code, Mma.next, hs, Option.map_eq_some_iff,
            Function.comp] at hnext
          by_cases hl : laneOf L g = 0
          · left
            simp only [hl, ↓reduceIte] at hnext
            obtain ⟨w, hw, a, hwa, had⟩ := hnext
            subst hwa had
            cases hw
            exact ⟨_, rfl, rfl, by simpa only [hs, Mma.Site.pc] using htag.symm⟩
          · exact .inr hl
        all_goals exfalso
        all_goals rw [hs] at hc'
        all_goals
          have hfree : (kernel.code[Flow.tmemRelinquish_0]?).all (fun i => freeOp i.op) &&
              (kernel.code[Flow.tmemDealloc_0]?).all (fun i => freeOp i.op) = true := by
            decide +kernel
          simp only [Mma.Site.pc, Bool.and_eq_true] at hc' hfree
          have hop : freeOp ins.op = true := by
            first
              | (rw [hc'] at hfree; simpa using hfree.1)
              | (rw [hc'] at hfree; simpa using hfree.2)
          generalize ins.op = op at hop hf
          cases op <;> simp only [freeOp, Bool.false_eq_true] at hop
          case' tcRelinquish grp0 =>
            have hev := eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t)
              (.tcRelinquish grp0)
          case' tcDealloc grp0 ta nc =>
            have hev := eventTmpl_opTmpl (A := asms) (L := L) (g := g) (t := t)
              (.tcDealloc grp0 ta nc)
          all_goals
            rcases hev with
              ⟨f, hm⟩ | ⟨grp', act, u, hm, hact⟩
            · rw [hm] at hf; simp [Fires] at hf
            · rw [hm] at hf
              simp only [Fires, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hf
              exact hact n hf.1.2.2.2.symm
      · cases hs : s.site <;> simp [nextKind, storeKind, hs] at hk
      · cases hs : s.site <;> simp [nextKind, softmaxKind, hs] at hk
      · cases hs : c.site <;> simp [nextKind, corrKind, hs] at hk

/-- A thread whose last event is an allocation request is at the address store, or is not lane
0. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.NextFacts_alloc_next (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) :
    ∀ {g pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {d : ThreadD},
      g < L.threads →
      X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ →
      Frame.stateAt (code L) X g (X.tr g).length = some (some d) →
        nextKind d = .allocStore ∨ laneOf L g ≠ 0 := by
  intro g pc grp dst n d _ he hσ
  have hj := len_of_get he
  change (X.tr g).length - 1 < (X.tr g).length at hj
  have hlen : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  rw [← hlen] at hσ
  rcases alloc_after hpre hX he hσ with ⟨m, rfl, hs, -⟩ | hl
  · exact .inl (by simp [nextKind, mmaKind, hs])
  · exact .inr hl

/-- A followed lane 0's event immediately after an allocation is its exact base-word store. -/
theorem alloc_result_event (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htr : Frame.Tracked (code L) X) (hub : ¬ HasUb X)
    {g j site : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat} {e : Event}
    (he : X.get (g, j) = some ⟨site, .tc (.resource grp dst (.alloc n))⟩)
    (hnext : X.get (g, j + 1) = some e) (hl : laneOf L g = 0) :
    ∃ bytes, X.get (g, j + 1) =
      some ⟨site, .wr { loc := baseLoc L (ctaOf L g), size := 4 } bytes⟩ := by
  have hsound : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨d, hd⟩ := Frame.state_of_noUb hsound hX htr hub hnext
  rcases alloc_after hpre hX he hd with ⟨m, rfl, hm, hsite⟩ | hne
  · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hsound hX hnext hd
    have hg : ∀ f, e.kind ≠ .ub f := by
      intro f he'
      exact hub ⟨(g, j + 1), e.pc, f, by cases e; simp_all⟩
    have hs : t.sub = 1 := by
      have hsub : t.sub = m.site.sub := hat.2.1
      rwa [hm] at hsub
    have hc' : kernel.code[m.site.pc]? = some ins := hc
    have hr : Holds t.regs (Mma.facts L g m) := hat.2.2.2.2
    have hb := Mma.sb_bounds hpre
    have hreg := Mma.reg_b32 (r := 337) (x := L.sharedBase) hr
      (by rw [hm]; table_decide) (by
        obtain ⟨s, i, t, b, p⟩ := m
        simp only at hm ⊢
        subst s
        mma_values)
    rw [hm] at hc'
    have hcode := Option.some.inj (hc'.symm.trans Flow.code_tmemAlloc_0)
    subst ins
    obtain ⟨a, bytes, hk, hloc, -, -⟩ :=
      fires_tcAllocStore_at (effAddr_b32_off (off := 328) hreg (by omega)) hs hf hg
    have hkind : nextKind (.inr (.mma m)) = .allocStore := by simp [nextKind, mmaKind, hm]
    have htmpl := tmpl_kind hat hc
    rw [hkind] at htmpl
    rcases htmpl with ⟨f, htmpl⟩ | ⟨dst', t', htmpl⟩
    · rw [htmpl] at hf
      exact absurd (congrArg Event.kind hf.1) (hg f)
    · rw [htmpl] at hf
      obtain ⟨col, -, he', -⟩ := hf
      rw [he'] at hk
      simp only [Kind.wr.injEq] at hk
      obtain ⟨ha, rfl⟩ := hk
      rw [← ha] at hloc
      change dst' = baseLoc L (ctaOf L g) at hloc
      exact ⟨(Value.bits 32 (BitVec.ofNat 64 col)).toBytes,
        by simpa only [he', hsite, hloc] using hnext⟩
  · exact (hne hl).elim

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
