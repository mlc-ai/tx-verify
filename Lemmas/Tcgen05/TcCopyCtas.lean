-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame
public import Lemmas.Flow.Hooks
public import Core.Assembly.Execution

@[expose] public section

/-! # A tcgen05 copy names each CTA of its group once

A proof tool. The thread rule of `tcgen05.cp` (THREAD-TC) takes the copy's destination CTAs
from the issuer's CTA group (`Launch.ctaGroup`, PROG-CTA-GROUP): the issuer's own CTA for
cta_group::1, and for cta_group::2 the CTA of the even rank of the pair followed by the CTA of
the next rank. These CTAs are distinct (`Launch.ctaGroup_nodup`). No other instruction fires a
copy event (`eventTmpl_cpNodup`), so in a consistent execution the CTA list of every copy has no
repeats (`cpIssue_ctas_nodup`). -/

namespace PTX.TcMma
open PTX

noncomputable section

/-- The CTAs of a CTA group are distinct. -/
theorem _root_.PTX.Launch.ctaGroup_nodup {L : Launch} {cta : Nat} {group : CtaGroup}
    {ctas : List Nat} (h : L.ctaGroup cta group = some ctas) : ctas.Nodup := by
  cases group
  · rw [Launch.ctaGroup_one] at h
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.nodup_singleton p
  · rw [Launch.ctaGroup_two] at h
    simp only [Launch.peerCta] at h
    split_ifs at h <;> simp only [Option.bind_some, Option.bind_none, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    simp

/-- A template whose copy events, if any, name distinct CTAs. -/
def CpNodup : Tmpl → Prop
  | .tc (.cp c) _ => c.ctas.Nodup
  | _ => True

theorem ofExec_cpNodup {r : Exec Tmpl} (h : PTX.EventFrame.AllOk CpNodup r) :
    CpNodup (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_cpNodup {A : List Assumption} {site : Nat} {m : Tmpl} (h : CpNodup m) :
    CpNodup (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

/-- The template of an instruction's local rule, or its `noRule` fault, fires no copy. -/
theorem ruleTmpl_cpNodup {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    CpNodup (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · rename_i r _
    cases r <;> simp only [localSregTmpl, sregTmpl, CpNodup]
  · simp only [CpNodup]

theorem ite_cpNodup {c : Prop} [Decidable c] {a b : Tmpl} (ha : CpNodup a) (hb : CpNodup b) :
    CpNodup (if c then a else b) := by
  split <;> assumption

/-- **Every instruction's template fires copies to distinct CTAs**: only `tcgen05.cp` fires a
copy, and its CTAs are the issuer's CTA group. -/
theorem eventTmpl_cpNodup {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    CpNodup (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_cpNodup (op := .int i)
  case move m => exact ruleTmpl_cpNodup (op := .move m)
  case cvt c => exact ruleTmpl_cpNodup (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try
    (apply Flow.tcLdTmpl_pres (Flow.thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_cpNodup
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_cpNodup)
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
        tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_cpNodup)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_cpNodup)
         | split
         | (exact Launch.ctaGroup_nodup ‹_›)
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A copy event fired by a template that fires copies to distinct CTAs names distinct CTAs. -/
theorem fires_cpNodup {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : CpNodup m)
    (hf : Fires pc m e o) {c : TcCopy.Spec} (hk : e.kind = .tc (.cp c)) : c.ctas.Nodup := by
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases m <;> simp only [Fires] at hf <;> aesop

/-- A copy event of a thread's run names distinct CTAs. -/
theorem run_cpNodup {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {es : List Event} {o : Option TState} (h : Run K A L g t es o) {e : Event} (he : e ∈ es)
    {c : TcCopy.Spec} (hk : e.kind = .tc (.cp c)) : c.ctas.Nodup := by
  have step : ∀ {t1 : TState} {o' : Option TState}, EStep K A L g t1 e o' → c.ctas.Nodup := by
    intro t1 o' hs
    cases o' with
    | some u =>
      obtain ⟨ins, -, -, hf⟩ := PTX.EventFrame.estep_event_source hs
      exact fires_cpNodup eventTmpl_cpNodup hf hk
    | none =>
      obtain ⟨m, -, hf⟩ := hs
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      exfalso
      cases m <;> simp only [Fires] at hf <;> aesop
  induction h with
  | nil => cases he
  | step _ hs _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact step hs
    · exact ih he
  | last _ hs =>
    cases List.mem_singleton.mp he
    exact step hs

/-- **The CTA list of a copy has no repeats** in a consistent execution: the copy is fired by a
`tcgen05.cp`, whose CTAs are the issuer's CTA group. -/
theorem cpIssue_ctas_nodup {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {cp : EvId} {c : TcCopy.Spec}
    (h : X.CpIssue cp c) : c.ctas.Nodup := by
  obtain ⟨pc, he⟩ := h
  obtain ⟨g, k⟩ := cp
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hg : g < L.threads := by
    by_contra hn
    rw [hX.outside g (by omega)] at hk
    simp at hk
  obtain ⟨o, hr⟩ := hX.thr g hg
  exact run_cpNodup hr (List.mem_of_getElem? he) rfl

end
end PTX.TcMma
