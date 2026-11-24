-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.LdWarp.CountFact
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The electing lane's copies on the second Q stage

The second Q stage's copies are group 2's, of the first block. On the lane that wins every election,
the copies made and the copies of the group still to come are two from the group's poll on, and zero
before it (`tc_alt8`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- Two once the lane is past group 2's poll (`z`: the lane has committed no packet). -/
def past2 (z : Bool) : Site → Nat
  | .pgLd per _ | .pgSt per _ | .rwSt per _ => if per = .prime then 0 else 2
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    if per = .prime then if v then 2 else 0 else 2
  | .tw t => if t.val ≤ 2 then 0 else 2
  | .te t _ | .ta t | .tc t _ => if t.val < 2 then 0 else 2
  | _ => if z then 0 else 2

def alt8Chk (b : Bool) (s s' : Site) : Bool :=
  b || s.isTe || [false, true].all fun z => !zOk s z ||
    tcRem s' 8 + (if s.tcOff = some 8 then 1 else 0) + past2 z s ==
      tcRem s 8 + past2 (z && tag s s' != .commit) s'

theorem alt8_edges : Edges alt8Chk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def TcAlt8 (w : Nat) (dn : D × (Cnt → Nat)) (N : Nat) : Prop :=
  w = 14 → N + tcRem dn.1.site 8 = past2 (decide (dn.2 .commit = 0)) dn.1.site

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

theorem z_next' {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g w dn e d') :
    decide (Code.bump (cls L g) dn.2 e .commit = 0) =
      (decide (dn.2 .commit = 0) && tag dn.1.site d'.site != .commit) := by
  rw [bump_tag hm]
  cases tag dn.1.site d'.site <;> simp [Tag.cnt]

theorem alt8_step (hp : Pre p L m) {dn : D × (Cnt → Nat)}
    {e : Event} {d' : D} {N : Nat} (hJ : Ref p L g w dn) (hev : Ev p L g w dn.1 e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w dn.1 e = some (some d')) (hm : Move L g w dn e d')
    (hwon : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (h : TcAlt8 w dn N) :
    TcAlt8 w (d', Code.bump (cls L g) dn.2 e) (N + if isTc L g 8 e then 1 else 0) := by
  intro hw14
  replace h := h hw14
  have hz := z_ok hJ
  obtain ⟨d, n⟩ := dn
  obtain ⟨-, -, h3, h4⟩ := copy_site hev hub
  simp only at h3 h4 hn h hz
  have hi : (if isTc L g 8 e then 1 else 0) = if d.site.tcOff = some 8 then 1 else 0 := by
    by_cases hs : ∃ t c, d.site = .tc t c
    · obtain ⟨t, c, hs⟩ := hs
      obtain ⟨a, s, hk, hb⟩ := h4 t c hs
      have hb' : s.mbar = bl L g (taOff t) := by
        rw [hb]
        obtain ⟨site, v, kk⟩ := d
        simp only at hs
        subst hs
        exact tc_loc' hp t c
      simp [isTc, hk, hb', hs, Site.tcOff, bl]
    · have hno : ∀ a s, e.kind ≠ .tensorIssue a s := fun a s hk => hs (h3.mp ⟨a, s, hk⟩)
      have h1 : isTc L g 8 e = false := by
        unfold isTc
        split
        · exact absurd ‹_› (hno _ _)
        · rfl
      have h2 : d.site.tcOff = none := by
        revert hs
        cases d.site <;> simp [Site.tcOff]
      simp [h1, h2]
  show _ = past2 (decide (Code.bump (cls L g) n e .commit = 0)) d'.site
  rw [hi, z_next' hm]
  simp only
  by_cases hte : d.site.isTe = true
  · obtain ⟨site, v, kk⟩ := d
    cases site <;> simp only [Site.isTe, Bool.false_eq_true] at hte
    rename_i t i
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
    rename_i mask inst ld
    obtain rfl := hwon mask inst ld rfl
    simp only [↓reduceIte] at hn
    subst hn
    have hoff : (Site.te t i).tcOff = none := rfl
    simp only [hoff, reduceCtorEq, ↓reduceIte, Nat.add_zero]
    have hrem : tcRem (teElected ⟨.te t i, v, kk⟩ t i).site 8 = tcRem (.te t i) 8 := by
      fin_cases i <;> simp [teElected, tcRem]
    have hpast : ∀ z z', past2 z (teElected ⟨.te t i, v, kk⟩ t i).site = past2 z' (.te t i) := by
      intro z z'
      fin_cases i <;> simp [teElected, past2]
    rw [hrem, hpast _ (decide (n .commit = 0))]
    exact h
  · rcases hm.edge with hs | hs
    · have hself : d.site.tcOff = none := by
        by_contra hne
        obtain ⟨t, c, hst⟩ : ∃ t c, d.site = .tc t c := by
          revert hne
          cases d.site <;> simp [Site.tcOff]
        obtain ⟨a, s, hk, -⟩ := h4 t c hst
        have hcl := hm.cnt .copy
        have ht : tag d.site d'.site = .none := by rw [hs, tag_self]
        simp only [ht, Tag.cnt, reduceCtorEq, decide_false] at hcl
        simp [cls, hk] at hcl
      rw [hs, tag_self, hself, show (Tag.none != Tag.commit) = true from rfl, Bool.and_true]
      simpa using h
    · have hc := alt8_edges.ok hs
      subst hw14
      simp only [alt8Chk, show not14 14 = false from rfl, Bool.false_or, Bool.or_eq_true] at hc
      have hc := hc.resolve_left hte
      have hco := List.all_eq_true.mp hc (decide (n .commit = 0))
        (by cases decide (n .commit = 0) <;> simp)
      rw [hz, Bool.not_true, Bool.false_or] at hco
      have hco := beq_iff_eq.mp hco
      omega

/-- **The electing lane's copies on the second Q stage** at every state. -/
theorem tc_alt8 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hwon : ∀ k pc mask inst ld, X.get (g, k) = some ⟨pc, .elect mask inst ld⟩ →
      ld = laneOf L g)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) :
    TcAlt8 (wOf b) (d, LdWarp.lcn n) (((X.tr g).take k).countP (isTc L g 8)) :=
  LdWarp.count_on (I := TcAlt8) (c := isTc L g 8)
    (fun e h => by
      unfold isTc at h
      split at h
      · exact .inr ⟨_, _, ‹_›⟩
      · cases h)
    (fun b _ => by simp [tcRem, past2])
    (fun _ _ e _ _ _ hJ hev hub hn hm ⟨j, hj⟩ h => alt8_step hp hJ hev hub hn hm
      (fun mask inst ld hk => by
        obtain ⟨pc, kd⟩ := e
        simp only at hk
        subst hk
        exact hwon j pc mask inst ld hj) h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
