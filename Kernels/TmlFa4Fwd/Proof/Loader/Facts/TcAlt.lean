-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The electing lane's tensor copies alternate

Standalone fact. On a lane that wins every election it takes part in, the tensor copies on a full
barrier, with those still to come in the current group, are two per successful poll of the barrier's
empty one (`TcAlt`): copy `c` of a group is a copy with `2 u + c` earlier ones. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The copies still to come at a site of a TMA group. -/
def tcRem (s : Site) (o : Nat) : Nat :=
  match s with
  | .te t e => if taOff t = o then (if e.val = 2 then 1 else 2) else 0
  | .ta t => if taOff t = o then 2 else 0
  | .tc t c => if taOff t = o then 2 - c.val else 0
  | _ => 0

def Site.isTe : Site → Bool
  | .te .. => true
  | _ => false

/-- The edge check at sites other than elections, for the barriers with two copies per poll. -/
def altChk (_ : Bool) (s s' : Site) : Bool :=
  s.isTe || [0, 320, 328].all fun o =>
    tcRem s' o + (if s.tcOff = some o then 1 else 0) ==
      tcRem s o + (if tag s s' = .acq (o + 16) then 2 else 0)

theorem alt_edges : Edges altChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def TcAlt (L : Launch) (g o : Nat) (dn : D × (Cnt → Nat)) (N : Nat) : Prop :=
  N + tcRem dn.1.site o = 2 * dn.2 (.acquire (bl L g (o + 16)))

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

theorem alt_step {o : Nat} (ho : o ∈ [0, 320, 328]) (hp : Pre p L m) {dn : D × (Cnt → Nat)}
    {e : Event} {d' : D} {N : Nat} (hev : Ev p L g w dn.1 e) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w dn.1 e = some (some d')) (hm : Move L g w dn e d')
    (hwon : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (h : TcAlt L g o dn N) :
    TcAlt L g o (d', Code.bump (cls L g) dn.2 e) (N + if isTc L g o e then 1 else 0) := by
  obtain ⟨d, n⟩ := dn
  obtain ⟨-, -, h3, h4⟩ := copy_site hev hub
  simp only at h3 h4 hn
  have ho' : o ∈ [0, 8, 320, 328] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    omega
  have hi : (if isTc L g o e then 1 else 0) = if d.site.tcOff = some o then 1 else 0 := by
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
      have h1 : isTc L g o e = false := by
        unfold isTc
        split
        · exact absurd ‹_› (hno _ _)
        · rfl
      have h2 : d.site.tcOff = none := by
        revert hs
        cases d.site <;> simp [Site.tcOff]
      simp [h1, h2]
  unfold TcAlt at h ⊢
  simp only at h ⊢
  rw [hi]
  have hb : Code.bump (cls L g) n e (.acquire (bl L g (o + 16))) =
      n (.acquire (bl L g (o + 16))) +
        if tag d.site d'.site = .acq (o + 16) then 1 else 0 := by
    rw [bump_tag hm]
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
        Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    case acqRing δ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      have := Nat.mod_lt (n .commit + δ) (show 0 < 3 by decide)
      have hne : ¬ 56 + 8 * ((n .commit + δ) % 3) = o + 16 := by omega
      simp [hne]
  rw [hb]
  by_cases hte : d.site.isTe = true
  · -- an election, won
    obtain ⟨site, v, kk⟩ := d
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
    have ht : tag (Site.te t i) (teElected ⟨.te t i, v, kk⟩ t i).site ≠ .acq (o + 16) := by
      fin_cases i <;> simp [teElected, tag]
    have hrem : tcRem (teElected ⟨.te t i, v, kk⟩ t i).site o = tcRem (.te t i) o := by
      fin_cases i <;> simp [teElected, tcRem]
    rw [hrem]
    simp only [ht, ↓reduceIte, Nat.add_zero]
    exact h
  · rcases hm.edge with hs | hs
    · -- a retried site is no copy
      have hself : d.site.tcOff = none := by
        by_contra hne
        obtain ⟨t, c, hst⟩ : ∃ t c, d.site = .tc t c := by
          revert hne
          cases d.site <;> simp [Site.tcOff]
        obtain ⟨a, s, hk, -⟩ := h4 t c hst
        have hcl := hm.cnt .copy
        have ht : tag d.site d'.site = .none := by rw [hs, tag_self]
        simp only [ht, Tag.cnt, reduceCtorEq, decide_false] at hcl
        simp [cls, hk] at hcl
      rw [hs, tag_self, hself]
      simpa using h
    · have hc := alt_edges.ok hs
      simp only [altChk, Bool.or_eq_true] at hc
      have hc := hc.resolve_left hte
      have hco := beq_iff_eq.mp (List.all_eq_true.mp hc o ho)
      split_ifs at hco ⊢ <;> omega

/-- **The electing lane's copies** at every state. -/
theorem tc_alt {o : Nat} (ho : o ∈ [0, 320, 328]) (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hwon : ∀ k pc mask inst ld, X.get (g, k) = some ⟨pc, .elect mask inst ld⟩ →
      ld = laneOf L g)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) :
    TcAlt L g o (d, LdWarp.lcn n) (((X.tr g).take k).countP (isTc L g o)) :=
  LdWarp.count_on (I := fun _ => TcAlt L g o) (c := isTc L g o)
    (fun e h => by
      unfold isTc at h
      split at h
      · exact .inr ⟨_, _, ‹_›⟩
      · cases h)
    (fun b => by simp [TcAlt, tcRem])
    (fun _ _ e _ _ _ _ hev hub hn hm ⟨j, hj⟩ h => alt_step ho hp hev hub hn hm
      (fun mask inst ld hk => by
        obtain ⟨pc, kd⟩ := e
        simp only at hk
        subst hk
        exact hwon j pc mask inst ld hj) h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
