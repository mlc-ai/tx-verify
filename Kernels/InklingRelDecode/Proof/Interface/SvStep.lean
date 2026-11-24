-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvInv

@[expose] public section

/-!
# One step of the softmax region keeps the iteration invariant: the frame lemmas

A step of the machine changes some of the fields `SvInv` reads. `SvInv.of_same0` keeps the
invariant when the entry numbers, the loop counter, the running maximum and sum and the bias words
agree, given the clauses about the S words, the final score words, the probabilities and the stage;
`SvInv.of_same` is the case where every field agrees.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- The fields of `D` the invariant reads, but for the S words, the final score words and the
probabilities, agree in two states. -/
structure Same0 (d d' : D) : Prop where
  e : d'.e = d.e
  i : d'.i = d.i
  m : d'.m = d.m
  l : d'.l = d.l
  w : d'.w = d.w
  v : d'.v = d.v
  cw : d'.cw = d.cw
  cv : d'.cv = d.cv

/-- The S words, the final score words and the probabilities agree in two states. -/
structure SameScore (d d' : D) : Prop where
  sv : d'.sv = d.sv
  fsv : d'.stg.fsv = d.stg.fsv
  pf : d'.pf = d.pf

/-- The stage's numbers agree in two states. -/
structure SameStg (d d' : D) : Prop where
  mn : d'.stg.mn = d.stg.mn
  kp : d'.stg.kp = d.stg.kp
  al : d'.stg.al = d.stg.al
  rs : d'.stg.rs = d.stg.rs
  alr : d'.stg.alr = d.stg.alr

/-- **A step that keeps the entry numbers, the loop counter, the running maximum and sum and the
bias words**: the invariant is kept where the S words', the final score words', the
probabilities' and the stage's clauses are. -/
theorem SvInv.of_same0 {d d' : D} (h : SvInv Q L g r s kvh B d) (hs : Same0 d d')
    (hn : nDone d' = nDone d)
    (hsv : d'.site = .waitLd → ∀ k < 64, (d'.sv k).1 = Value.float .f32
      (score Q r (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
        (keyB Q s d'.i (Sm.half (g % L.block)) k)))
    (hown : d'.site = .shfl5 → ∀ k < 64, (d'.stg.fsv k).1 =
      if visB Q r s (tokOf (g % L.block)) d'.i (Sm.half (g % L.block)) k then
        Value.float .f32 (logitB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d'.i
          (Sm.half (g % L.block)) k)
      else infB)
    (hst : StageSite d'.site → StageSite d.site ∧ SameStg d d')
    (hpf : PfSite d'.site → d'.pf = d.pf) :
    SvInv Q L g r s kvh B d' where
  ent := by rw [hs.e]; exact h.ent
  corr := by
    unfold Corr at *
    rw [hn, hs.m, hs.l]
    exact h.corr
  wb := by
    intro k hk hi
    rw [hs.cw] at hk
    rw [hs.i, hs.e] at hi
    rw [hs.w, hs.i]
    exact h.wb k hk hi
  vb := by
    intro k hk hi
    rw [hs.cv] at hk
    rw [hs.i, hs.e] at hi
    rw [hs.v, hs.i]
    exact h.vb k hk hi
  sv := hsv
  own := hown
  stage := by
    intro hsite
    obtain ⟨hd, hg⟩ := hst hsite
    have := h.stage hd
    rw [hs.i]
    exact (this.stg_eq hg.mn hg.kp hg.al hg.rs hg.alr)
  pf := by
    intro hsite k hk
    have hP : PfSite d.site := by
      rcases hsite with hh | hh
      · exact Or.inl (hst hh).1
      · right
        have hnd : nDone d = d.i + 1 := by
          rw [← hn]
          simp [nDone, hh, hs.i]
        by_contra hnp
        simp [nDone, hnp] at hnd
    rw [hpf hsite, hs.i]
    exact h.pf hP k hk

/-- **A step that changes none of the invariant's fields** (only the site and numbers it does not
read): the invariant is kept where the site's conditions are. -/
theorem SvInv.of_same {d d' : D} (h : SvInv Q L g r s kvh B d) (hs : Same0 d d')
    (hc : SameScore d d') (hn : nDone d' = nDone d)
    (hsv : d'.site = .waitLd → d.site = .waitLd) (hown : d'.site = .shfl5 → d.site = .shfl5)
    (hst : StageSite d'.site → StageSite d.site ∧ SameStg d d') :
    SvInv Q L g r s kvh B d' := by
  refine h.of_same0 hs hn ?_ ?_ hst (fun _ => hc.pf)
  · intro hsite k hk
    rw [hc.sv, hs.i]
    exact h.sv (hsv hsite) k hk
  · intro hsite k hk
    have := h.own (hown hsite) k hk
    rw [hc.fsv, hs.i]
    exact this

/-- A step that changes only the site. -/
theorem SvInv.site {d : D} (h : SvInv Q L g r s kvh B d) (S : Site)
    (hn : PostSite S ↔ PostSite d.site) (hsv : S = .waitLd → d.site = .waitLd)
    (hown : S = .shfl5 → d.site = .shfl5) (hst : StageSite S → StageSite d.site) :
    SvInv Q L g r s kvh B { d with site := S } := by
  refine h.of_same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ?_ hsv hown
    (fun hh => ⟨hst hh, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)
  unfold nDone
  by_cases hp : PostSite S
  · simp [hp, hn.mp hp]
  · simp [hp, mt hn.mpr hp]

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
