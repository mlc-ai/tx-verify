-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.CountFact
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaArr
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's `cp.async` copies and the copies into a TMA barrier, in the trace

Standalone facts. A lane's `cp.async` copies are 32 per committed packet and those of the current
one (`cp_count`); its tensor copies completing on the full barrier at offset `o` are its won
elections at the copy groups' election points, less the one pending at a copy site (`tc_count`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

/-- A `cp.async` copy. -/
def isCp (e : Event) : Bool := match e.kind with | .copy _ => true | _ => false

/-- A tensor copy completing on the barrier at offset `o`. -/
def isTc (L : Launch) (g o : Nat) (e : Event) : Bool :=
  match e.kind with | .tensorIssue _ s => decide (s.mbar = bl L g o) | _ => false

def Site.isCp : Site → Bool
  | .cp .. => true
  | _ => false

def Site.tcOff : Site → Option Nat
  | .tc t _ => some (taOff t)
  | _ => none

set_option maxHeartbeats 4000000 in
/-- A copy is at a packet's copy site, a tensor copy at a TMA group's. -/
theorem copy_site {d : D} {e : Event} (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f) :
    isCp e = d.site.isCp ∧ (d.site.isCp = true → ∃ s, e.kind = .copy s ∧
      s.completion = .asyncGroup) ∧
    ((∃ a s, e.kind = .tensorIssue a s) ↔ ∃ t c, d.site = .tc t c) ∧
    ∀ t c, d.site = .tc t c → ∃ a s, e.kind = .tensorIssue a s ∧
      s.mbar = smLoc L g (rv p L g w d (tcBar t).1) (tcBar t).2 := by
  obtain ⟨site, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site <;> simp only [Ev] at hev
  case cp per b i c =>
    rcases hev with ⟨n, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp [isCp, Site.isCp]
    · exact absurd hk (hub f)
  case tc t c =>
    rcases hev with ⟨a, s, hk, hb⟩ | ⟨f, hk⟩
    · subst hk
      simp [isCp, Site.isCp, hb]
    · exact absurd hk (hub f)
  all_goals (try simp only [Epilogue.Ev, Site.toE] at hev)
  all_goals shape_destruct hev
  all_goals simp_all [isCp, Site.isCp]

/-! ### Row copies -/

/-- The edge check: 32 copies per commit. -/
def cpCntChk (_ : Bool) (s s' : Site) : Bool :=
  match tag s s' with
  | .copy => if s.isCp then
      (inPkt s').1 == (inPkt s).1 + 1 && (inPkt s').2 == (inPkt s).2
    else (inPkt s').1 == (inPkt s).1 && (inPkt s').2 == (inPkt s).2
  | .commit => (inPkt s').1 == (inPkt s).1 && (inPkt s').2 == (inPkt s).2 + 1 && !s.isCp
  | .pub => (inPkt s).1 == 32 && (inPkt s).2 == 1 && (inPkt s').1 == 0 && (inPkt s').2 == 0 &&
      !s.isCp
  | _ => (inPkt s').1 == (inPkt s).1 && (inPkt s').2 == (inPkt s).2 && !s.isCp

theorem cpCnt_edges : Edges cpCntChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def CpCount (dn : D × (Cnt → Nat)) (N : Nat) : Prop :=
  N + 32 * (inPkt dn.1.site).2 = 32 * dn.2 .commit + (inPkt dn.1.site).1

theorem cp_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} {N : Nat}
    (hev : Ev p L g w dn.1 e) (hub : ∀ f, e.kind ≠ .ub f) (hm : Move L g w dn e d')
    (h : CpCount dn N) :
    CpCount (d', Code.bump (cls L g) dn.2 e) (N + if isCp e then 1 else 0) := by
  obtain ⟨d, n⟩ := dn
  obtain ⟨h1, h2, -, -⟩ := copy_site hev hub
  simp only at h1 h2
  unfold CpCount at h ⊢
  simp only [bump_tag hm, h1] at h ⊢
  -- a copy site is left by its copy
  have hself : d'.site = d.site → d.site.isCp = false := by
    intro hs
    rw [Bool.eq_false_iff]
    intro hc
    obtain ⟨s, hk, -⟩ := h2 hc
    have hcl := hm.cnt .copy
    have ht : tag d.site d'.site = .none := by rw [hs, tag_self]
    simp only [ht, Tag.cnt, reduceCtorEq, decide_false] at hcl
    simp [cls, hk] at hcl
  rcases hm.edge with hs | hs
  · rw [hself hs, hs, tag_self]
    simpa [Tag.cnt] using h
  · have hc := cpCnt_edges.ok hs
    unfold cpCntChk at hc
    revert hc h
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, ↓reduceIte, Bool.and_eq_true,
        beq_iff_eq, Bool.not_eq_true', Nat.add_zero] <;> intro h hc
    case copy =>
      cases hcp : d.site.isCp <;> simp only [hcp, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        beq_iff_eq] at hc ⊢ <;> omega
    all_goals simp_all
    all_goals omega

/-- **A loader lane's `cp.async` copies** at every state. -/
theorem cp_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) :
    CpCount (d, LdWarp.lcn n) (((X.tr g).take k).countP isCp) :=
  LdWarp.count_at (I := fun _ => CpCount) (c := isCp)
    (fun e h => by
      unfold isCp at h
      split at h
      · exact .inl ⟨_, ‹_›⟩
      · cases h)
    (fun b => by simp [CpCount, inPkt])
    (fun _ _ _ _ _ _ _ hev hub _ hm h => cp_step hev hub hm h) hp hX hg hw k b d n hσ hub

/-! ### Tensor copies -/

/-- The elections before a tensor copy on the barrier at offset `o`. -/
def tcPts (o : Nat) : List Nat :=
  (List.finRange 7).flatMap fun t => if taOff t = o then [tePc t 1, tePc t 2] else []

/-- One at a copy site of the barrier at offset `o`. -/
def pendTc (s : Site) (o : Nat) : Nat := if s.tcOff = some o then 1 else 0

/-- The edge check, for each of the four barriers. -/
def tcChk (_ : Bool) (s s' : Site) : Bool :=
  [0, 8, 320, 328].all fun o =>
    match tag s s' with
    | .won pc => pendTc s' o == pendTc s o + (tcPts o).count pc && s.tcOff == none
    | .copy => if s.tcOff.isSome then pendTc s' o == 0 else pendTc s' o == pendTc s o
    | _ => pendTc s' o == pendTc s o && s.tcOff == none

theorem tc_edges : Edges tcChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state, for the barrier at offset `o`. -/
def TcCount (o : Nat) (dn : D × (Cnt → Nat)) (N : Nat) : Prop :=
  N + pendTc dn.1.site o = ((tcPts o).map fun pc => dn.2 (.won pc)).sum

theorem tc_loc' (hp : Pre p L m) (t : Fin 7) (c : Fin 2) {v : V} {kk : Fin 2} :
    smLoc L g (rv p L g w ⟨.tc t c, v, kk⟩ (tcBar t).1) (tcBar t).2 = bl L g (taOff t) := by
  fin_cases t
  · exact smLoc_sb hp 0 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)
  · exact smLoc_sb hp 8 (by norm_num)
  · exact smLoc_sb hp 328 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)
  · exact smLoc_sb hp 328 (by norm_num)
  · exact smLoc_addi hp 320 (by norm_num)

theorem tc_step {o : Nat} (ho : o ∈ [0, 8, 320, 328]) (hp : Pre p L m) {dn : D × (Cnt → Nat)}
    {e : Event} {d' : D} {N : Nat}
    (hev : Ev p L g w dn.1 e) (hub : ∀ f, e.kind ≠ .ub f) (hm : Move L g w dn e d')
    (h : TcCount o dn N) :
    TcCount o (d', Code.bump (cls L g) dn.2 e) (N + if isTc L g o e then 1 else 0) := by
  obtain ⟨d, n⟩ := dn
  obtain ⟨-, -, h3, h4⟩ := copy_site hev hub
  simp only at h3 h4
  have hi : (if isTc L g o e then 1 else 0) = pendTc d.site o := by
    by_cases hs : ∃ t c, d.site = .tc t c
    · obtain ⟨t, c, hs⟩ := hs
      obtain ⟨a, s, hk, hb⟩ := h4 t c hs
      have hb' : s.mbar = bl L g (taOff t) := by
        rw [hb]
        obtain ⟨site, v, kk⟩ := d
        simp only at hs
        subst hs
        exact tc_loc' hp t c
      simp [isTc, hk, hb', pendTc, hs, Site.tcOff, bl]
    · have hn : ∀ a s, e.kind ≠ .tensorIssue a s := fun a s hk => hs (h3.mp ⟨a, s, hk⟩)
      have h1 : isTc L g o e = false := by
        unfold isTc
        split
        · exact absurd ‹_› (hn _ _)
        · rfl
      have h2 : d.site.tcOff = none := by
        revert hs
        cases d.site <;> simp [Site.tcOff]
      simp [h1, pendTc, h2]
  have hself : d'.site = d.site → d.site.tcOff = none := by
    intro hs
    by_contra hne
    obtain ⟨t, c, hst⟩ : ∃ t c, d.site = .tc t c := by
      revert hne
      cases d.site <;> simp [Site.tcOff]
    obtain ⟨a, s, hk, -⟩ := h4 t c hst
    have hcl := hm.cnt .copy
    have ht : tag d.site d'.site = .none := by rw [hs, tag_self]
    simp only [ht, Tag.cnt, reduceCtorEq, decide_false] at hcl
    simp [cls, hk] at hcl
  unfold TcCount at h ⊢
  rw [hi]
  simp only [bump_tag hm] at h ⊢
  rcases hm.edge with hs | hs
  · have h0 : pendTc d.site o = 0 := by simp [pendTc, hself hs]
    rw [hs, tag_self, h0]
    rw [h0] at h
    simpa [Tag.cnt] using h
  · have hc := List.all_eq_true.mp (tc_edges.ok hs) o ho
    revert hc h
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.won.injEq, ↓reduceIte,
        Bool.and_eq_true, beq_iff_eq, Nat.add_zero] <;> intro h hc
    case won pc =>
      have h0 : pendTc d.site o = 0 := by simp [pendTc, hc.2]
      rw [sum_map_add, ← h, hc.1, h0]
      omega
    case copy =>
      cases hts : d.site.tcOff with
      | none =>
        have h0 : pendTc d.site o = 0 := by simp [pendTc, hts]
        simp [hts] at hc
        omega
      | some x => simp [hts] at hc; omega
    all_goals
      have h0 : pendTc d.site o = 0 := by simp [pendTc, hc.2]
      omega

/-- **A loader lane's tensor copies on the barrier at offset `o`** at every state. -/
theorem tc_count {o : Nat} (ho : o ∈ [0, 8, 320, 328]) (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) :
    TcCount o (d, LdWarp.lcn n) (((X.tr g).take k).countP (isTc L g o)) :=
  LdWarp.count_at (I := fun _ => TcCount o) (c := isTc L g o)
    (fun e h => by
      unfold isTc at h
      split at h
      · exact .inr ⟨_, _, ‹_›⟩
      · cases h)
    (fun b => by simp [TcCount, pendTc, Site.tcOff])
    (fun _ _ _ _ _ _ _ hev hub _ hm h => tc_step ho hp hev hub hm h) hp hX hg hw k b d n hσ
    hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
