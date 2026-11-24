-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasNum
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaBudget
public import Lemmas.Order.ElectSiteOrdinal
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's elections before its TMA arrivals

Standalone fact. Every lane of warp 14 makes one election per successful poll of a Q or Bias empty
barrier, at the sites whose winner arrives on the full barrier at `o`, but for the one still to come
at such a site (`elect_num`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The election sites before an arrival on the full barrier at `o`. -/
def arrPcs (o : Nat) (pc : Nat) : Bool := (tmaArrPts o).contains pc

/-- The elections at `arrPcs o`. -/
abbrev arrElect (o : Nat) : Event → Bool := ElectOrd.atSites (arrPcs o)

/-- A site is an election before an arrival on the full barrier at `o`. -/
def isArrE (s : Site) (o : Nat) : Bool :=
  match s with
  | .te t e => taOff t == o && e.val == 0
  | .de => o == 8
  | _ => false

def Site.isEl : Site → Bool
  | .te _ _ | .de => true
  | _ => false

/-- The edge check. -/
def elChk (b : Bool) (s s' : Site) : Bool :=
  b || (s' != s || !s.isEl) && [0, 8, 320, 328].all fun o =>
    budArr s' o + (if isArrE s o then 1 else 0) ==
      budArr s o + (if tag s s' = .acq (o + 16) then 1 else 0)

theorem el_edges : Edges elChk := by unfold Edges AllSites; decide +kernel

theorem el_self : AllSites fun s => [0, 8, 320, 328].all fun o =>
    (!s.isEl || isArrE s o == arrPcs o s.pc) && (s.isEl || !isArrE s o) := by
  unfold AllSites; decide +kernel

variable {p : Params} {L : Launch} {g w : Nat}

/-- An election moves. -/
theorem el_move {d d' : D} {e : Event} (hn : succ p L g w d e = some (some d'))
    (hs : d.site.isEl = true) : d'.site ≠ d.site := by
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [Site.isEl, Bool.false_eq_true] at hs
  case te t i =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
    subst hn
    have hge : ∀ d0 : D, (groupEnd p L g d0 t).site ≠ .te t 2 := by
      intro d0
      fin_cases t <;> simp [groupEnd]
      intro h
      have := (afterTail_aft (p := p) (L := L) (g := g) d0).1
      rw [h] at this
      cases this
    split
    · fin_cases i <;> simp [teElected]
    · fin_cases i <;> simp [teNext]
      exact hge _
  case de =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
    subst hn
    split <;> simp

/-- An election's site. -/
theorem el_site {d : D} {e : Event} (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f) :
    (isElectEv e = true ↔ d.site.isEl = true) ∧
      (d.site.isEl = true → e.pc = d.site.pc) := by
  obtain ⟨site, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site <;> simp only [Ev] at hev
  case te t i =>
    rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
    · exact ⟨by simp [isElectEv, hk, Site.isEl], fun _ => hpc⟩
    · exact absurd hk (hub f)
  case de =>
    rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
    · exact ⟨by simp [isElectEv, hk, Site.isEl], fun _ => hpc⟩
    · exact absurd hk (hub f)
  all_goals refine ⟨?_, fun h => by simp [Site.isEl] at h⟩
  all_goals (try simp only [Epilogue.Ev, Site.toE] at hev)
  all_goals shape_destruct hev
  all_goals simp_all [isElectEv, Site.isEl]

/-- The startup's elections are before the roles. -/
theorem start_el_pc {s : Startup.D} {pc : Nat} {kind : Kind} (hE : Startup.Ev L g s ⟨pc, kind⟩)
    (hen : ∀ r, s.site ≠ .enter r) (hk : isElectEv ⟨pc, kind⟩ = true) : pc ≤ 173 := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | enter r => exact absurd rfl (hen r)
  | sh j =>
    exfalso
    fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨_, _, hk'⟩ := hE <;>
      simp [isElectEv, hk'] at hk
  | fence => exfalso; simp only [Startup.Ev] at hE; simp [isElectEv, hE] at hk
  | bar => exfalso; simp only [Startup.Ev] at hE; simp [isElectEv, hE] at hk
  | elect j =>
    simp only [Startup.Ev] at hE
    rcases hE with ⟨_, _, hpc', hk'⟩ | ⟨_, hk'⟩
    · rw [hpc']
      fin_cases j <;> decide
    · exfalso; simp [isElectEv, hk'] at hk
  | init q =>
    exfalso
    simp only [Startup.Ev] at hE
    rcases hE with ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> simp [isElectEv, hk'] at hk

/-- **The elections before the arrivals** at every state of a lane of warp 14. -/
theorem elect_num {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) {o : Nat} (ho : o ∈ [0, 8, 320, 328]) :
    ElectOrd.siteOrdinal (arrPcs o) X g k + budArr d.site o =
      n (.load (.acquire (bl L g (o + 16)))) := by
  refine LdWarp.step_at (w := 14) (I := fun k dn => ElectOrd.siteOrdinal (arrPcs o) X g k +
    budArr dn.1.site o = dn.2 (.acquire (bl L g (o + 16)))) ?_ ?_ ?_ hp hX hg (.inl rfl) hw
    k b d n hσ hub
  · intro b k n _ _ hst
    have h0 : ElectOrd.siteOrdinal (arrPcs o) X g k = 0 := by
      refine hst _ fun s e hE hen => ?_
      obtain ⟨pc, kind⟩ := e
      rw [Bool.eq_false_iff]
      intro hc
      simp only [ElectOrd.atSites, Bool.and_eq_true] at hc
      obtain ⟨hk, hpc⟩ := hc
      have hlt : pc ≤ 173 := start_el_pc hE hen hk
      have hall : ∀ o ∈ [0, 8, 320, 328], ∀ pc ∈ tmaArrPts o, 173 < pc := by decide
      have := hall o ho pc (by simpa [arrPcs] using hpc)
      omega
    rw [h0]
    rfl
  · intro k b n d e d' he _ _ _ _ _ hev hub hn hm h
    simp only at h ⊢
    have hb : Code.bump (cls L g) (LdWarp.lcn n) e (.acquire (bl L g (o + 16))) =
        LdWarp.lcn n (.acquire (bl L g (o + 16))) +
          if tag d.site d'.site = .acq (o + 16) then 1 else 0 := by
      rw [bump_tag hm]
      cases tag d.site d'.site <;>
        simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
          Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
      case acqRing δ =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        have := Nat.mod_lt (LdWarp.lcn n .commit + δ) (show 0 < 3 by decide)
        have hne : ¬ 56 + 8 * ((LdWarp.lcn n .commit + δ) % 3) = o + 16 := by omega
        simp [hne]
    obtain ⟨h1, h2⟩ := el_site hev hub
    have hself := List.all_eq_true.mp (AllSites.ok el_self d.site) o ho
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hself
    have hq : arrElect o e = isArrE d.site o := by
      cases hel : d.site.isEl with
      | true =>
        have := hself.1.resolve_left (by simp [hel])
        rw [this, arrElect, ElectOrd.atSites, h1.mpr hel, h2 hel, Bool.true_and]
      | false =>
        have := hself.2.resolve_left (by simp [hel])
        rw [this, arrElect, ElectOrd.atSites]
        have : isElectEv e = false := by
          rw [Bool.eq_false_iff]; intro h'; rw [h1.mp h'] at hel; cases hel
        rw [this, Bool.false_and]
    have hstep : ElectOrd.siteOrdinal (arrPcs o) X g (k + 1) =
        ElectOrd.siteOrdinal (arrPcs o) X g k + if isArrE d.site o then 1 else 0 := by
      have he' : (X.tr g)[k]? = some e := he
      unfold ElectOrd.siteOrdinal
      rw [List.take_add_one, he', List.countP_append, ← hq]
      simp [List.countP_cons]
    rw [hb, hstep]
    rcases hm.edge with hs | hs
    · simp only at hs
      have hel : d.site.isEl = false := by
        rw [Bool.eq_false_iff]; exact fun h' => el_move hn h' hs
      have := hself.2.resolve_left (by simp [hel])
      rw [hs, tag_self, this]
      simpa using h
    · have hc := el_edges.ok hs
      simp only [elChk, show not14 14 = false from rfl, Bool.false_or, Bool.and_eq_true] at hc
      have hc := beq_iff_eq.mp (List.all_eq_true.mp hc.2 o ho)
      omega
  · intro k dn hk h
    unfold ElectOrd.siteOrdinal at h ⊢
    rw [List.take_of_length_le (by omega)] at h ⊢
    exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
