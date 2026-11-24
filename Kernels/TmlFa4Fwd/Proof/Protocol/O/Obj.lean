-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Top.JRMma
import Kernels.TmlFa4Fwd.Proof.Top.JRLoader
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites

@[expose] public section

/-! # Who names the final O barriers

The MMA warp's last commits `cm 10` and `cm 11` target the objects at shared offsets 144 and 152
(`Mma.cm_loc`, `cmO`); the correction lanes poll them at `fw 0 0` and `fw 1 0` with parity 0
(`pollOff`, `pollPar`); no other event of the shape tables names them (`o_use`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The final O barrier of stage `st`: offset 144 or 152. -/
abbrev oOff (st : Fin 2) : Nat := 144 + 8 * st.val

theorem corr_arrOff_o (s : Correction.Site) (st : Fin 2) : Correction.arrOff s ≠ oOff st := by
  have h := List.all_eq_true.mp (show Correction.allSites.all (fun s =>
    Correction.arrOff s != 144 && Correction.arrOff s != 152) = true by decide +kernel) s
    (Correction.mem_allSites s)
  fin_cases st <;> simp_all [oOff]

theorem corr_pollOff_o {s : Correction.Site} {st : Fin 2} (h : Correction.pollOff s = oOff st) :
    s = .fw st 0 := by
  have h1 := List.all_eq_true.mp (show Correction.allSites.all (fun s =>
    (Correction.pollOff s != 144 || s == .fw 0 0) &&
      (Correction.pollOff s != 152 || s == .fw 1 0)) = true by decide +kernel) s
    (Correction.mem_allSites s)
  fin_cases st <;> simp_all [oOff]

theorem cmO_o {r : Nat} {c : Fin 12} {st : Fin 2} (h : Mma.cmO r c = oOff st) :
    c.val = 10 + st.val := by
  fin_cases c <;> fin_cases st <;> simp [Mma.cmO, oOff] at h ⊢ <;> omega

/-- The MMA warp's polls are at offsets up to 120. -/
abbrev Le120 (o : Nat) : Prop := o ≤ 120

theorem mma_wt_le (hp : Pre p L m) {v : Mma.V} {n : Mma.Cnt → Nat} {r : Nat} {w : Bool}
    (k : Fin 10) (hQ : Mma.RefQ p L g (Mma.Site.wt k).ord v n r w) :
    IsObjIn L g (smLoc L g (Mma.wtOp L v k).1 0) Le120 := by
  fin_cases k <;> simp only [Mma.wtOp, Fin.isValue, Fin.reduceFinMk]
  · rw [Mma.smLoc_sbW hp 0 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [Mma.smLoc_addi hp 32 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [Mma.smLoc_addi hp 8 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [(hQ.regs (by decide)).1, Mma.smLoc_slot hp (by omega)]
    exact ⟨_, by simp only [Le120]; omega, rfl⟩
  · rw [Mma.smLoc_addi hp 96 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [(Mma.slot1_eq (hQ.regs (by decide))).1, Mma.smLoc_slot hp (by omega)]
    exact ⟨_, by simp only [Le120]; omega, rfl⟩
  · rw [Mma.smLoc_addi hp 104 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [(hQ.regs (by decide)).1, Mma.smLoc_slot hp (by omega)]
    exact ⟨_, by simp only [Le120]; omega, rfl⟩
  · rw [Mma.smLoc_addi hp 96 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩
  · rw [Mma.smLoc_addi hp 104 (by decide) (by decide)]; exact ⟨_, by decide, rfl⟩

theorem cm_o (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {c : Fin 12}
    {v : Mma.V} {r : Nat} {w : Bool} {n : Mma.Cnt → Nat} {spec : TcCommit.Spec} {k pc : Nat}
    {st : Fin 2} (he : X.get (g, k) = some ⟨pc, .tc (.commit spec)⟩)
    (hm : ∃ rank, TcCommit.target spec rank = some (obj L g (oOff st)))
    (hev : spec.mbar = smLoc L g (Mma.cmOp L v c).1 (Mma.cmOp L v c).2 ∧ spec.group = .one)
    (hQ : Mma.RefQ p L g (Mma.Site.cm c).ord v n r w) : c.val = 10 + st.val := by
  obtain ⟨rank, ht⟩ := hm
  have hl := commit_target hp hX he ht
  have hloc := Mma.cm_loc (g := g) hp c (r := r) (v := v) (fun hc => hQ.regs (by
    fin_cases c <;> simp_all [Mma.Site.ord]))
  rw [hev.1, hloc] at hl
  have hc : Mma.cmO r c = oOff st := by
    simp only [obj, Mma.bl, Loc.mk.injEq, true_and] at hl
    omega
  exact cmO_o hc

set_option maxHeartbeats 8000000 in
/-- **An MMA code state that names a final O barrier** is at its commit. -/
theorem mma_o (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Mma.D} {n : Mma.Cnt → Nat} {e : Event} {st : Fin 2} (he : X.get (g, k) = some e)
    (hQ0 : Mma.RefCounts p L g (d, n)) (hev : Mma.Ev p L g d e)
    (hm : MbarOf e (obj L g (oOff st))) :
    ∃ c : Fin 12, c.val = 10 + st.val ∧ d.site = .cm c ∧ ∃ s, e.kind = .tc (.commit s) := by
  have hne : ∀ o, o ≤ 120 → obj L g (oOff st) ≠ Mma.bl L g o := by
    intro o ho h
    simp only [obj, Mma.bl, Loc.mk.injEq, true_and, oOff] at h
    omega
  revert hne
  obtain ⟨r, w, hQ⟩ := hQ0
  obtain ⟨site, v⟩ := d
  unfold Mma.Ev at hev
  split at hev
  all_goals first
    | (exfalso; epi_none; done)
    | skip
  all_goals obtain ⟨pc, kind⟩ := e
  all_goals revert hQ
  all_goals cases kind <;> (try cases ‹TcKind›) <;> simp only [MbarOf] at hm <;>
    (try simp_all)
  all_goals (intro hQ; intros)
  all_goals first
    | (obtain ⟨o, ho, hl⟩ := mma_wt_le hp _ hQ; exact ⟨o, ho, hl⟩)
    | exact ⟨_, by split <;> decide, Mma.mw_loc hp _⟩
    | exact cm_o hp hX he hm hev hQ
    | skip
  all_goals obtain ⟨pc, kind⟩ := e
  all_goals revert hQ
  all_goals cases kind <;> (try cases ‹TcKind›) <;> simp only [MbarOf] at hm <;>
    (try simp_all)
  all_goals (intro hQ; intros)
  all_goals first
    | (obtain ⟨o, ho, hl⟩ := mma_wt_le hp _ hQ; exact ⟨o, ho, hl⟩)
    | exact ⟨_, by split <;> decide, Mma.mw_loc hp _⟩
    | (rename_i c _ _ _ _
       obtain ⟨rank, ht⟩ := hm
       have hl := commit_target hp hX he ht
       have hloc := Mma.cm_loc hp c (r := r) (v := v) (fun hc => hQ.regs (by
         fin_cases c <;> simp_all [Mma.Site.ord]))
       rw [hev.1, hloc] at hl
       have hc : Mma.cmO r c = oOff st := by
         simp only [obj, Mma.bl, Loc.mk.injEq, true_and] at hl
         omega
       exact cmO_o hc)
    | skip

set_option maxHeartbeats 8000000 in
/-- **Who names a final O barrier**: an event of a followed lane that names the final O barrier
of stage `st` of lane `g`'s CTA and is no initialization is a lane of that CTA, either the MMA
warp's commit at `cm (10 + st)` or a correction lane's poll at `fw st 0` with parity 0. -/
theorem o_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h k : Nat}
    {σ : (thread p L h).D} {e : Event} {st : Fin 2} (he : X.get (h, k) = some e)
    (hσ : Frame.stateAt (thread p L) X h k = some (some σ)) (hJ : JR p L h σ)
    (hi : (thread p L h).inv σ) (hev : TEv p L h σ e)
    (hm : MbarOf e (obj L g (oOff st))) (hni : ∀ c, e.kind ≠ .mbInit (obj L g (oOff st)) c) :
    h / L.block = g / L.block ∧
      ((∃ d n s, σ = (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n) ∧ (∃ c : Fin 12, c.val = 10 + st.val ∧
          d.site = .cm c) ∧ e.kind = .tc (.commit s)) ∨
        ∃ d n ok, σ = (.inr ⟨.correction, d⟩, n) ∧ d.site = .fw st 0 ∧
          e.kind = .wait (obj L g (oOff st)) 0 ok true .cta) := by
  obtain ⟨σ1, n⟩ := σ
  have hub0 : n .ub = 0 := ub_zero hX he hσ
  have hoff : ∀ o, obj L g (oOff st) = obj L h o → h / L.block = g / L.block ∧ o = oOff st := by
    intro o hl
    simp only [obj, Loc.mk.injEq, true_and] at hl
    omega
  rcases σ1 with s | ⟨i, d⟩
  · exact absurd (start_mbar hev hi.2 hm) (fun ⟨c, hc⟩ => hni c hc)
  cases i with
  | epilogue =>
    exfalso
    rcases epi_site hev hm with ⟨st', -, hl⟩ | ⟨st', -, hl⟩ <;>
      simp only [Epilogue.readyLoc, Epilogue.freeLoc, obj, Loc.mk.injEq, true_and, oOff] at hl <;>
      omega
  | correction =>
    have hevC := hev.1.data_or_vote.resolve_right (by
      obtain ⟨pc,kind⟩ := e
      rintro ⟨_,_,rfl⟩
      exact hm.elim)
    rcases corr_mbar2 hevC hm with ⟨-, hl, -⟩ | ⟨par, ok, hk, hl, -⟩
    · obtain ⟨-, ho⟩ := hoff _ hl
      exact absurd ho (corr_arrOff_o _ st)
    · obtain ⟨hc, ho⟩ := hoff _ hl
      have hs := corr_pollOff_o ho
      have hev1 := hevC
      obtain ⟨site, v, kk⟩ := d
      change site = _ at hs
      subst hs
      simp only [Correction.Control.D.scheduler, Correction.Ev, Correction.pollPar] at hev1
      obtain ⟨ok', hk'⟩ := hev1
      refine ⟨hc, .inr ⟨_, n, ok', rfl, rfl, ?_⟩⟩
      rw [hk']
      simp only [Correction.bl, obj, Correction.pollOff, hc]
      fin_cases st <;> rfl
  | softmax =>
    exfalso
    obtain ⟨o, ho, hl⟩ := soft_obj hev.1 hm
    obtain ⟨-, ho'⟩ := hoff o hl
    obtain ⟨-, h2⟩ := ho
    simp only [oOff] at ho'
    omega
  | stub r =>
    exact (jr_stub hJ).elim
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exfalso
      obtain ⟨pc, kind⟩ := e
      simp only [TEv, Mma.PreEv] at hev
      cases kind <;> (try cases ‹TcKind›) <;> simp only [MbarOf] at hm <;> simp_all
    · have hR : Mma.Ref p L h (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n) :=
        (jr_mma_ref hJ).2
      have hm' : MbarOf e (obj L h (oOff st)) := by
        obtain ⟨o, -, hl⟩ := mma_obj hp hX he (hR hub0).1 hev hm
        obtain ⟨hc, -⟩ := hoff o hl
        simp only [obj, hc]
        exact hm
      obtain ⟨c, hc10, hs, sp, hk⟩ := mma_o hp hX he (hR hub0).1 hev hm'
      obtain ⟨o, -, hl⟩ := mma_obj hp hX he (hR hub0).1 hev hm
      exact ⟨(hoff o hl).1, .inl ⟨d, n, sp, rfl, ⟨c, hc10, hs⟩, hk⟩⟩
  | loader b =>
    exfalso
    have hR : LdWarp.Ref p L (Prologue.warpIndex L h) h (.inr ⟨.loader b, d⟩, n) :=
      (jr_loader hJ).2
    have hRing := (hR.2 hub0).1.toRefRing
    rw [← hR.1] at hRing
    obtain ⟨o, ho, hl⟩ := ld_obj hp hRing hev hm
    obtain ⟨-, ho'⟩ := hoff o hl
    obtain ⟨-, h2⟩ := ho
    simp only [oOff] at ho'
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
