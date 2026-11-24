-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
public import Lemmas.Flow.NotTensor
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.BiasAcq
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QPar
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaArr
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaBudget
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' TMA arrivals, copies and polls, counted

An expect-tx arrival of a loader lane on a Q or bias full barrier expects 32768 bytes and follows
one more successful poll of the empty barrier than its earlier arrivals (`ld_tma_arr`); a tensor
copy completing on it has fewer earlier copies than twice those polls (`ld_tma_copy`). Both are of a
lane of warp 14 that won an election. The polls of the empty barriers have the parity of the lane's
earlier ones plus one (`ld_tma_empty_par`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem off_mem {o : Nat} (ho : LdTmaOff o) : o ∈ [0, 8, 320, 328] := by
  rcases ho with rfl | rfl | rfl | rfl <;> simp

private theorem ld_open (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {e : Event} {l : Loc}
    (he : X.get (h, k) = some e) (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    ∃ b d n kk A, Frame.stateAt (thread p L) X h k = some (some (LdWarp.linj p L h b d n)) ∧
      n .ub = 0 ∧ Loader.wOf b = Prologue.warpIndex L h ∧
      Loader.RefRing p L h (Loader.wOf b) d kk A ∧
      Loader.Ev p L h (Loader.wOf b) d e ∧ LdUse p L h (Loader.wOf b) kk A d e l := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact absurd (start_mbar hev hi.2 hm) (fun ⟨c, hc⟩ => hni c hc)
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, -⟩ := hJl.refE
  exact ⟨b, d, n, kk, A, hσ, h0, hR.1, hRing, hev, ld_use hp hRing hev hm⟩

/-- A lane with a counted won election won one. -/
private theorem won_of_sum {σ : (glued p L h).D} {n : Cls → Nat} {l : List Nat}
    (hσ : Frame.stateAt (thread p L) X h k = some (some (σ, n)))
    (hs : 1 ≤ (l.map fun pc => n (.load (.won pc))).sum) :
    ∃ j pc mask inst, j < k ∧ X.get (h, j) = some ⟨pc, .elect mask inst (laneOf L h)⟩ := by
  obtain ⟨pcw, hpos⟩ : ∃ pc, 0 < n (.load (.won pc)) := by
    by_contra hno
    have hz : ∀ pc, n (.load (.won pc)) = 0 := fun pc =>
      Nat.eq_zero_of_not_pos fun h => hno ⟨pc, h⟩
    simp [hz] at hs
  obtain ⟨j, hj, ⟨pcf, kd⟩, hf, hcl⟩ := exists_of_count hσ (c := .load (.won pcw)) hpos
  cases kd <;> simp [cls, Loader.cls] at hcl
  rename_i mask inst ld
  obtain ⟨-, rfl⟩ := hcl
  exact ⟨j, pcf, mask, inst, hj, hf⟩

private theorem tx_ta (t : Fin 7) {w : Nat} {v : Loader.V} {kk : Fin 2} :
    (truncBits 32 (Loader.rv p L h w ⟨.ta t, v, kk⟩ (Loader.taRegs (.ta t)).2.2)).toNat =
      32768 := by
  have hc : (truncBits 32 (Arith32.i32 32768)).toNat = 32768 := by decide
  fin_cases t <;> exact hc

private theorem tx_da {w : Nat} {v : Loader.V} {kk : Fin 2} :
    (truncBits 32 (Loader.rv p L h w ⟨.da, v, kk⟩ (Loader.taRegs .da).2.2)).toNat = 32768 := by
  have hc : (truncBits 32 (Arith32.i32 32768)).toNat = 32768 := by decide
  exact hc

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A loader lane's expect-tx arrival.** -/
theorem ld_tma_arr (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {o : Nat} (ho : LdTmaOff o) {pc tx : Nat} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h o) tx 1 true sc⟩) :
    Prologue.warpIndex L h = 14 ∧ tx = 32768 ∧
      arrivals (obj L h o) ((X.tr h).take k) + 1 ≤
        okPolls (obj L h (o + 16)) ((X.tr h).take k) ∧
      ∃ j pc' mask inst, j < k ∧
        X.get (h, j) = some ⟨pc', .elect mask inst (laneOf L h)⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, d, n, kk, A, hσ, hub, hb, hR, hev, hu⟩ := ld_open hp hX hFw hw he
    (l := obj L h o) rfl (fun _ h => by cases h)
  have hsite : d.site.isTma = true ∧ Loader.pendingArr d.site = some o ∧ tx = 32768 := by
    cases hu with
    | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | arrive _ _ _ _ hk
    | tc _ _ _ _ _ _ hk _ => cases hk
    | ta t tx' hs hl hk =>
      have hoo := (obj_off hl).2
      refine ⟨by rw [hs]; rfl, by rw [hs]; simp only [Loader.pendingArr]; rw [hoo], ?_⟩
      obtain ⟨site, v, k2⟩ := d
      simp only at hs
      subst hs
      simp only [Loader.Ev, Kind.arrive.injEq] at hev
      exact hev.2.1.trans (tx_ta t)
    | da tx' hs hl hk =>
      have hoo := (obj_off hl).2
      refine ⟨by rw [hs]; rfl, by rw [hs]; simp only [Loader.pendingArr]; rw [hoo], ?_⟩
      obtain ⟨site, v, k2⟩ := d
      simp only at hs
      subst hs
      simp only [Loader.Ev, Kind.arrive.injEq] at hev
      exact hev.2.1.trans tx_da
  obtain ⟨h1, h2, h3⟩ := hsite
  have harr := Loader.tma_arr hp hX hg hw hσ hub o (off_mem ho)
  have hbud := (Loader.tma_budget hp hX hg hw hσ hub o (off_mem ho)).1
  simp only [Loader.pendAt, h2, ite_true] at harr
  have hca : arrivals (obj L h o) ((X.tr h).take k) = n (.load (.arrive (obj L h o))) :=
    count hσ (.load (.arrive (obj L h o)))
  have hcp : okPolls (obj L h (o + 16)) ((X.tr h).take k) =
      n (.load (.acquire (obj L h (o + 16)))) := count hσ (.load (.acquire (obj L h (o + 16))))
  have harr' : n (.load (.arrive (obj L h o))) + 1 =
      ((Loader.tmaArrPts o).map fun pc => n (.load (.won pc))).sum := harr
  have hbud' : ((Loader.tmaArrPts o).map fun pc => n (.load (.won pc))).sum +
      Loader.budArr d.site o ≤ n (.load (.acquire (obj L h (o + 16)))) := hbud
  exact ⟨hb ▸ hR.tma h1, h3, by omega, won_of_sum hσ (l := Loader.tmaArrPts o) (by omega)⟩

/-- **A loader lane's tensor copy.** -/
theorem ld_tma_copy (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {o : Nat} (ho : LdTmaOff o) {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (h, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L h o) :
    Prologue.warpIndex L h = 14 ∧
      ((X.tr h).take k).countP (issuesTo (obj L h o)) + 1 ≤
        2 * okPolls (obj L h (o + 16)) ((X.tr h).take k) ∧
      ∃ j pc' mask inst, j < k ∧
        X.get (h, j) = some ⟨pc', .elect mask inst (laneOf L h)⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, d, n, kk, A, hσ, hub, hb, hR, -, hu⟩ := ld_open hp hX hFw hw he
    (l := obj L h o) hm (fun _ h => by cases h)
  have hsite : d.site.isTma = true ∧ d.site.tcOff = some o := by
    cases hu with
    | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | arrive _ _ _ _ hk
    | ta _ _ _ _ hk | da _ _ _ hk => cases hk
    | tc t c a' s hs hl hk hb' =>
      have hoo := (obj_off hl).2
      exact ⟨by rw [hs]; rfl, by rw [hs]; simp only [Loader.Site.tcOff]; rw [hoo]⟩
  obtain ⟨h1, h2⟩ := hsite
  have hcp := Loader.tc_count (off_mem ho) hp hX hg hw hσ hub
  have hbud := (Loader.tma_budget hp hX hg hw hσ hub o (off_mem ho)).2
  simp only [Loader.TcCount, Loader.pendTc, h2, ite_true] at hcp
  have hca : okPolls (obj L h (o + 16)) ((X.tr h).take k) =
      n (.load (.acquire (obj L h (o + 16)))) := count hσ (.load (.acquire (obj L h (o + 16))))
  have hcp' : ((X.tr h).take k).countP (issuesTo (obj L h o)) + 1 =
      ((Loader.tcPts o).map fun pc => n (.load (.won pc))).sum := hcp
  have hbud' : ((Loader.tcPts o).map fun pc => n (.load (.won pc))).sum +
      Loader.budCp d.site o ≤ 2 * n (.load (.acquire (obj L h (o + 16)))) := hbud
  exact ⟨hb ▸ hR.tma h1, by omega, won_of_sum hσ (l := Loader.tcPts o) (by omega)⟩

/-- A poll of a Q or bias empty barrier is a lane's of warp 14, with the parity of its earlier ones
plus one. -/
theorem ld_tma_empty_par (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {o : Nat} (ho : LdTmaOff o) {pc par : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait (obj L h (o + 16)) par ok acq sc⟩) :
    Prologue.warpIndex L h = 14 ∧
      par % 2 = (okPolls (obj L h (o + 16)) ((X.tr h).take k) + 1) % 2 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, d, n, kk, A, hσ, hub, hb, hR, hev, hu⟩ := ld_open hp hX hFw hw he
    (l := obj L h (o + 16)) rfl (fun _ h => by cases h)
  have hc : okPolls (obj L h (o + 16)) ((X.tr h).take k) =
      n (.load (.acquire (obj L h (o + 16)))) := count hσ (.load (.acquire (obj L h (o + 16))))
  rw [hc]
  have h1 : (truncBits 32 (Arith32.i32 1)).toNat % 2 = 1 := by decide
  cases hu with
  | slot _ _ _ _ hl _ | dw _ _ _ hl _ =>
    exfalso
    have := (obj_off hl).2
    unfold LdTmaOff at ho
    omega
  | arrive _ _ _ _ hk | ta _ _ _ _ hk | da _ _ _ hk | tc _ _ _ _ _ _ hk _ => cases hk
  | tw t ok' hs hl hk =>
    have hoo := (obj_off hl).2
    have h14 : Loader.wOf b = 14 := hR.tma (by rw [hs]; rfl)
    refine ⟨hb ▸ h14, ?_⟩
    have hbi := Loader.bias_acq hp hX hg hw hσ hub h14
    have hq := Loader.q_acq hp hX hg hw hσ hub
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, hpar, -, -, -⟩ := hk
    obtain ⟨site, v, k'⟩ := d
    simp only at hs
    subst hs
    rw [hpar]
    have hbq : ∀ a : Nat, (truncBits 32 (BitVec.ofNat 64 (a % 2))).toNat % 2 = a % 2 := by
      intro a
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;> decide
    fin_cases t <;> simp [Loader.twOff] at hoo <;> subst hoo
    · have h0 := hq 16 (by simp)
      rw [show n (.load (.acquire (obj L h (0 + 16)))) = _ from h0]
      simp [Loader.qAcq]
      exact h1
    · have h0 := (hbi false).1 0 rfl
      rw [show n (.load (.acquire (obj L h (320 + 16)))) = _ from h0]
      exact h1
    · have h0 := hq 24 (by simp)
      rw [show n (.load (.acquire (obj L h (8 + 16)))) = _ from h0]
      simp [Loader.qAcq]
      exact h1
    · have h0 := (hbi true).1 0 rfl
      rw [show n (.load (.acquire (obj L h (328 + 16)))) = _ from h0]
      exact h1
    · have h0 := (hbi false).2 0 rfl
      change (truncBits 32 v.bq0).toNat % 2 % 2 = _
      rw [show v.bq0 = _ from h0, hbq, Nat.mod_mod]
      rfl
    · have h0 := (hbi true).2 0 rfl
      change (truncBits 32 v.bq1).toNat % 2 % 2 = _
      rw [show v.bq1 = _ from h0, hbq, Nat.mod_mod]
      rfl
    · have h0 := (hbi false).2 0 rfl
      change (truncBits 32 v.bq0).toNat % 2 % 2 = _
      rw [show v.bq0 = _ from h0, hbq, Nat.mod_mod]
      rfl
  | dq ok' hs hl hk =>
    have hoo := (obj_off hl).2
    have h14 : Loader.wOf b = 14 := hR.tma (by rw [hs]; rfl)
    refine ⟨hb ▸ h14, ?_⟩
    have ho8 : o = 8 := by omega
    subst ho8
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, hpar, -, -, -⟩ := hk
    obtain ⟨site, v, k'⟩ := d
    simp only at hs
    subst hs
    rw [hpar]
    have h0 := (Loader.q_par hp hX hg hw hσ hub h14).2 rfl
    have hbq : ∀ a : Nat, (truncBits 32 (BitVec.ofNat 64 (a % 2))).toNat % 2 = a % 2 := by
      intro a
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;> decide
    change (truncBits 32 v.qp).toNat % 2 % 2 = _
    rw [show v.qp = _ from h0, hbq, Nat.mod_mod]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
