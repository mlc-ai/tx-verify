-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.EmptyObj
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Parity
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Lemmas.Protocol.PollLe
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The loader lanes' polls of the empty barriers

A loader lane's successful poll of an empty barrier has the parity of its earlier successful polls
of it plus one (`ld_empty_par`: at a `slot` site of packet `j = pkOf per v k`, the count is
`ringCnt j (j % 3) = j / 3` by the reference invariant's closed form, the parity `(j / 3 + 1) % 2`
by `slot_par`; at the drain's `dw j`, for packet `A + j`). So its successful polls are at most
the empty object's phase plus one (`ld_empty_okPolls`, `MbarRing.okPolls_le_phase`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A loader lane's successful poll of an empty barrier has the parity of its count plus
one.** -/
theorem ld_empty_par (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat}
    (ho : EmptyOff o) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    (hg : g < L.threads) {k pc par : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (obj L g o) par true acq sc⟩) :
    par % 2 = (okPolls (obj L g o) ((X.tr g).take k) + 1) % 2 := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hg he
    (fun f hf => by cases hf)
  have hJ' : JR p L g (σ1, n) := hJ
  have hub0 : n .ub = 0 := ub_zero hX he hσ
  have h8 : ¬ Prologue.warpIndex L g < 8 := by omega
  have h12 : Prologue.warpIndex L g ≠ 12 := by omega
  have h13 : Prologue.warpIndex L g ≠ 13 := by omega
  simp only [JR_eq, h8, ite_false] at hJ'
  unfold RefAll at hJ'
  simp only [h12, h13, hw, ite_true, ite_false] at hJ'
  rcases σ1 with s | ⟨i, d⟩
  · -- the startup polls no barrier
    have hEv : Startup.Ev L g s ⟨pc, .wait (obj L g o) par true acq sc⟩ := hev
    obtain ⟨site, x1, x2, x3⟩ := s
    exfalso
    cases site with
    | enter r => exact jr_start_site hJ r rfl
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | elect j =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  cases i with
  | loader b =>
    obtain ⟨hwb, hR⟩ := hJ'
    obtain ⟨kk, A, hRing, hCnt⟩ := (hR hub0).1.refE
    rw [← hwb] at hRing
    have hcl := count hσ (.load (.acquire (obj L g o)))
    have hok : okPolls (obj L g o) ((X.tr g).take k) = n (.load (.acquire (obj L g o))) := by
      rw [← hcl]
      rfl
    rw [hok]
    have hEv : Loader.Ev p L g (Loader.wOf b) d ⟨pc, .wait (obj L g o) par true acq sc⟩ := hev
    obtain ⟨site, v, k'⟩ := d
    cases site <;> simp only [Loader.Ev] at hEv
    case slot per vv =>
      obtain ⟨ok, hk⟩ := hEv
      simp only [Kind.wait.injEq] at hk
      obtain ⟨hl, hpar, -, -, -⟩ := hk
      rw [Loader.slot_loc hp hRing] at hl
      have hlo := (obj_inj (L := L) (g := g) hl).symm
      have hcm := hCnt.commit
      simp only [Loader.arrAt, Loader.inPkt, Nat.add_zero, LdWarp.lcn] at hcm
      have hc := Loader.acq_ring hp hX hg hw hσ hub0
        ⟨Loader.pkOf per vv kk % 3, Nat.mod_lt _ (by decide)⟩
      simp only at hc
      subst hlo
      simp only [LdWarp.lcn] at hc
      rw [show n (.load (.acquire (obj L g (56 + 8 * (Loader.pkOf per vv kk % 3))))) = _ from hc,
        hpar, Nat.mod_mod, Loader.slot_par hRing]
      simp only [Loader.acqOff, hcm, Nat.add_zero, Loader.ringCnt_mod]
    case dw jj =>
      obtain ⟨ok, hk⟩ := hEv
      simp only [Kind.wait.injEq] at hk
      obtain ⟨hl, hpar, -, -, -⟩ := hk
      rw [Loader.dw_loc hp jj hRing] at hl
      have hlo := (obj_inj (L := L) (g := g) hl).symm
      have hcm := hCnt.commit
      simp only [Loader.arrAt, Loader.inPkt, Nat.add_zero, LdWarp.lcn] at hcm
      have hc := Loader.acq_ring hp hX hg hw hσ hub0
        ⟨(A + jj.val) % 3, Nat.mod_lt _ (by decide)⟩
      simp only at hc
      subst hlo
      simp only [LdWarp.lcn] at hc
      rw [show n (.load (.acquire (obj L g (56 + 8 * ((A + jj.val) % 3))))) = _ from hc,
        hpar, Nat.mod_mod, Loader.dw_par hRing]
      simp only [Loader.acqOff, hcm, Nat.add_zero, Loader.ringCnt_mod]
    case tw t =>
      exfalso
      obtain ⟨ok, hk⟩ := hEv
      simp only [Kind.wait.injEq] at hk
      obtain ⟨hl, -⟩ := hk
      rw [Loader.tw_loc hp t] at hl
      have := obj_inj (L := L) (g := g) hl
      rcases ho with rfl | rfl | rfl <;> fin_cases t <;> simp_all [Loader.twOff]
    case dq =>
      exfalso
      obtain ⟨ok, hk⟩ := hEv
      simp only [Kind.wait.injEq] at hk
      obtain ⟨hl, -⟩ := hk
      have := obj_inj (L := L) (g := g) (hl.trans (Loader.smLoc_addi hp 24 (by norm_num)))
      omega
    all_goals (try simp only [Epilogue.Ev, Loader.Site.toE] at hEv)
    all_goals (try split at hEv)
    all_goals (try shape_destruct hEv)
    all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)
  | _ => exact (by simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] : False).elim

set_option maxHeartbeats 4000000 in
/-- **A loader lane's successful polls of an empty barrier are at most its phase plus one.** -/
theorem ld_empty_okPolls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat}
    (ho : EmptyOff o) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    (hg : g < L.threads) {before : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (obj L g o)) (X.objects (obj L g o)).length =
      some before) :
    okPolls (obj L g o) (X.tr g) ≤ before.phase + 1 := by
  obtain ⟨q, hq, hc⟩ := empty_init ho
  have hinit : PairTmaRing.InitFirst X (obj L g o) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hc] at this
  have hni := AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) (obj L g o)
  exact MbarRing.okPolls_le_phase hX le_rfl (PairTmaRing.poll_clean hX hinit hni) hni
    (fun k pc par acq sc he => ld_empty_par hp hX hFw ho hw hg he) hst

end
end PTX.Kernels.TmlFa4Fwd.Proof
