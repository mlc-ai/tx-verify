-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Lemmas.Tmem.AccessClass
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Win
public import Kernels.TmlFa4Fwd.Proof.Protocol.O.Obj
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.AccBar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRStub

@[expose] public section

/-! # A successful final O poll observes every MMA of the CTA done

A successful parity-0 poll of the final O barrier of stage `st` of an MMA's CTA follows a stage
commit (`o_commit_exists`), whose notification it observes (`o_hist`,
`MbarOneShot.Hist.observes_arrive`). The commit tracks the MMA: both are the MMA warp's winner's
(`win_lane`), and the MMA precedes the commit (`post_states`: after the commit the lane issues
nothing). So the poll observes the MMA's completion (`mma_observed`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A recorded commit notification's rank was notified. -/
theorem notified_of_record (hX : Consistent L kernel Assumptions.all m X) {o : Loc}
    {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects o) {c : EvId} {rank : Fin 16}
    (hid : r.id = .async c (.tcNotify rank)) : rank ∈ X.tcNotified c := by
  have ha := ((hX.tma.2.2.1 o).2.1 r hr).1
  rw [hid] at ha
  simp only [AsyncCopy.objectAction] at ha
  cases he : X.get c with
  | none => simp [he] at ha
  | some ev =>
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp only [he, reduceCtorEq] at ha
    case tc k =>
      cases k <;> simp only [reduceCtorEq] at ha
      case commit sp =>
        split_ifs at ha with hc
        exact hc.2

/-- An MMA kind. -/
def IsMmaK : Kind → Prop
  | .tc (.mma ..) => True
  | _ => False

set_option maxHeartbeats 8000000 in
theorem mma_win_site {d : Mma.D} {pc : Nat} {k : Kind} (hk : IsMmaK k)
    (hev : Mma.Ev p L g d ⟨pc, k⟩) : winSite d.site = true := by
  have hacc : IsAcc k := by
    revert hk; cases k <;> (try cases ‹TcKind›) <;> simp [IsMmaK, IsAcc]
  obtain ⟨s, v⟩ := d
  cases s
  all_goals first | rfl | skip
  all_goals exfalso
  all_goals simp only [Mma.Ev] at hev
  all_goals (try exact (epi_noacc hacc (‹Epilogue.Ev _ _ _ _ _› : Epilogue.Ev p L g _ _)).elim)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsMmaK]

set_option maxHeartbeats 8000000 in
theorem mma_issue_site {d : Mma.D} {pc : Nat} {k : Kind} (hk : IsMmaK k)
    (hev : Mma.Ev p L g d ⟨pc, k⟩) :
    (∃ b j, d.site = .qk b j) ∨ ∃ b j, d.site = .pv b j := by
  have hacc : IsAcc k := by
    revert hk; cases k <;> (try cases ‹TcKind›) <;> simp [IsMmaK, IsAcc]
  obtain ⟨s, v⟩ := d
  cases s
  case qk b j => exact .inl ⟨b, j, rfl⟩
  case pv b j => exact .inr ⟨b, j, rfl⟩
  all_goals exfalso
  all_goals simp only [Mma.Ev] at hev
  all_goals (try exact (epi_noacc hacc (‹Epilogue.Ev _ _ _ _ _› : Epilogue.Ev p L g _ _)).elim)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsMmaK]

set_option maxHeartbeats 8000000 in
theorem soft_nomma {d : Softmax.D} {pc : Nat} {k : Kind} (hk : IsMmaK k)
    (hev : Softmax.Ev p L g d ⟨pc, k⟩) : False := by
  have hacc : IsAcc k := by
    revert hk; cases k <;> (try cases ‹TcKind›) <;> simp [IsMmaK, IsAcc]
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  all_goals simp only [Softmax.Ev] at hev
  all_goals (try exact (epi_noacc hacc (‹Epilogue.Ev _ _ _ _ _› : Epilogue.Ev p L g _ _)).elim)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsMmaK, Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
theorem corr_nomma {d : Correction.D} {pc : Nat} {k : Kind} (hk : IsMmaK k)
    (hev : Correction.Ev p L g d ⟨pc, k⟩) : False := by
  have hacc : IsAcc k := by
    revert hk; cases k <;> (try cases ‹TcKind›) <;> simp [IsMmaK, IsAcc]
  obtain ⟨s, v, kk⟩ := d
  cases s
  all_goals simp only [Correction.Ev] at hev
  all_goals (try exact (epi_noacc hacc (‹Epilogue.Ev _ _ _ _ _› : Epilogue.Ev p L g _ _)).elim)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsMmaK, Correction.rdOrUb]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

set_option maxHeartbeats 8000000 in
/-- **An MMA is issued from a winning state of the MMA warp.** -/
theorem mma_issue_state {f pc : Nat} {dd : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (g, f) = some ⟨pc, .tc (.mma dd sp acc mask)⟩) :
    ∃ d n, Frame.stateAt (thread p L) X g f = some (some (Mma.minj p L g d n)) ∧
      JR p L g (Mma.minj p L g d n) ∧ winSite d.site = true := by
  have hk : IsMmaK (.tc (.mma dd sp acc mask)) := trivial
  have hacc : IsAcc (.tc (.mma dd sp acc mask)) := trivial
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he (by intro f hf; cases hf)
  rcases σ1 with s | ⟨i, d⟩
  · exact (start_noacc hJ hacc hev).elim
  cases i with
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exfalso
      rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> cases hk'
    · exact ⟨d, n, hσ, hJ, mma_win_site hk hev⟩
  | epilogue => exact (epi_noacc hacc hev).elim
  | loader b => exact (ld_noacc hacc hev).elim
  | softmax => exact (soft_nomma hk hev.1).elim
  | correction =>
    exact (corr_nomma hk (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h))).elim
  | stub r =>
    exact (jr_stub hJ).elim

set_option maxHeartbeats 8000000 in
/-- **A successful final O poll of an MMA's CTA observes the MMA's completion.** -/
theorem mma_observed {i : EvId} (hi : Tmem.Access.IsMma X i) {st : Fin 2} {h k pc : Nat}
    {acq : Bool} {ws : MbarScope}
    (hw : X.get (h, k) = some ⟨pc, .wait (obj L i.1 (oOff st)) 0 true acq ws⟩) :
    AsyncCopy.AsyncObserved X i .mmaDone (h, k) acq ws := by
  obtain ⟨zi, fi⟩ := i
  obtain ⟨dd, sp, accm, mask, pci, hei⟩ := hi
  obtain ⟨⟨zc, jc⟩, pcc, s, rank, hc, ht⟩ := o_commit_exists hp hX hFw hw
  obtain ⟨σc, hσc, hJc, hcta, hc2⟩ := o_event hp hX hFw (g := zi) hc ⟨rank, ht⟩
    (by intro c h; cases h)
  have hobj : obj L zc (oOff st) = obj L zi (oOff st) := by simp only [obj, hcta]
  have hH := o_hist hp hX hFw (z := zc) hc (hobj ▸ ht)
  rw [hobj] at hH
  have hU := hH.observes_arrive hX (List.mem_singleton_self _) hw
  -- the commit's lane is the MMA's, after it
  rcases hc2 with ⟨dc, nc, spc, rfl, ⟨c, hcv, hsc⟩, -⟩ | ⟨d, n, ok, -, -, hk⟩
  swap; · cases hk
  obtain ⟨di, ni, hσi, hJi, hwi⟩ := mma_issue_state hp hX hFw hei
  have hzi := Frame.lt_of_get hX hei
  have hzc := Frame.lt_of_get hX hc
  have hw12 : SameWarp L zc zi := ⟨⟨hzc, hzi, hcta⟩, by
    have : zc % L.block / 32 = 12 := jr_mma hJc
    have : zi % L.block / 32 = 12 := jr_mma hJi
    omega⟩
  have hzz := win_lane hX hw12 hσc hσi (by rw [hsc]; rfl) hwi
  subst hzz
  have hcc : c = ⟨10 + st.val, by omega⟩ := Fin.ext hcv
  rw [hcc] at hsc
  have hfi : fi < jc := by
    by_contra hle
    rcases Nat.lt_or_ge jc fi with hlt | hge
    · have hfl : fi ≤ (X.tr zc).length :=
        (List.getElem?_eq_some_iff.mp (show (X.tr zc)[fi]? = _ from hei)).1.le
      obtain ⟨d2, n2, h2, hp2⟩ := post_states hσc hsc fi hlt hfl _ hσi
      simp only [Mma.minj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
        true_and] at h2
      obtain ⟨rfl, -⟩ := h2
      have hev := (Mma.mfired hp hX hei hσi).1
      rcases mma_issue_site (k := .tc (.mma dd sp accm mask)) trivial hev with
        ⟨b, j, hs⟩ | ⟨b, j, hs⟩ <;> rw [hs] at hp2 <;> cases hp2
    · have : fi = jc := by omega
      subst this
      rw [hei] at hc
      cases hc
  have hU' := hU
  obtain ⟨ii, jj, r, w, phase, hr, hid, -⟩ := hU'
  have hnot := notified_of_record hX (List.mem_of_getElem? hr) hid
  exact ⟨_, _, ⟨(zc, jc), s, rank, rfl, ⟨rfl, hfi, .inl ⟨_, _, _, _, _, hei⟩, s, _, hc⟩, ⟨_, hc⟩,
    hobj ▸ ht, hnot⟩, ⟨⟨_, _, hw⟩, hU⟩⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
