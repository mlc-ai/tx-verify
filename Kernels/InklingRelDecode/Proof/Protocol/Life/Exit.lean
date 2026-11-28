-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Def
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Kernel.SharedEnabled
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.BarPc
import Kernels.InklingRelDecode.Proof.Common.Export.EpiPoll
import Kernels.InklingRelDecode.Proof.Lib.BarSchedule
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll
import Lemmas.Async.AsyncOrigins
import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! # What follows an observing poll or the final poll in a lane that exited

A poll of an exited CTA's lane is a canonical spin, so the lane's exit resumes from it
(`Resumes.of_spin`): an update the poll observes is finished (`observed_finished`). A default
lane exits only after its final poll of `o_final` (`exit_poll`): its last rendezvous is at pc 2850
(a data lane never has the worker's final rendezvous), and the epilogue's events after the poll
site follow a successful poll. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.AsyncCopy

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An event that is no exit is followed, in its lane, by the lane's exit** once its CTA
exited. -/
theorem exit_after (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) (hne : e.kind ≠ .exit) (hx : CtaExited L X (i.1 / L.block)) :
    ∃ finish, OwnerExit L X (i.1 / L.block) finish ∧ TraceBefore X i finish := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨tag, hl⟩ := hx i.1 hg rfl
  rw [List.getLast?_eq_getElem?] at hl
  have hGet : X.get (i.1, (X.tr i.1).length - 1) = some ⟨tag, .exit⟩ := hl
  have hi := PTX.len_of_get he
  have hLast := PTX.len_of_get hGet
  have hlt : i.2 < (X.tr i.1).length - 1 := by
    by_contra hn
    have hIndex : i = (i.1, (X.tr i.1).length - 1) := Prod.ext rfl (by omega)
    have hEq := Option.some.inj ((hIndex ▸ he).symm.trans hGet)
    exact hne (congrArg Event.kind hEq)
  exact ⟨(i.1, (X.tr i.1).length - 1), ⟨hg, rfl, tag, hGet⟩, rfl, hlt, hLast⟩

/-- **An update a poll observes has an enabling chain to the polling lane's exit**: the poll is a
canonical spin that resumes the lane's exit, after the object's order from the update to the
poll. -/
theorem observed_enabled (hX : Consistent L kernel Assumptions.all m X) {ref} {w : EvId}
    {mb : Loc} {acq : Bool} {scope : MbarScope} (hw : WaitObserves X ref w mb acq scope)
    (hx : CtaExited L X (w.1 / L.block)) :
    SharedEnabled L kernel Assumptions.all X (w.1 / L.block) ref := by
  obtain ⟨⟨tag, parity, he⟩, i, j, ri, rj, _, hi, hid, _, hj, hjd, _, _, hij, _, _, _⟩ := hw
  have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hp
  obtain ⟨finish, hExit, htrace⟩ := exit_after hX he (by simp) hx
  obtain ⟨_, hspin⟩ := (Lib.poll_site hX he).2
  exact ⟨hp, finish, hExit, .inl ⟨.mbar mb, trivial,
    .head (.inr (.inl ⟨rfl, rfl, i, j, ri, rj, hi, hid, hj, hjd, hij⟩))
      (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (.single (DepStep.of_resumes L
        (Resumes.of_spin he hspin htrace.1 htrace.2.1 htrace.2.2))))⟩⟩

/-- **An update a poll observes finishes before the polling lane's exit.** -/
theorem observed_finished (hX : Consistent L kernel Assumptions.all m X) {ref} {w : EvId}
    {mb : Loc} {acq : Bool} {scope : MbarScope} (hw : WaitObserves X ref w mb acq scope)
    (hx : CtaExited L X (w.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X ref (w.1 / L.block) :=
  (observed_enabled hX hw hx).finished

private theorem getD_lt {l : List Nat} (h : ∀ x ∈ l, x < 2853) (k : Nat) : l.getD k 0 < 2853 := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hk)

private theorem preloadBar_lt (v : Nat) : Lib.preloadBar v < 2853 := by
  have all : ∀ l ∈ [[192, 201, 212, 222, 227], [236, 243, 254, 264, 269],
      [278, 285, 296, 306, 311]], ∀ x ∈ l, x < 2853 := by decide
  unfold Lib.preloadBar
  cases hk : [[192, 201, 212, 222, 227], [236, 243, 254, 264, 269],
    [278, 285, 296, 306, 311]][v / 5]? with
  | none => simp [List.getD_eq_getElem?_getD, hk]
  | some l =>
    simp only [List.getD_eq_getElem?_getD, hk, Option.getD_some]
    exact getD_lt (all l (List.mem_of_getElem? hk)) _

private theorem dataBar_lt (p lim t : Nat) : Lib.dataBar p lim t < 2853 := by
  have rb (u : Nat) : Lib.roundBar u < 2853 := getD_lt (by decide) _
  unfold Lib.dataBar Lib.dataTail
  split
  · exact getD_lt (by decide) _
  · split
    · exact preloadBar_lt _
    · split_ifs <;> first | omega | exact rb _

/-- **A default lane exits after a successful poll of `o_final`.** -/
theorem exit_poll (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {g kx pc : Nat} (he : X.get (g,kx) = some ⟨pc,.exit⟩)
    (hd : g % L.block < 128) :
    ∃ j < kx, ∃ l q ac sc, X.get (g,j) = some ⟨2565,.wait l q true ac sc⟩ := by
  obtain ⟨u,p,hu,get,ord⟩ := Export.exit_final_bar hp hX he
  have fin := (Export.final_late hp hX get).mpr ord
  simp only [Lib.finalSync, Bool.or_eq_true, beq_iff_eq] at fin
  rcases fin with rfl | rfl
  · obtain ⟨j,l,q,ac,sc,hj,gj⟩ := Export.epilogue_event_poll hp hX hf get (fun f => by simp)
      (by omega) (by omega)
    exact ⟨j, by omega, l, q, ac, sc, gj⟩
  · rcases Export.data_bar_pc hp hX hf get hd with h | ⟨h, -⟩
    · have := dataBar_lt (Iface.preloadCount Q L (g / L.block)) (Lib.blocksOf Q L (g / L.block))
        (((X.tr g).take u).countP (Execution.isBarId 0) +
          ((X.tr g).take u).countP (Execution.isBarId 1) -
          ((X.tr g).take u).countP (fun e => e.pc == 2326))
      omega
    · omega

/-- **Lane zero of an exited CTA exits after a successful poll of `o_final`.** -/
theorem final_wait (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {c : Nat} (hc : c < L.grid) (hx : CtaExited L X c) :
    ∃ jw kx l q ac sc, jw < kx ∧ OwnerExit L X c (c * L.block, kx) ∧
      X.get (c * L.block, jw) = some ⟨2565, .wait l q true ac sc⟩ := by
  have hb : L.block = 256 := hp.block
  have hh : c * L.block < L.threads := by
    unfold Launch.threads
    exact Nat.mul_lt_mul_of_pos_right hc (by omega)
  have hhc : c * L.block / L.block = c := Nat.mul_div_cancel _ (by omega)
  have hhd : c * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
  obtain ⟨pcx, hl⟩ := hx _ hh hhc
  rw [List.getLast?_eq_getElem?] at hl
  obtain ⟨jw, hjk, l, q, ac, sc, hpoll⟩ := exit_poll hp hX hf hl hhd
  exact ⟨jw, _, l, q, ac, sc, hjk, ⟨hh, hhc, pcx, hl⟩, hpoll⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
