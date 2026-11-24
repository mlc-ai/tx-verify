-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.InputBar
import Kernels.TmlFa4Fwd.Proof.Loader.Export.QIssue
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Lemmas.Order.OrderWaits
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.Tensor.TensorTransfer
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q stages' copies and operand reads are ordered

A Q stage is filled once, by two copies into its two boxes (`q_copy`), so two copies that write one
byte are one (`q_copy_unique`). Every QK MMA of the stage follows the poll that observes both copies
(`q_copy_read`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The copy that writes a byte of box `q` of Q stage `st`.** -/
theorem q_copy {st q : Fin 2} {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) {x y z : Nat} {l : Loc}
    (hl : TensorCopy.writeLoc s x y z = some l) (hcta : l.cta = g / L.block)
    (hlo : L.sharedBase + (3072 + 32768 * st.val + 16384 * q.val) ≤ l.addr)
    (hhi : l.addr < L.sharedBase + (3072 + 32768 * st.val + 16384 * q.val) + 16384) :
    ∃ c, i = (tmaLane L X g, c) ∧ s.mbar = obj L g (8 * st.val) ∧
      ((X.tr (tmaLane L X g)).take c).countP (issuesTo (obj L g (8 * st.val))) = q.val := by
  obtain ⟨h, c⟩ := i
  obtain ⟨hw, -⟩ := input_box hp hX hFw he
  obtain ⟨j, org, -, hs⟩ := ld_input_bar hp hX hFw hw he
  obtain ⟨m1, m2, m3, m4, -⟩ := input_map p j
  have hbx : l.cta = h / L.block ∧ L.sharedBase + (Loader.inputSite j).sharedOffset ≤ l.addr ∧
      l.addr < L.sharedBase + (Loader.inputSite j).sharedOffset + 16384 := by
    subst hs
    have hf2 : (Loader.inputMap p (Loader.inputSite j)).format.bytes = 2 := by rw [m3]; rfl
    obtain ⟨b1, b2⟩ := box_lt m1 m2 hf2 m4 hl
    obtain ⟨slot, -, rfl⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨rfl, b1, b2⟩
  obtain ⟨c1, c2, c3⟩ := hbx
  have hc : h / L.block = g / L.block := c1.symm.trans hcta
  have hst := st.isLt
  have hq := q.isLt
  have hbar : s.mbar = obj L h (8 * st.val) := by
    rw [hs]
    show obj L h (siteBar j) = _
    have h2 := Nat.mod_lt j.val (show 0 < 2 by decide)
    congr 1
    rcases siteBar_slot j with (⟨h1, h3⟩ | ⟨h1, h3⟩) | (⟨h1, h3⟩ | ⟨h1, h3⟩) <;> omega
  have hoo : obj L h (8 * st.val) = obj L g (8 * st.val) := obj_cta hc _
  have hbar' := hbar.trans hoo
  obtain ⟨hlane, -⟩ := tma_copy hp hX hFw (g := g) (q_tmaOff st) he hbar'
  subst hlane
  obtain ⟨-, -, jw, pcw, maskw, instw, -, hjw⟩ := ld_tma_copy hp hX hFw hw (q_tmaOff st) he hbar
  obtain ⟨j', org', hs', hoff'⟩ := ld_q_copy hp hX hFw hw
    (fun k pc mask inst ld hk => tmaLane_won hX hjw hk) st he hbar
  obtain ⟨-, -, hle⟩ := Loader.q_issue hp hX hFw (o := 8 * st.val) (by omega) hw he hbar
  have hjj : (Loader.inputSite j').sharedOffset = (Loader.inputSite j).sharedOffset := by
    have := congrArg (fun s : TensorCopy.Spec => s.sharedBase.addr) (hs'.symm.trans hs)
    simp only [inputSpec] at this
    omega
  rw [hoo] at hoff' hle
  refine ⟨c, rfl, hbar', ?_⟩
  simp only at hoff' hle
  have h2 := Nat.mod_lt j.val (show 0 < 2 by decide)
  rcases siteBar_slot j with (⟨h1, h3⟩ | ⟨h1, h3⟩) | (⟨h1, h3⟩ | ⟨h1, h3⟩) <;> omega

omit hp hX hFw in
/-- The box of a byte of the Q stages. -/
theorem q_box {l : Loc} (h1 : L.sharedBase + 3072 ≤ l.addr)
    (h2 : l.addr < L.sharedBase + 68608) : ∃ st q : Fin 2,
      L.sharedBase + (3072 + 32768 * st.val + 16384 * q.val) ≤ l.addr ∧
      l.addr < L.sharedBase + (3072 + 32768 * st.val + 16384 * q.val) + 16384 := by
  refine ⟨⟨(l.addr - L.sharedBase - 3072) / 32768, by omega⟩,
    ⟨(l.addr - L.sharedBase - 3072) / 16384 % 2, by omega⟩, ?_, ?_⟩ <;> simp only <;> omega

/-- **Two copies that write one byte of a Q stage are one.** -/
theorem q_copy_unique {i i' : EvId} {pc pc' a a' : Nat} {s s' : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) (he' : X.get i' = some ⟨pc', .tensorIssue a' s'⟩)
    {x y z x' y' z' : Nat} {l : Loc} (hw : TensorCopy.writeLoc s x y z = some l)
    (hw' : TensorCopy.writeLoc s' x' y' z' = some l) (h1 : L.sharedBase + 3072 ≤ l.addr)
    (h2 : l.addr < L.sharedBase + 68608) :
    (Ref.async i (.write (.load x y z))) = .async i' (.write (.load x' y' z')) := by
  obtain ⟨st, q, hlo, hhi⟩ := q_box h1 h2
  have hcta : l.cta = l.cta * L.block / L.block := by rw [hp.block]; omega
  obtain ⟨c, rfl, m1, p1⟩ := q_copy hp hX hFw he hw hcta hlo hhi
  obtain ⟨c', rfl, m2, p2⟩ := q_copy hp hX hFw he' hw' hcta hlo hhi
  have hcc : c = c' := nthEv_unique (p := issuesTo (obj L (l.cta * L.block) (8 * st.val))) he
    (by simp [issuesTo, m1]) he' (by simp [issuesTo, m2]) (p1.trans p2.symm)
  subst hcc
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he'
  obtain ⟨-, -, rfl⟩ := he'
  obtain ⟨s1, hs1, hl1⟩ := Option.map_eq_some_iff.mp hw
  obtain ⟨s2, hs2, hl2⟩ := Option.map_eq_some_iff.mp hw'
  have hslot : s1 = s2 :=
    TensorTransfer.sharedByte_injective _ _ (congrArg Loc.addr (hl1.trans hl2.symm))
  obtain ⟨a1, a2, a3⟩ := TensorCopy.slotAt_coordinates hs1
  obtain ⟨b1, b2, b3⟩ := TensorCopy.slotAt_coordinates hs2
  subst hslot
  rw [← a1, ← a2, ← a3, ← b1, ← b2, ← b3]

/-- **A copy that writes a byte of a Q stage is before every QK MMA's read of the byte.** -/
theorem q_copy_read {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) {x y z : Nat} {l : Loc}
    (hw : TensorCopy.writeLoc s x y z = some l) {gm k st u idx : Nat} {j : Fin 8}
    (hR : Tm.Qk L X gm k st u j) (hst : st < 2)
    (hr : AsyncCovers X (gm, k) (.mmaRead false idx) l) (hcta : l.cta = gm / L.block)
    (hlo : L.sharedBase + 3072 + 32768 * st ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 3072 + 32768 * st + 32768) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async (gm, k) (.mmaRead false idx)) :=
    by
  obtain ⟨q, hq1, hq2⟩ : ∃ q : Fin 2,
      L.sharedBase + (3072 + 32768 * st + 16384 * q.val) ≤ l.addr ∧
      l.addr < L.sharedBase + (3072 + 32768 * st + 16384 * q.val) + 16384 := by
    refine ⟨⟨(l.addr - L.sharedBase - 3072 - 32768 * st) / 16384, by omega⟩, ?_, ?_⟩ <;>
      simp only <;> omega
  obtain ⟨c, rfl, hm, hcnt⟩ := q_copy hp hX hFw (st := ⟨st, hst⟩) (q := q) (g := gm) he hw hcta
    hq1 hq2
  simp only at hm hcnt
  obtain ⟨pcm, da, db, hme⟩ := hR.issue
  have hgm := Frame.lt_of_get hX hme
  have hmma : X.MmaIssue (gm, k) (128 * st) _ _ _ := ⟨pcm, hme⟩
  have hwm := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hmma⟩).1
  obtain ⟨cm, hin, -, hcm, hfull, -⟩ := qHandoff hp hX hFw (tmaBytes hp hX hFw) gm hgm ⟨st, hst⟩
  have hcme : gm = cm := hcm hmma ⟨hgm, rfl, hwm⟩
  subst hcme
  have hq := hR.q
  have hpoll : 0 + 1 ≤ okPolls (qF L gm ⟨st, hst⟩) ((X.tr gm).take k) := by
    show 1 ≤ okPolls (obj L gm (8 * st)) _
    rw [show obj L gm (8 * st) = Tm.bar L (gm / L.block) (8 * st) from rfl, hq]
  obtain ⟨jw, pcw, par, acq, sc, hjk, hwe, hwo⟩ := nth_poll hpoll
  have hacq : acq = true := by
    obtain ⟨-, hu⟩ := bar_use (o := 8 * st) hp hX hFw hwe rfl (fun _ h => by cases h)
    cases hu with
    | mmaPoll _ _ _ hk => cases hk; rfl
    | ldPoll _ _ _ _ hk | epiPoll _ _ _ _ hk | corrPoll _ _ _ hk | softPoll _ _ _ _ _ hk =>
      cases hk; rfl
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  subst hacq
  obtain ⟨i1, pci, al, sp, he1, hm1, hc1, -, hW⟩ := hfull hwe hwo q
  have hii : i1 = c := nthEv_unique (p := issuesTo (qF L gm ⟨st, hst⟩)) he1
    (by simp [issuesTo, hm1]) he (by simp [issuesTo, qF, hm]) (by
      rw [hc1]
      simp only [qF] at hcnt ⊢
      rw [hcnt]
      omega)
  subst hii
  obtain ⟨-, hU⟩ := id hW
  obtain ⟨ii, jj, r, w, phase, hrec, hid, -⟩ := hU
  have hpres := object_record_present hX.tma (List.mem_of_getElem? hrec)
  rw [hid] at hpres
  obtain ⟨o, ho, hn⟩ := id hpres
  obtain ⟨⟨addr, pco, hio⟩, -⟩ := hX.tensor _ o ho
  have hos : o.spec = sp := by
    rw [he1] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  have hty := (tmaLane_in (X := X) hp gm).1
  have hsame : SameCta L (tmaLane L X gm) gm := ⟨Frame.lt_of_get hX he1, hgm, hty⟩
  refine ⟨.inl hsame, .direct ⟨cover_load he hw, hr, .inl ⟨(gm, jw), .inr ⟨sc, ⟨_, _, ⟨rfl, o,
    addr, ho, ⟨pco, hio⟩, by rw [hos]; exact hm1, hn⟩, hW⟩, ScopesMeet.of_sameCta hsame⟩, ?_⟩⟩⟩
  exact .single (.inl (po_of_source_not_access rfl hjk
    (List.getElem?_eq_some_iff.mp (show (X.tr gm)[k]? = _ from hme)).1 (by simp [hwe, Event.acc])))

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
