-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxCarry
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockTail
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Closed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # The row sum the epilogue reads from its partner

An event of the epilogue of lane `g` (pc 1178 to 1839) has the lane's load at pc 1157 before it in
the same block, with no closing event between. That load returned the partner's store at pc 1155,
a word that reads as `w0ESum rP lP` with `rP` the true maximum the partner's finished blocks carry
(equal to the lane's: `rmax_carry_eq`) and `lP` its carried sum over all its blocks
(`rmax_peer_sum`: `lP = (w0Carry (w0Fin ((X.tr peer).take kq)).1).2` at a prefix `kq` of the partner
with all of the CTA's blocks finished, so that both sums are over the same blocks). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The peer's row sum at an epilogue event** (complete execution). -/
theorem rmax_peer_sum (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) {g k : Nat} {e : Event}
    (hw : warp L g < 4) (hv : W0Trace P X g) (hvh : W0Trace P X (w0Partner L g))
    (hC : Complete L X) (he : X.get (g, k) = some e) (h1 : 1157 < e.pc) (h2 : e.pc < 1840) :
    ∃ kp f a bs rP kq e', X.get (g, kp) = some f ∧ f.pc = 1157 ∧ f.kind = .rd a bs ∧ kp < k ∧
      (∀ q, kp < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) ∧
      X.get (w0Partner L g, kq) = some e' ∧ e'.pc = 1157 ∧
      (w0Fin ((X.tr (w0Partner L g)).take kq)).1.length = blocksOf P L (g / L.block) ∧
      Rd ((rebuild 3 bs).toOption.getD (.pred false))
        ((w0ESum rP (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).2 : ℝ) : EReal) ∧
      w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 = rP ∧
      w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1 = rP ∧
      (w0Fin ((X.tr g).take k)).1.length = blocksOf P L (g / L.block) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨hpt, -, -⟩, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => hnu ⟨(g, k), e.pc, f, by rw [← h]; exact he⟩
  obtain ⟨-, -, hs3⟩ := w0_boundSeen hp hX hFw hw he hub (by omega) (hv.take k)
  obtain ⟨f, hfm, hf1157⟩ := hs3 h1 h2
  have hfs : f ∈ (w0Scan ((X.tr g).take k)).2 := by rw [← w0Fin_snd]; exact hfm
  obtain ⟨i, hi, hci⟩ := w0Scan_snd_idx hfs
  have hik : i < k := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, i) = some f := by
    rw [List.getElem?_take_of_lt hik] at hi
    exact hi
  have hat : MbarRow.Wg0At L g f.pc := ⟨hw, by omega, by omega⟩
  obtain ⟨-, hrd⟩ := wg0_peerPlace hp hX hFw hget (noUb_kind hnu hget) hat (by omega)
  obtain ⟨a, bs, hkd, -⟩ := hrd (by omega)
  have hfirst : ∀ q, i < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122 := by
    have hci' : w0Closed ((X.tr g).take k) = w0Closed ((X.tr g).take i) := by
      rw [List.take_take, Nat.min_eq_left hik.le] at hci
      exact hci.symm
    exact fun q hq1 hq2 ev hev => w0_noClose_between hci' q hq1.le hq2 ev hev
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨ex, -, -, hfin⟩ := w0_tail hp hX hFw hw (hv.take _) hget (by omega) (by omega)
    (lo := 1178) (by omega)
    (fun e' he' hu => by
      rcases Wg0.w0_next_1157 hp hX hFw hw hget hf1157 he' hu hv with h | h <;> omega)
    hik hKl hfirst
  have hlen := w0_len_epi hp hX hFw hw hget (noUb_kind hnu hget) (Or.inr hf1157)
  have hcnt := w0_cnt_exch hp hX hFw hw hget (noUb_kind hnu hget) (Or.inr hf1157)
  rw [hlen] at hcnt
  obtain ⟨pcf, kd⟩ := f
  simp only at hf1157 hkd
  subst hf1157 hkd
  obtain ⟨j, f', a', ws, v, hf', hfpc, hk', hcj, hbs, hv1, hv2, hrdv, hcase⟩ :=
    rmax_read_value hp hX hFw hnu hR hw hget (Or.inr rfl) hcnt le_rfl hvh hC
  rcases hcase with ⟨hf566, -⟩ | ⟨hf1155, hRd⟩
  · exfalso
    have h3 := w0Fin_length_st hp hX hFw hwh hf' (noUb_kind hnu hf') (Or.inl hf566) hcj
    have h4 := w0_len_lt hp hX hFw hwh hf' (noUb_kind hnu hf') (Or.inl hf566)
    rw [show w0Partner L g / L.block = g / L.block from hdiv] at h4
    omega
  obtain ⟨pcx, hlast⟩ := (hC.1 _ hpt).resolve_left (noCanceled hX _)
  have h103 : 103 ≤ pcx :=
    startup_exit hp hX hFw (by rwa [List.getLast?_eq_getElem?] at hlast)
  obtain ⟨e1, he1⟩ := w0_not_last hp hX hFw hwh hlast h103 hf' (by omega)
  have he1pc := Wg0.w0_next_1155 hp hX hFw hwh hf' hf1155 he1 (noUb_kind hnu he1)
    (hvh.take (j + 1))
  obtain ⟨e2, he2⟩ := w0_not_last hp hX hFw hwh hlast h103 he1 (by omega)
  have he2pc := Wg0.w0_next_1156 hp hX hFw hwh he1 he1pc he2 (noUb_kind hnu he2) hvh
  have hl2 : j + 2 < (X.tr (w0Partner L g)).length :=
    (List.getElem?_eq_some_iff.mp he2).1
  obtain ⟨ex', -, -, hfin'⟩ := w0_tail hp hX hFw hwh (hvh.take _) hf' (by omega) (by omega)
    (lo := 1156) (by omega) (fun e' he' _ => by rw [he1] at he'; cases he'; omega)
    (show j < j + 2 by omega) hl2
    (fun q hq1 hq2 ev hev => by
      obtain rfl : q = j + 1 := by omega
      rw [he1] at hev; cases hev; omega)
  have hcar := rmax_carry_eq hp hX hFw hnu hR hw hv hvh hC hget rfl he2 he2pc
  have hl := w0_len_epi hp hX hFw hwh he2 (noUb_kind hnu he2) (Or.inr he2pc)
  refine ⟨i, ⟨1157, .rd a bs⟩, a, bs,
    w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take (j + 2))).1, j + 2, e2,
    hget, rfl, rfl, hik, hfirst, he2, he2pc, ?_, ?_, ?_, rfl, ?_⟩
  · rw [hl, hdiv]
  · have hv' : (rebuild 3 bs).toOption.getD (.pred false) = v := Option.some.inj hrdv
    rw [hv', hfin']
    exact hRd
  · rw [hfin, hcar]
  · rw [hfin]; exact hlen

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
