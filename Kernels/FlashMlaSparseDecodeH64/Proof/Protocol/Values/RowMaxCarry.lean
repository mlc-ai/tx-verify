-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Closed
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PmFin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PmRd

@[expose] public section

/-! # The two lanes of a pair carry the same maximum

Lane `g` of warpgroup 0 and its partner `h` fold the same blocks: block `t` of `g` has the exchange
word `w0Loc` of the partner's block `t` (`rmax_pm_peer`) and the other way, so the true maxima the
two finished-block lists carry are equal (`rmax_carry_eq`), and a row without a kept column has no
kept column in the partner either. -/

/-! # The exchange word of a block is the partner's maximum

The exchange load at pc 572 of block `r` of lane `g` closes with the block at the event `K0`, and
the partner's store it read closes the partner's block `r` at `K0'`: the load's word, read as an
extended real (`w0FE`), is the partner's `w0Loc` of that block (`rmax_pm_peer`). -/

/-! # The exchange load returns the partner's value

The load of a lane of warpgroup 0 at pc 572 or 1157 reads the word the partner's store wrote, and
that word is a scalar value, so the load's value (`w0RdVal`) is the word itself (`rmax_read_value`):
at pc 566 the word reads as `w0Loc` of the words of the partner's block that closes after the store
(every store at pc 566 has a closing event after it, as the partner exits: `w0_closed_of_exit`),
at pc 1155 as the partner's carried row sum `w0ESum`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The exchange load reads the partner's value** (valid rows): the load of lane `g` at pc 572 or
1157 after `2 r + 2` barrier-9 events has the value `v` of the partner's store at pc 566 or 1155
after `2 r + 1` of its own, `v` a scalar word that reads as the partner's `w0Loc` (pc 566, with the
closing event of the partner's block) or its `w0ESum` (pc 1155). -/
theorem rmax_read_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) {g k r pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hw : warp L g < 4) (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hpc : pc = 572 ∨ pc = 1157)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2)
    (hrR : r ≤ blocksOf P L (g / L.block)) (hv : W0Trace P X (w0Partner L g))
    (hC : Complete L X) :
    ∃ j f a' ws v, X.get (w0Partner L g, j) = some f ∧ (f.pc = 566 ∨ f.pc = 1155) ∧
      f.kind = .wr a' ws ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) = 2 * r + 1 ∧
      bs = ws.map some ∧ ws = v.toBytes ∧ Scal v ∧ w0RdVal ⟨pc, .rd a bs⟩ = some v ∧
      ((f.pc = 566 ∧ ∃ K0 c0, j < K0 ∧ X.get (w0Partner L g, K0) = some c0 ∧ c0.pc = 1122 ∧
        (w0Fin ((X.tr (w0Partner L g)).take K0)).1 = (w0Fin ((X.tr (w0Partner L g)).take j)).1 ∧
        Rd v (w0Loc P.scale (w0Words (w0Fin ((X.tr (w0Partner L g)).take K0)).2))) ∨
      (f.pc = 1155 ∧ Rd v ((w0ESum (w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take j)).1)
        (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take j)).1).2 : ℝ) : EReal))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨hpt, -, -⟩, hwh, -, -⟩ := w0Partner_facts hp hw hg
  obtain ⟨pcx, hlast⟩ := (hC.1 _ hpt).resolve_left (noCanceled hX _)
  have hcl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 566 →
      ∃ K c, j < K ∧ X.get (w0Partner L g, K) = some c ∧ c.pc = 1122 :=
    fun j f hf hpc => w0_closed_of_exit hp hX hFw hwh hv hlast
      (startup_exit hp hX hFw (by rwa [List.getLast?_eq_getElem?] at hlast)) j f hf
      (by omega) (by omega)
  have hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → (f.pc = 566 ∨ f.pc = 1155) →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) = 2 * r + 1 →
      ws.length = 4 := by
    intro j f a' ws hf hfpc hk _ _
    obtain ⟨v, hv1, -, hv3, -⟩ := peer_word hp hX hFw hnu hwh hv hcl hf hfpc hk
    rw [hv1]
    simp [Value.toBytes, hv3.1]
  obtain ⟨j, f, a', ws, hf, hfpc, hk, hcj, -, hbs⟩ :=
    rmax_read_bytes hp hX hFw hR hw he hpc hcnt hrR
      (fun j f hf _ => ⟨hv.take (j + 1), noUb_kind hnu hf⟩) hlen
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := peer_word hp hX hFw hnu hwh hv hcl hf hfpc hk
  refine ⟨j, f, a', ws, v, hf, hfpc, hk, hcj, hbs, hv1, hv2, ?_, hv4⟩
  rw [hbs, hv1]
  simp only [w0RdVal]
  rw [rebuild_of_scal (by rw [hv3.1]; omega) hv2]
  rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A block's exchange word is the partner's maximum** (complete execution): the exchange load
of lane `g` at pc 572 after `2 r + 2` barrier-9 events (`r` below the CTA's block count) lies in
a block that closes at `K0` with `r` blocks before it, the partner's block `r` closes at `K0'`,
and the word of the first reads as the second's `w0Loc`. -/
theorem rmax_pm_peer (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) {g k r : Nat} {a : Acc}
    {bs : List (Option Byte)} (hw : warp L g < 4) (he : X.get (g, k) = some ⟨572, .rd a bs⟩)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2)
    (hrR : r < blocksOf P L (g / L.block)) (hv : W0Trace P X g)
    (hvh : W0Trace P X (w0Partner L g)) (hC : Complete L X) :
    ∃ K0 K0' c0 c0', k < K0 ∧ X.get (g, K0) = some c0 ∧ c0.pc = 1122 ∧
      (w0Fin ((X.tr g).take K0)).1.length = r ∧
      X.get (w0Partner L g, K0') = some c0' ∧ c0'.pc = 1122 ∧
      (w0Fin ((X.tr (w0Partner L g)).take K0')).1.length = r ∧
      w0FE (w0Words (w0Fin ((X.tr g).take K0)).2).pm =
        w0Loc P.scale (w0Words (w0Fin ((X.tr (w0Partner L g)).take K0')).2) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨hpt, -, -⟩, hwh, -, -⟩ := w0Partner_facts hp hw hg
  obtain ⟨pcx, hlast⟩ := (hC.1 _ hg).resolve_left (noCanceled hX _)
  obtain ⟨K, c, hkK, hK, hKc⟩ := w0_closed_of_exit hp hX hFw hw hv hlast
    (startup_exit hp hX hFw (by rwa [List.getLast?_eq_getElem?] at hlast)) k _ he
    (by show 566 ≤ 572; omega) (by show 572 ≤ 1121; omega)
  obtain ⟨K0, hkK0, -, ⟨c0, hc0, hc0pc⟩, hfirst⟩ := w0_first_close hK hKc hkK
  have hpm := w0_pm_fin hp hX hFw hw (hv.take K0) he rfl rfl hc0 hkK0 hfirst
  have hrd := w0_pm_rd (hv.take (K0 + 1)) hc0 hc0pc
  have hlen : (w0Fin ((X.tr g).take K0)).1.length = r := by
    have hno := w0_noEarly hp hX hFw hnu hw
    rw [w0Fin_length (hno K0), w0Closed_take_eq hkK0.le (fun q hq1 hq2 ev hev => by
      rcases Nat.eq_or_lt_of_le hq1 with rfl | hq
      · rw [he] at hev; cases hev; simp
      · exact hfirst q hq hq2 ev hev), ← w0Fin_length (hno k)]
    exact w0Fin_length_exch hp hX hFw hw he (noUb_kind hnu he) (Or.inl rfl) hcnt
  obtain ⟨j, f, a', ws, v, hf, hfpc, hk, hcj, hbs, hv1, hv2, hrdv, hcase⟩ :=
    rmax_read_value hp hX hFw hnu hR hw he (Or.inl rfl) hcnt hrR.le hvh hC
  rcases hcase with ⟨hf566, K0', c0', hjK, hc0', hc0'pc, hsame, hRd⟩ | ⟨hf1155, -⟩
  · have hlj := w0Fin_length_st hp hX hFw hwh hf (noUb_kind hnu hf) (Or.inl hf566) hcj
    refine ⟨K0, K0', c0, c0', hkK0, hc0, hc0pc, hlen, hc0', hc0'pc, ?_, ?_⟩
    · rw [hsame]; exact hlj
    · simp only [w0RdVal] at hrdv
      have hv' : (rebuild 3 bs).toOption.getD (.pred false) = v := Option.some.inj hrdv
      have hpv := hpm.trans hv'
      have hrd' : ∀ y, Rd (w0Words (w0Fin ((X.tr g).take K0)).2).pm y → Rd v y :=
        fun y h => hpv ▸ h
      exact rd_unique (hrd' _ hrd) hRd
  · exfalso
    have h1 := w0Fin_length_st hp hX hFw hwh hf (noUb_kind hnu hf) (Or.inr hf1155) hcj
    have h2 := w0_len_epi hp hX hFw hwh hf (noUb_kind hnu hf) (Or.inl hf1155)
    have h3 : blocksOf P L (w0Partner L g / L.block) = blocksOf P L (g / L.block) := by
      rw [(w0Partner_facts hp hw hg).2.2.1]
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The partner of the partner is the lane itself. -/
theorem w0Partner_partner (hp : Pre P L m) {g : Nat} (hw : warp L g < 4) (hg : g < L.threads) :
    w0Partner L (w0Partner L g) = g := by
  obtain ⟨-, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hb : L.block = 384 := by have := hp.block; omega
  have hlt : g % 384 < 128 := by
    simp only [warp, tidOf_x_eq hp] at hw
    omega
  rw [hb] at hdiv hmod
  generalize w0Partner L g = h at hdiv hmod ⊢
  unfold w0Partner
  rw [hb, hmod, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  omega

/-- **Block `t` of a lane and of its partner** (complete execution): at prefixes of the two lanes
with more than `t` finished blocks (`t` below the block count), entry `t` of the finished blocks
exists in both, and the exchange word of the lane's block reads as the `w0Loc` of the partner's. -/
theorem rmax_block_pair (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) {x kx ky t : Nat}
    (hw : warp L x < 4) (hg : x < L.threads) (hv : W0Trace P X x)
    (hvh : W0Trace P X (w0Partner L x)) (hC : Complete L X)
    (hlx : t < (w0Fin ((X.tr x).take kx)).1.length)
    (hly : t < (w0Fin ((X.tr (w0Partner L x)).take ky)).1.length)
    (ht : t < blocksOf P L (x / L.block)) :
    ∃ sx sy, (w0Fin ((X.tr x).take kx)).1[t]? = some sx ∧
      (w0Fin ((X.tr (w0Partner L x)).take ky)).1[t]? = some sy ∧
      w0FE (w0Words sx).pm = w0Loc P.scale (w0Words sy) := by
  obtain ⟨⟨hpt, -, -⟩, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hcl : w0Closed ((X.tr x).take kx) = (w0Fin ((X.tr x).take kx)).1.length :=
    (w0Fin_length (w0_noEarly hp hX hFw hnu hw kx)).symm
  have hcl' : w0Closed ((X.tr (w0Partner L x)).take ky) =
      (w0Fin ((X.tr (w0Partner L x)).take ky)).1.length :=
    (w0Fin_length (w0_noEarly hp hX hFw hnu hwh ky)).symm
  obtain ⟨K, c, hKc, hKpc, hct⟩ := w0_close_idx (l := (X.tr x).take kx) (t := t) (by omega)
  have hKk : K < kx := by
    have := (List.getElem?_eq_some_iff.mp hKc).1
    simp only [List.length_take] at this
    omega
  have hK : X.get (x, K) = some c := by
    rw [List.getElem?_take_of_lt hKk] at hKc
    exact hKc
  have hlK : (w0Fin ((X.tr x).take K)).1.length = t := by
    rw [w0Fin_length (w0_noEarly hp hX hFw hnu hw K), ← hct, List.take_take,
      Nat.min_eq_left hKk.le]
  obtain ⟨k, a, bs, hkK, hget, hcnt⟩ := w0_load_of_close hp hX hFw hw hnu (noUb_kind hnu hK)
    (hv.take K) hK hKpc
  rw [hlK] at hcnt
  obtain ⟨K0, K0', c0, c0', hkK0, hc0, hc0pc, hlen0, hc0', hc0'pc, hlen0', hpm⟩ :=
    rmax_pm_peer hp hX hFw hnu hR hw hget hcnt ht hv hvh hC
  have hK0 : K0 < kx := by
    by_contra hge
    have := w0Closed_mono (l := X.tr x) (le_of_not_gt hge)
    rw [← w0Fin_length (w0_noEarly hp hX hFw hnu hw K0), hlen0] at this
    omega
  have hK0' : K0' < ky := by
    by_contra hge
    have := w0Closed_mono (l := X.tr (w0Partner L x)) (le_of_not_gt hge)
    rw [← w0Fin_length (w0_noEarly hp hX hFw hnu hwh K0'), hlen0'] at this
    omega
  refine ⟨_, _, ?_, ?_, hpm⟩
  · have := w0Fin_block_of_close hp hX hFw hw hc0 hc0pc hK0 hnu
    rwa [hlen0] at this
  · have := w0Fin_block_of_close hp hX hFw hwh hc0' hc0'pc hK0' hnu
    rwa [hlen0'] at this

/-- **The two lanes of a pair carry the same true maximum** (complete execution): at the epilogue
loads (pc 1157) of lane `g` and its partner, the maxima of their finished blocks are equal. -/
theorem rmax_carry_eq (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) {g k k' : Nat} {e e' : Event}
    (hw : warp L g < 4) (hv : W0Trace P X g) (hvh : W0Trace P X (w0Partner L g))
    (hC : Complete L X) (he : X.get (g, k) = some e) (hpc : e.pc = 1157)
    (he' : X.get (w0Partner L g, k') = some e') (hpc' : e'.pc = 1157) :
    w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 =
      w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take k')).1 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨hpt, -, -⟩, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hpp := w0Partner_partner hp hw hg
  have hlx := w0_len_epi hp hX hFw hw he (noUb_kind hnu he) (Or.inr hpc)
  have hly := w0_len_epi hp hX hFw hwh he' (noUb_kind hnu he') (Or.inr hpc')
  rw [show w0Partner L g / L.block = g / L.block from hdiv] at hly
  let term : List Event → EReal := fun seg =>
    max (w0Loc P.scale (w0Words seg)) (w0FE (w0Words seg).pm)
  have hfold : ∀ bs : List (List Event), w0MxCarry P.scale bs = (bs.map term).foldl max ⊥ := by
    intro bs
    unfold w0MxCarry
    rw [List.foldl_map]
  have hmap : ((w0Fin ((X.tr g).take k)).1.map term) =
      ((w0Fin ((X.tr (w0Partner L g)).take k')).1.map term) := by
    refine List.ext_getElem? fun t => ?_
    by_cases ht : t < blocksOf P L (g / L.block)
    · obtain ⟨sg, sh, h1, h2, h3⟩ := rmax_block_pair hp hX hFw hnu hR hw hg hv hvh hC
        (kx := k) (ky := k')
        (by rw [hlx]; exact ht) (by rw [hly]; exact ht) ht
      have ht' : t < blocksOf P L (w0Partner L g / L.block) := by rw [hdiv]; exact ht
      obtain ⟨sh', sg', h1', h2', h3'⟩ := rmax_block_pair hp hX hFw hnu hR hwh hpt hvh
        (by rw [hpp]; exact hv) hC (kx := k') (ky := k) (by rw [hly]; exact ht)
        (by rw [hpp, hlx]; exact ht) ht'
      rw [hpp] at h2'
      rw [h2] at h1'
      rw [h1] at h2'
      cases h1'
      cases h2'
      simp only [List.getElem?_map, h1, h2]
      simp only [Option.map_some, term]
      rw [h3, h3', max_comm]
    · have h1 : (w0Fin ((X.tr g).take k)).1[t]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      have h2 : (w0Fin ((X.tr (w0Partner L g)).take k')).1[t]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      simp [List.getElem?_map, h1, h2]
  rw [hfold, hfold, hmap]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
