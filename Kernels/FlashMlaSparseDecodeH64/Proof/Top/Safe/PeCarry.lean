-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PmValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxCarry
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TcSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MstFin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PmFin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PmRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PoVote

@[expose] public section

/-! # The two lanes of a pair carry the same maximum, from valid prefixes

`W0Under P L X g k`: every event of a lane of warps 0 to 3 below the event `(g, k)` in the tcgen05
order has a valid prefix of its lane through it. At the epilogue's row-sum load of lane `g`
(pc 1157) and the partner's row-sum store (pc 1155) that the load reads, the blocks the two
lanes finished fold to the same true maximum (`w0_carry_eq`): block `t` of each lane has the
exchange word of the other's block `t` (`w0_pm_link`, both ways). -/

/-! # A block's exchange word is the partner's maximum, from valid prefixes

Block `t` of lane `x`, closed within the first `Nx` events, read at its exchange load (pc 572)
the word the partner's store at pc 566 of its block `t` wrote (`w0_pm_peer_read`); the partner's
block `t`, closed within its first `Ny` events, has the words that store reads as the partner's
`w0Loc` (`w0_mst_value_fin`), and the block's `pm` word is the load's value. The proof uses the
prefixes `W0Valid` of the two lanes only (no complete execution), and the guard `W0Below` of the
partner's events below the load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {x : Nat}

/-- **Block `t` of a lane and of its partner** (valid prefixes): the exchange word of the lane's
block `t` reads as the `w0Loc` of the partner's block `t`. -/
theorem w0_pm_link (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L x < 4) {t Nx Ny : Nat} (hax : LaneUbFree X x Nx)
    (hay : LaneUbFree X (w0Partner L x) Ny) (hvx : W0Valid P.scale ((X.tr x).take Nx))
    (hvy : W0Valid P.scale ((X.tr (w0Partner L x)).take Ny))
    (htx : t < (w0Fin ((X.tr x).take Nx)).1.length)
    (hty : t < (w0Fin ((X.tr (w0Partner L x)).take Ny)).1.length)
    (hG : ∀ kt a bs, kt < Nx → X.get (x, kt) = some ⟨572, .rd a bs⟩ →
      W0Below P L X (w0Partner L x) x kt) :
    ∃ sx sy, (w0Fin ((X.tr x).take Nx)).1[t]? = some sx ∧
      (w0Fin ((X.tr (w0Partner L x)).take Ny)).1[t]? = some sy ∧
      w0FE (w0Words sx).pm = w0Loc P.scale (w0Words sy) := by
  have hno : ∀ k, k ≤ Nx → W0NoEarlyClose ((X.tr x).take k) := fun k hk =>
    w0_noEarly_pre hp hX hFw hw (hax.mono hk)
  obtain ⟨K, c, hKc, hKpc, hct⟩ := w0_close_idx (l := (X.tr x).take Nx) (t := t)
    (by rw [← w0Fin_length (hno Nx le_rfl)]; exact htx)
  have hKk : K < Nx := by
    have := (List.getElem?_eq_some_iff.mp hKc).1
    simp only [List.length_take] at this
    omega
  have hK : X.get (x, K) = some c := by
    rw [List.getElem?_take_of_lt hKk] at hKc
    exact hKc
  have hg := Frame.lt_of_get hX hK
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  have hnoh : ∀ k, k ≤ Ny → W0NoEarlyClose ((X.tr (w0Partner L x)).take k) := fun k hk =>
    w0_noEarly_pre hp hX hFw hwh (hay.mono hk)
  have hlK : (w0Fin ((X.tr x).take K)).1.length = t := by
    rw [w0Fin_length (hno K hKk.le), ← hct, List.take_take, Nat.min_eq_left hKk.le]
  obtain ⟨kt, a, bs, hkK, hget, hcnt⟩ := w0_load_of_close hp hX hFw hw
    (hax.mono hKk.le) (NoUbBefore.ne hax hKk hK)
    (Wg0.W0Valid.take_le hvx hKk.le) hK hKpc
  rw [hlK] at hcnt
  have hlkt : (w0Fin ((X.tr x).take kt)).1.length = t :=
    w0Fin_length_exch hp hX hFw hw hget (NoUbBefore.ne hax (by omega) hget) (Or.inl rfl) hcnt
  obtain ⟨j, f, a', ws, v, hf, h566, hk', hcj, htcf, hbs, hv1, hv2, -, hrb⟩ :=
    w0_pm_peer_read hp hIn hX hFw hget hw (hG kt a bs (by omega) hget)
  rw [hlkt] at hcj
  have hlj := w0Fin_length_st hp hX hFw hwh hf (tcTrans_nonUb hX htcf hf) (Or.inl h566) hcj
  obtain ⟨K', c', hKc', hKpc', hct'⟩ := w0_close_idx
    (l := (X.tr (w0Partner L x)).take Ny) (t := t)
    (by rw [← w0Fin_length (hnoh Ny le_rfl)]; exact hty)
  have hKk' : K' < Ny := by
    have := (List.getElem?_eq_some_iff.mp hKc').1
    simp only [List.length_take] at this
    omega
  have hK' : X.get (w0Partner L x, K') = some c' := by
    rw [List.getElem?_take_of_lt hKk'] at hKc'
    exact hKc'
  have hlK' : (w0Fin ((X.tr (w0Partner L x)).take K')).1.length = t := by
    rw [w0Fin_length (hnoh K' hKk'.le), ← hct', List.take_take, Nat.min_eq_left hKk'.le]
  have hjK' : j < K' := by
    by_contra hnot
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hnot) with rfl | hlt
    · rw [hf] at hK'
      cases hK'
      omega
    · exact w0_noClose_between (X := X) (g := w0Partner L x) (k := K') (K := j)
        (by rw [← w0Fin_length (w0_noEarly_pre hp hX hFw hwh (noUbBefore_of_get hX hf)),
          ← w0Fin_length (hnoh K' hKk'.le), hlj, hlK']) K' le_rfl hlt c' hK'
        hKpc'
  obtain ⟨K0, hjK0, hK0K', ⟨c0, hc0, hc0pc⟩, hsame, hval⟩ := w0_mst_value_fin hp hX hFw hwh
    (Wg0.W0Valid.take_le hvy (by omega : K' + 1 ≤ Ny)) hf h566 hK'
    (NoUbBefore.ne hay hKk' hK') hKpc' hjK'
  obtain ⟨v2, hv2b, hv2s, hRd⟩ := hval a' ws hk'
  have hblocky := w0Fin_block_of_close hp hX hFw hwh hc0 hc0pc (by omega : K0 < Ny) hay
  rw [hsame, hlj] at hblocky
  obtain ⟨K0x, hkK0x, hK0xK, ⟨c0x, hc0x, hc0xpc⟩, hfirst⟩ := w0_first_close hK hKpc hkK
  have hpm := w0_pm_fin hp hX hFw hw (Wg0.W0Valid.take_le hvx (by omega : K0x ≤ Nx)) hget
    rfl rfl hc0x hkK0x hfirst
  have hrd := w0_pm_rd (Wg0.W0Valid.take_le hvx (by omega : K0x + 1 ≤ Nx)) hc0x hc0xpc
  have hlx : (w0Fin ((X.tr x).take K0x)).1.length = t := by
    rw [w0Fin_length (hno K0x (by omega)), w0Closed_take_eq hkK0x.le (fun q hq1 hq2 ev hev => by
      rcases Nat.eq_or_lt_of_le hq1 with rfl | hq
      · rw [hget] at hev; cases hev; simp
      · exact hfirst q hq hq2 ev hev), ← w0Fin_length (hno kt (by omega))]
    exact hlkt
  have hblockx := w0Fin_block_of_close hp hX hFw hw hc0x hc0xpc (by omega : K0x < Nx) hax
  rw [hlx] at hblockx
  refine ⟨_, _, hblockx, hblocky, ?_⟩
  have hb4 : 0 < v2.bytes := by rw [hRd.1.1]; omega
  have hvv : v = v2 := by
    have h1 : rebuild 3 bs = .ok v2 := by
      rw [hbs, hv2b]
      exact rebuild_of_scal hb4 hv2s
    rw [hrb] at h1
    exact Except.ok.inj h1
  have hpmv : (w0Words (w0Fin ((X.tr x).take K0x)).2).pm = v2 := by
    rw [hpm, hrb, hvv]
    rfl
  rw [hpmv] at hrd ⊢
  exact rd_unique hrd hRd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The events below an event are valid**: the induction hypothesis of the trace's proof. -/
def W0Under (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∀ y j f, X.get (y, j) = some f → warp L y < 4 →
    Relation.TransGen (TcMma.TcStep L X) (y, j) (g, k) → W0Valid P.scale ((X.tr y).take (j + 1))

/-- **The maxima of two folds of blocks agree** when the exchange word of each block of the
first is the maximum of the second's block, and the other way. -/
theorem w0MxCarry_eq {sc : ℝ} {A B : List (List Event)} (hlen : A.length = B.length)
    (h1 : ∀ t < A.length, ∃ sa sb, A[t]? = some sa ∧ B[t]? = some sb ∧
      w0FE (w0Words sa).pm = w0Loc sc (w0Words sb))
    (h2 : ∀ t < A.length, ∃ sb sa, B[t]? = some sb ∧ A[t]? = some sa ∧
      w0FE (w0Words sb).pm = w0Loc sc (w0Words sa)) : w0MxCarry sc A = w0MxCarry sc B := by
  let term : List Event → EReal := fun seg =>
    max (w0Loc sc (w0Words seg)) (w0FE (w0Words seg).pm)
  have hfold : ∀ bs : List (List Event), w0MxCarry sc bs = (bs.map term).foldl max ⊥ := by
    intro bs
    unfold w0MxCarry
    rw [List.foldl_map]
  have hmap : A.map term = B.map term := by
    refine List.ext_getElem? fun t => ?_
    by_cases ht : t < A.length
    · obtain ⟨sa, sb, ha, hb, h3⟩ := h1 t ht
      obtain ⟨sb', sa', hb', ha', h3'⟩ := h2 t ht
      rw [hb] at hb'
      rw [ha] at ha'
      cases hb'
      cases ha'
      simp only [List.getElem?_map, ha, hb, Option.map_some, term]
      rw [h3, h3', max_comm]
    · have h1 : A[t]? = none := by rw [List.getElem?_eq_none_iff]; omega
      have h2 : B[t]? = none := by rw [List.getElem?_eq_none_iff]; omega
      simp [List.getElem?_map, h1, h2]
  rw [hfold, hfold, hmap]

/-- **The carried maxima of a lane and its partner agree** (valid prefixes): at the lane's
row-sum load (pc 1157) and the partner's row-sum store (pc 1155) that it reads, the blocks of the
two lanes fold to the same true maximum. -/
theorem w0_carry_eq (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k j : Nat} {a : Acc} {bs : List (Option Byte)} {f : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some ⟨1157, .rd a bs⟩) (hv : W0Valid P.scale ((X.tr g).take k))
    (hf : X.get (w0Partner L g, j) = some f) (hpc : f.pc = 1155)
    (htc : Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k))
    (hU : W0Under P L X g k) :
    w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 =
      w0MxCarry P.scale (w0Fin ((X.tr (w0Partner L g)).take j)).1 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hpp := w0Partner_partner hp hw hg
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hjl : j < (X.tr (w0Partner L g)).length := (List.getElem?_eq_some_iff.mp hf).1
  have hlx := w0_len_epi hp hX hFw hw he (fun _ h => by cases h) (Or.inr rfl)
  have hly := w0_len_epi hp hX hFw hwh hf (tcTrans_nonUb hX htc hf) (Or.inl hpc)
  rw [hdiv] at hly
  have hvj : W0Valid P.scale ((X.tr (w0Partner L g)).take (j + 1)) := hU _ j f hf hwh htc
  have hvj' : W0Valid P.scale ((X.tr (w0Partner L g)).take j) :=
    Wg0.W0Valid.take_le hvj (Nat.le_succ j)
  refine w0MxCarry_eq (by rw [hlx, hly]) (fun t ht => ?_) (fun t ht => ?_)
  · refine w0_pm_link hp hIn hX hFw hw (noUbBefore_of_get hX he) (noUbBefore_of_get hX hf) hv hvj'
      ht (by omega) ?_
    intro kt a' bs' hkt hget j' e' hget' htc'
    exact ⟨hU _ j' e' hget' hwh (htc'.trans (w0_tc_572 hp hX hFw hw hget rfl
      (Wg0.W0Valid.take_le hv (by omega)) hkt hkl)),
      tcTrans_nonUb hX (htc'.trans (w0_tc_572 hp hX hFw hw hget rfl
        (Wg0.W0Valid.take_le hv (by omega)) hkt hkl)) hget'⟩
  · have key := w0_pm_link hp hIn hX hFw hwh (t := t) (Nx := j) (Ny := k) (noUbBefore_of_get hX hf)
      (by rw [hpp]; exact noUbBefore_of_get hX he) hvj'
      (by rw [hpp]; exact hv) (by omega) (by rw [hpp]; omega) (by
        intro kt a' bs' hkt hget j' e' hget' htc'
        rw [hpp] at hget' htc'
        have := hU g j' e' hget' hw (htc'.trans ((w0_tc_572 hp hX hFw hwh hget rfl
          (Wg0.W0Valid.take_le hvj (by omega)) hkt hjl).trans htc))
        rw [hpp]
        exact ⟨this, tcTrans_nonUb hX (htc'.trans ((w0_tc_572 hp hX hFw hwh hget rfl
          (Wg0.W0Valid.take_le hvj (by omega)) hkt hjl).trans htc)) hget'⟩)
    rw [hpp] at key
    obtain ⟨sx, sy, h1, h2, h3⟩ := key
    exact ⟨sx, sy, h1, h2, h3⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
