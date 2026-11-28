-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPairs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PstValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Pex
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SegEvent
import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # The peer reads of a finished block are the partner's low words

The two reads at the peer pc `477 + 5 k0` of a finished block are the elements 0 and 1 of the
lane's slot (`w0_peer_events`), each reading the pair of the partner's low words at the partner's
store of the block (`peer_read_value`; the store is unique, `peer_store`): the block's peer pair
`k0` is the two pairs of the partner's words `4 k0 .. 4 k0 + 3`. -/

/-! # The peer load reads the partner's low words

The load of lane `g` at pc `477 + 5 k0` after `r + 1` pair-barrier events reads, as the value
`w0RdVal`, the pair of the partner's low words `4 k0 + 2 el` and `4 k0 + 2 el + 1` of its block in
progress at the peer store (`peer_read_value`), when the low words are `f32` numbers
(`hfl`) and the low half is loaded at the store (`hne`): `peer_read_bytes` (the load returns the
store's bytes `8 el .. 8 el + 7`) and `w0_pst_value` (the store writes the pack of the words). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The bytes of a pair are the first's and the second's. -/
theorem toBytes_pair (a b : Value) : (Value.pair a b).toBytes = a.toBytes ++ b.toBytes := by
  simp only [Value.toBytes, Value.bytes]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    simp [Value.byteAt, List.mem_range.mp hk]
  · refine List.map_congr_left fun k hk => ?_
    simp [Value.byteAt]

/-- The bytes of a pair of `f32` numbers read back give the pair. -/
theorem rebuild_pair_float (x y : ℝ) :
    rebuild 3 ((Value.pair (.float .f32 x) (.float .f32 y)).toBytes.map some) =
      .ok (.pair (.float .f32 x) (.float .f32 y)) := by
  simp [Value.toBytes, Value.bytes, Value.byteAt, List.range_succ, FloatFmt.bytes, rebuild,
    rebuild.halves, intByte]
  rfl

/-- **The peer load reads the partner's low words** (valid rows): the load of lane `g` at pc
`477 + 5 k0` after `r + 1` pair-barrier events reads the pair of the low words `4 k0 + 2 el` and
`4 k0 + 2 el + 1` of the partner's block in progress at its peer store at pc `403 + 10 k0`
(after `r` pair-barrier events), `el` the load's element (`a'.loc.addr + 8 el = a.loc.addr`). -/
theorem peer_read_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {g k r k0 : Nat} {a : Acc}
    {bs : List (Option Byte)} {kb : Nat} (hw : warp L g < 4) (hk0 : k0 < 8)
    (he : X.get (g, k) = some ⟨477 + 5 * k0, .rd a bs⟩)
    (hnp : ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1)
    (hkb : kb < (X.tr g).length)
    (hnb : ((X.tr g).take kb).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1)
    (hrR : r < blocksOf P L (g / L.block)) (hv : W0Below P L X (w0Partner L g) g kb)
    (hne : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo ≠ [])
    (hfl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) → ∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c (.pred false) =
        .float .f32 x) :
    ∃ j f el, X.get (w0Partner L g, j) = some f ∧ f.pc = 403 + 10 * k0 ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId (10 + warp L g % 2)) = r ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) ∧
      el < 2 ∧ (∃ a' ws, f.kind = .wr a' ws ∧ a'.loc.addr + 8 * el = a.loc.addr) ∧
      w0RdVal ⟨477 + 5 * k0, .rd a bs⟩ = some (.pair
        ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 2 * el)
          (.pred false))
        ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 2 * el + 1)
          (.pred false))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  have hwords : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      ∃ x0 x1 x2 x3 : ℝ, ws = (Value.pair
        (.pair (.float .f32 x0) (.float .f32 x1))
        (.pair (.float .f32 x2) (.float .f32 x3))).toBytes ∧
        (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0) (.pred false) =
          .float .f32 x0 ∧
        (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 1) (.pred false) =
          .float .f32 x1 ∧
        (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 2) (.pred false) =
          .float .f32 x2 ∧
        (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 3) (.pred false) =
          .float .f32 x3 := by
    intro j f a' ws hf hpc hk htc
    have hws := w0_pst_value hp hX hFw hwh hf hk0 hpc
      (Wg0.W0Valid.take_le (hv j f hf htc).1 (Nat.le_succ j)) (hne j f hf hpc htc) a' ws hk
    obtain ⟨x0, h0⟩ := hfl j f hf hpc htc (4 * k0) (by omega)
    obtain ⟨x1, h1⟩ := hfl j f hf hpc htc (4 * k0 + 1) (by omega)
    obtain ⟨x2, h2⟩ := hfl j f hf hpc htc (4 * k0 + 2) (by omega)
    obtain ⟨x3, h3⟩ := hfl j f hf hpc htc (4 * k0 + 3) (by omega)
    rw [h0, h1, h2, h3] at hws
    exact ⟨x0, x1, x2, x3, hws, h0, h1, h2, h3⟩
  have hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      ws.length = 16 := by
    intro j f a' ws hf hpc hk htc
    obtain ⟨x0, x1, x2, x3, hws, -⟩ := hwords j f a' ws hf hpc hk htc
    rw [hws]
    simp [Value.toBytes, Value.bytes, FloatFmt.bytes]
  obtain ⟨j, f, a', ws, hf, hfpc, hk, hcj, htc, el, hel, hA, hbs⟩ :=
    peer_read_bytes hp hX hFw hR hw hk0 he hnp hkb hnb hrR hv hlen
  obtain ⟨x0, x1, x2, x3, hws, h0, h1, h2, h3⟩ := hwords j f a' ws hf hfpc hk htc
  refine ⟨j, f, el, hf, hfpc, hcj, htc, hel, ⟨a', ws, hk, hA⟩, ?_⟩
  have hl2 : ∀ u v : ℝ, (Value.pair (.float .f32 u) (.float .f32 v)).toBytes.length = 8 := by
    intro u v
    simp [Value.toBytes, Value.bytes, FloatFmt.bytes]
  rw [hws, toBytes_pair] at hbs
  simp only [w0RdVal]
  interval_cases el
  · rw [Nat.mul_zero, List.drop_zero, List.take_left' (hl2 x0 x1)] at hbs
    rw [hbs, rebuild_pair_float]
    simp only [Nat.mul_zero, Nat.add_zero, h0, h1]
    rfl
  · rw [Nat.mul_one, List.drop_left' (hl2 x0 x1), List.take_of_length_le (by rw [hl2]) ] at hbs
    rw [hbs, rebuild_pair_float]
    simp only [Nat.mul_one, h2, h3]
    rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}


/-- The count facts of a peer read: the read's pair-barrier count is one more than the closed
blocks of its prefix, a ring round below the block count. -/
theorem peer_cnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k0 j : Nat} {a : Acc}
    {bs : List (Option Byte)} (hk0 : k0 < 8) (he : X.get (g, j) = some ⟨477 + 5 * k0, .rd a bs⟩) :
    ∃ r < blocksOf P L (g / L.block), r = w0Closed ((X.tr g).take j) ∧
      ((X.tr g).take j).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1 := by
  obtain ⟨r, hrR, -, h2, -, hb⟩ := pex_cnt hp hX hFw (fun _ h => by cases h) he (by omega) hw
    (.inl ⟨k0, hk0, .inr rfl⟩)
  obtain ⟨-, h2'⟩ := h2 (by omega) (by omega)
  have := w0Closed_of_ring hp hX hFw hw (fun b => (hb b).2) (noUbBefore_of_get hX he)
  exact ⟨r, hrR, by omega, h2'⟩

theorem peer_pair_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) (hw : warp L g < 4)
    {N kb K0 k0 : Nat} (hvg : W0Valid P.scale ((X.tr g).take N)) (hk0 : k0 < 8)
    (hN : K0 ≤ N + 1) (hkb : kb < (X.tr g).length)
    (hn2 : 2 ≤ ((w0Scan ((X.tr g).take K0)).2.filter fun e =>
      e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length) (hal : LaneUbFree X g K0)
    (hnb : ((X.tr g).take kb).countP (Execution.isBarId (10 + warp L g % 2)) =
      w0Closed ((X.tr g).take K0) + 1)
    (hv : W0Below P L X (w0Partner L g) g kb)
    (hne : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo ≠ [])
    (hfl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) → ∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c (.pred false) =
        .float .f32 x) :
    ∃ j f, X.get (w0Partner L g, j) = some f ∧ f.pc = 403 + 10 * k0 ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) ∧
      w0Closed ((X.tr (w0Partner L g)).take j) = w0Closed ((X.tr g).take K0) ∧
      w0Peer (w0Fin ((X.tr g).take K0)).2 k0 =
        (.pair ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0) (.pred false))
          ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 1) (.pred false)),
         .pair ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 2)
            (.pred false))
          ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 3)
            (.pred false))) := by
  obtain ⟨j0, j1, x, y, a0, b0, a1, b1, hj0, hj1, hg0, hg1, hc0, hc1, hk0', hk1', hp0, hp1, hw0,
    hw1, hpeer⟩ := w0_peer_events hp hX hFw hw hvg hk0 hN hn2 hal
  have hg := Frame.lt_of_get hX hg0
  obtain ⟨-, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hpar := partner_warp_par (h := w0Partner L g) hp hw hmod
  obtain ⟨pcx, kx⟩ := x
  obtain ⟨pcy, ky⟩ := y
  simp only at hk0' hk1' hp0 hp1
  subst hk0' hk1' hp0 hp1
  obtain ⟨r0, hr0, hr0e, hnp0⟩ := peer_cnt hp hX hFw hw hk0 hg0
  obtain ⟨r1, hr1, hr1e, hnp1⟩ := peer_cnt hp hX hFw hw hk0 hg1
  have hnb' : ((X.tr g).take kb).countP (Execution.isBarId (10 + warp L g % 2)) = r0 + 1 := by
    rw [hnb, hr0e, hc0]
  obtain ⟨js, fs, hfs, hfspc, hcs, htcs, huniq⟩ :=
    peer_store hp hX hFw hR hw hkb hk0 hnb' hr0 hv
  obtain ⟨jp0, f0, el0, hf0, hf0pc, hcn0, htc0, hel0, ⟨a', ws, hkf0, hA0⟩, hval0⟩ :=
    peer_read_value hp hX hFw hR hw hk0 hg0 hnp0 hkb hnb' hr0 hv hne hfl
  obtain ⟨jp1, f1, el1, hf1, hf1pc, hcn1, htc1, hel1, ⟨a'', ws', hkf1, hA1⟩, hval1⟩ :=
    peer_read_value hp hX hFw hR hw hk0 hg1 (by rw [hnp1, hr1e, hr0e, hc1, hc0]) hkb hnb' hr0
      hv hne hfl
  have hj0e : jp0 = js := huniq jp0 f0 hf0 (fun _ h => by rw [hkf0] at h; cases h) hf0pc hcn0
  have hj1e : jp1 = js := huniq jp1 f1 hf1 (fun _ h => by rw [hkf1] at h; cases h) hf1pc hcn1
  subst hj0e hj1e
  rw [hf0] at hf1
  cases hf1
  rw [hkf0] at hkf1
  simp only [Kind.wr.injEq] at hkf1
  obtain ⟨rfl, -⟩ := hkf1
  obtain ⟨hl0, -⟩ := hw0
  obtain ⟨hl1, -⟩ := hw1
  have ha0 : a0.loc.addr = L.sharedBase + (204800 + 4096 * (tidOf L g / 32) +
      16 * (tidOf L g % 32) + 512 * k0 + 8 * 0) := by rw [hl0]; rfl
  have ha1 : a1.loc.addr = L.sharedBase + (204800 + 4096 * (tidOf L g / 32) +
      16 * (tidOf L g % 32) + 512 * k0 + 8 * 1) := by rw [hl1]; rfl
  have he0 : el0 = 0 := by omega
  have he1 : el1 = 1 := by omega
  subst he0 he1
  refine ⟨_, f0, hf0, hf0pc, htc0, ?_, ?_⟩
  · obtain ⟨r', hrR', h1', -, -, hb'⟩ := pex_cnt hp hX hFw
      (fun _ h => by rw [hkf0] at h; cases h) hf0 (by omega) hwh
      (.inl ⟨k0, hk0, .inl hf0pc⟩)
    obtain ⟨-, hnpp⟩ := h1' (by omega)
    rw [hpar] at hnpp
    have := w0Closed_of_ring hp hX hFw hwh (fun b => (hb' b).2) (noUbBefore_of_get hX hf0)
    omega
  · rw [hpeer, w0A0_of_rdVal hval0]
    simp only [hval1, Option.getD_some]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at *

/-- **The peer reads of a finished block** with whole valid traces of the lane and its partner. -/
theorem peer_pair (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hw : warp L g < 4)
    (hvg : W0Trace P X g) (hv : W0Trace P X (w0Partner L g)) {K0 k0 : Nat} (hk0 : k0 < 8)
    (hOk : W0PeerOk ((w0Words (w0Fin ((X.tr g).take K0)).2).pw k0))
    (hne : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo ≠ [])
    (hfl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 → ∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c (.pred false) =
        .float .f32 x) :
    ∃ j f, X.get (w0Partner L g, j) = some f ∧ f.pc = 403 + 10 * k0 ∧
      w0Closed ((X.tr (w0Partner L g)).take j) = w0Closed ((X.tr g).take K0) ∧
      w0Peer (w0Fin ((X.tr g).take K0)).2 k0 =
        (.pair ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0) (.pred false))
          ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 1) (.pred false)),
         .pair ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 2)
            (.pred false))
          ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD (4 * k0 + 3)
            (.pred false))) := by
  have hn2 := w0_peer_len hk0 hOk
  obtain ⟨j0, j1, x, y, a0, b0, a1, b1, hj0, hj1, hg0, hg1, hc0, hc1, hk0', hk1', hp0, hp1, hw0,
    hw1, hpeer⟩ := w0_peer_events hp hX hFw hw (hvg.take (j := K0)) hk0 (Nat.le_succ K0) hn2 hnu
  obtain ⟨pcx, kx⟩ := x
  simp only at hk0' hp0
  subst hk0' hp0
  obtain ⟨r0, -, hr0e, hnp0⟩ := peer_cnt hp hX hFw hw hk0 hg0
  have hkb : j0 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hg0).1
  obtain ⟨j, f, hf, hpc, -, hcl, hpe⟩ := peer_pair_at hp hX hFw hR hw
    (hvg.take (j := K0)) hk0 (Nat.le_succ K0) hkb hn2 hnu (by rw [hnp0, hr0e, hc0])
    (fun j' f' hf' _ => ⟨hv.take (j' + 1), noUb_kind hnu hf'⟩) (fun j f hf hpc _ => hne j f hf hpc)
    (fun j f hf hpc _ => hfl j f hf hpc)
  exact ⟨j, f, hf, hpc, hcl, hpe⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
