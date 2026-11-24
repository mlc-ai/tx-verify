-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Reduce
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

/-! # The output of a complete execution

In a complete execution every thread has exited, after the rows of its CTA. So for each row and
each of its pairs of outputs, the thread that owns them stored them in the row (`out_write`): its
reloaded inputs times the scale factor of the row's total times its weights, which is the
specified output. It is the only write of those bytes, and no write touches global memory outside
the output (`result`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow Finset

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The pair of outputs `2 p`, `2 p + 1` of tile `t` of thread `tid` in row `r`. -/
def outPair (P : Params) (r t tid p : Nat) : Value :=
  .pair (.float .f16 (y P r (2048 * t + 8 * tid + 2 * p)))
    (.float .f16 (y P r (2048 * t + 8 * tid + 2 * p + 1)))

/-- A global write is an output store of a row of the thread. -/
theorem out_site {g k pc : Nat} {d : D} {a : Acc} {bs : List Byte}
    (hA : At P L X g k d ⟨pc, .wr a bs⟩) (hg : a.loc.space = .global) :
    ((d.site = .stoa ∧ a = vacc .global 0 (P.O + off g d.i) d.sub) ∨
      (d.site = .stob ∧ a = vacc .global 0 (P.O + off g d.i + 4096) d.sub)) ∧
    bs = (outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub).toBytes := by
  rcases wr_site hA.event with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ |
    ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ <;>
    simp [vacc] at hg
  · exact ⟨.inl ⟨h1, rfl⟩, rfl⟩
  · exact ⟨.inr ⟨h1, rfl⟩, rfl⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **The output a state stores**: the specified outputs of its row. -/
theorem out_value {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) {t : Nat} (hs : (d.site = .stoa ∧ t = 0) ∨ (d.site = .stob ∧ t = 1)) :
    outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub = outPair P (row g d.i) t (g % 256) d.sub := by
  have hr : d.site.inRow = true := by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.inRow]
  have hsub := hA.inv.sub.1 (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.vec])
  have hp : p1 g + 14 ≤ d.pos g := by
    rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp only [D.pos, h] <;> omega
  have htt := tt_eq hpre hX ht he hA hr (by omega)
  have hpos := tt_pos P (row g d.i)
  have hdata : d.raw = hwords (win P g t) ∧ d.rs0 = fwords (xin P g d.i t) 0 ∧
      d.rs1 = fwords (xin P g d.i t) 4 := by
    rcases hs with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact tile_data hpre hX ht he hA hr (.inl ⟨rfl, hp, by simp only [D.pos, h]; omega⟩)
    · exact tile_data hpre hX ht he hA hr (.inr ⟨rfl, by simp only [D.pos, h]; omega⟩)
  obtain ⟨hw, hs0, hs1⟩ := hdata
  rw [hw, hs0, hs1, htt, cpair_fin hpos, outV_fin _ _ _ hsub]
  simp only [outPair, y, rms, c4096_eq, xin, win, Nat.add_assoc]

/-- The footprint of output pair `p` of tile `t` of thread `tid` in row `r`. -/
def outAcc (P : Params) (r t tid p : Nat) : Acc :=
  vacc .global 0 (P.O + 2 * (4096 * r + 8 * tid) + 4096 * t) p

/-- The output store of a state, with its footprint and value. -/
theorem out_store {g k pc : Nat} {d : D} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hA : At P L X g k d ⟨pc, .wr a bs⟩) {t : Nat}
    (hs : (d.site = .stoa ∧ t = 0) ∨ (d.site = .stob ∧ t = 1)) :
    a = outAcc P (row g d.i) t (g % 256) d.sub ∧
      bs = (outPair P (row g d.i) t (g % 256) d.sub).toBytes := by
  have hsp : a.loc.space = .global := by
    rcases wr_site hA.event with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ |
      ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ <;>
      rcases hs with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1] at h2 <;> first | rfl | cases h2
  obtain ⟨ha, hb⟩ := out_site hA hsp
  rw [out_value hpre hX ht he hA hs] at hb
  refine ⟨?_, hb⟩
  rcases ha with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hs with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
    rw [h1] at h2 <;>
    first | (simp [outAcc, vacc, off]; done) | cases h2

/-- **The owner of an output pair stored it**, in a complete execution. -/
theorem out_write (hcomplete : Complete L X) {r t tid p : Nat} (hr : r < P.Bt) (ht2 : t < 2)
    (htid : tid < 256) (hp : p < 4) :
    ∃ pc, X.get (256 * (r % 152) + tid,
        rowBase (256 * (r % 152) + tid) (r / 152) +
          (p1 (256 * (r % 152) + tid) + 14 + 16 * t + p)) =
      some ⟨pc, .wr (outAcc P r t tid p) (outPair P r t tid p).toBytes⟩ := by
  set g := 256 * (r % 152) + tid with hgdef
  have hgc : g / 256 = r % 152 := by omega
  have hgt : g % 256 = tid := by omega
  have hg : g < L.threads := by
    simp only [Launch.threads, hpre.hyp.grid, hpre.hyp.block]; omega
  obtain ⟨pcx, hlast⟩ := ((noTma_of_consistent noTma hX).complete_iff L hX.clc).mp hcomplete _ hg
  have hlen0 : 0 < (X.tr g).length := by
    rcases h : X.tr g with _ | ⟨e, es⟩
    · rw [h] at hlast; cases hlast
    · simp
  have hx : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩ := by
    unfold Execution.get
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨-, dx, hAx⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
  have hxs := exit_site hAx.event
  have hex := hAx.inv.exit hxs
  have hkx : (X.tr g).length - 1 = rowBase g dx.i := by rw [hAx.index]; simp [D.idx, hxs]
  have hi : r / 152 < dx.i := by omega
  have hrow : row g (r / 152) = r := by simp only [row]; omega
  obtain ⟨d, e, he, hA, hid, hpd, hrd⟩ := row_state hpre hX ht hx (by intro _ _ h; cases h)
    (i := r / 152) (q := p1 g + 14 + 16 * t + p) (by unfold rowLen; omega)
    (.inl (by
      rw [hkx]
      have := rowBase_lt (g := g) (q' := 0) (q := p1 g + 14 + 16 * t + p) hi
        (by unfold rowLen; omega)
      simpa using this))
  have hs : ((d.site = .stoa ∧ t = 0) ∨ (d.site = .stob ∧ t = 1)) ∧ d.sub = p := by
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · obtain ⟨h1, h2⟩ := stoa_of_pos hA.inv hrd hp (by omega)
      exact ⟨.inl ⟨h1, rfl⟩, h2⟩
    · obtain ⟨h1, h2⟩ := stob_of_pos hA.inv hrd hp (by omega)
      exact ⟨.inr ⟨h1, rfl⟩, h2⟩
  obtain ⟨pc, a, bs, rfl⟩ := wr_event hA.event (by
    rcases hs.1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.isStore])
  obtain ⟨rfl, rfl⟩ := out_store hpre hX ht he hA hs.1
  rw [hid, hrow, hgt, hs.2] at he
  exact ⟨pc, he⟩

/-- **The output store is the only write of its word.** -/
theorem out_unique {r t tid p b : Nat} (ht2 : t < 2) (htid : tid < 256)
    (hp : p < 4) (hb : b < 4) {w : EvId} {a : Acc} {ws : List Byte} (hw : X.Writes w a ws)
    (hc : a.Covers ((outAcc P r t tid p).loc.at b)) :
    w = (256 * (r % 152) + tid,
      rowBase (256 * (r % 152) + tid) (r / 152) +
        (p1 (256 * (r % 152) + tid) + 14 + 16 * t + p)) := by
  obtain ⟨x, kx⟩ := w
  obtain ⟨-, dx, ex, hex, hAx, hsx, -⟩ := access_facts hpre hX ht (.inr (.inl ⟨ws, hw, rfl⟩))
  obtain ⟨pcw, hw⟩ := hw
  rw [hw] at hex
  cases Option.some.inj hex
  have hO := hpre.hyp.outAlign
  have hl := loc_eq_of_overlap hsx.size (a := a) (b := outAcc P r t tid p) rfl hsx.align
    (by simp only [outAcc, vacc]; omega) ⟨_, hc, Acc.covers_at (a := outAcc P r t tid p) hb⟩
  have hsp : a.loc.space = .global := by rw [hl]; rfl
  obtain ⟨-, hW, -⟩ := hsx.global hsp
  obtain ⟨-, -, h1, h2⟩ := hW rfl
  have haddr : a.loc.addr = P.O + 2 * (4096 * r + 8 * tid) + 4096 * t + 4 * p := by
    rw [hl]; rfl
  rw [haddr] at h1 h2
  have hxg : x = 256 * (r % 152) + tid := by
    have e1 : (P.O + 2 * (4096 * r + 8 * tid) + 4096 * t + 4 * p - P.O) / 8192 = r := by omega
    have e2 : (P.O + 2 * (4096 * r + 8 * tid) + 4096 * t + 4 * p - P.O) % 4096 / 16 = tid := by
      omega
    rw [e1] at h1
    rw [e2] at h2
    omega
  subst hxg
  obtain ⟨ha, -⟩ := out_site hAx hsp
  have hidx : kx = dx.idx (256 * (r % 152) + tid) := hAx.index
  rcases ha with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · simp only [vacc, off, row] at haddr
    have hsub := hAx.inv.sub.1 (by simp [hs, Site.vec])
    have hi : dx.i = r / 152 := by omega
    have : dx.sub = p := by omega
    have ht0 : t = 0 := by omega
    rw [hidx, idx_of_row (by simp [hs, Site.inRow]), hi]
    simp [D.pos, hs, this, ht0]
  · simp only [vacc, off, row] at haddr
    have hsub := hAx.inv.sub.1 (by simp [hs, Site.vec])
    have hi : dx.i = r / 152 := by omega
    have : dx.sub = p := by omega
    have ht1 : t = 1 := by omega
    rw [hidx, idx_of_row (by simp [hs, Site.inRow]), hi]
    simp [D.pos, hs, this, ht1]

omit hpre hX ht in
theorem outPair_bytes (P : Params) (r t tid p : Nat) {j : Nat} (hj : j < 4) :
    (outPair P r t tid p).toBytes[j]? =
      some (.float .f16 (y P r (2048 * t + 8 * tid + 2 * p + j / 2)), j % 2) := by
  interval_cases j <;> simp [outPair, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes,
    List.range_succ]

/-- **The output of a complete execution.** -/
theorem result (hcomplete : Complete L X) {m : FinalMem} (hfin : IsFinal L mem0 X m) :
    Post P mem0 m := by
  have hn := noTma_of_consistent noTma hX
  have hO := hpre.hyp.outAlign
  have hbyte : ∀ r < P.Bt, ∀ k < 4096, ∀ b < 2,
      m ((gl (P.O + 2 * (4096 * r + k))).at b) = some (some (.float .f16 (y P r k), b)) := by
    intro r hr k hk b hb
    obtain ⟨pc, hw⟩ := out_write hpre hX ht hcomplete hr (t := k / 2048) (tid := k % 2048 / 8)
      (p := k % 8 / 2) (by omega) (by omega) (by omega)
    have hcov : (outAcc P r (k / 2048) (k % 2048 / 8) (k % 8 / 2)).Covers
        ((gl (P.O + 2 * (4096 * r + k))).at b) := by
      refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [outAcc, vacc, gl, Loc.at] <;> omega
    rw [hfin.unique (w := .thread _) (.inl ⟨pc, hw⟩) hcov fun w' a' bs' hw' hc' => by
      obtain ⟨w', rfl, hwT⟩ := Execution.NoTma.memWrites_thread (hn.emptyAsync hX) hw'
      have hwT := writes_of_memWrites hpre hX ht hwT
      have hj : (gl (P.O + 2 * (4096 * r + k))).at b =
          (outAcc P r (k / 2048) (k % 2048 / 8) (k % 8 / 2)).loc.at (2 * (k % 2) + b) := by
        simp only [outAcc, vacc, gl, Loc.at, Loc.mk.injEq, true_and]; omega
      rw [hj] at hc'
      rw [out_unique hpre hX ht (by omega) (by omega) (by omega) (by omega) hwT hc']]
    simp only [wbyte, outAcc, vacc, gl, Loc.at]
    rw [show P.O + 2 * (4096 * r + k) + b - (P.O + 2 * (4096 * r + 8 * (k % 2048 / 8)) +
      4096 * (k / 2048) + 4 * (k % 8 / 2)) = 2 * (k % 2) + b by omega,
      outPair_bytes P r _ _ _ (by omega)]
    rw [show 2048 * (k / 2048) + 8 * (k % 2048 / 8) + 2 * (k % 8 / 2) + (2 * (k % 2) + b) / 2 = k
      by omega, show (2 * (k % 2) + b) % 2 = b by omega]
  refine ⟨fun r hr k hk => memFloat_float fun b hb => hbyte r hr k hk b hb, fun l hglobal hl => ?_⟩
  apply hfin.unwritten
  intro w a bs hw hcov
  obtain ⟨⟨g, k⟩, rfl, hwT⟩ := Execution.NoTma.memWrites_thread (hn.emptyAsync hX) hw
  obtain ⟨-, d, ev, -, -, hsh, -⟩ := access_facts hpre hX ht
    (.inr (.inl ⟨bs, writes_of_memWrites hpre hX ht hwT, rfl⟩))
  obtain ⟨h1, h2, h3, h4⟩ := hcov
  rw [hsh.size] at h4
  have h4' := hsh.align
  rcases hsh.space with hg | hs
  · obtain ⟨hc0, hW, -⟩ := hsh.global hg
    obtain ⟨hlo, hhi, -⟩ := hW rfl
    exact hl ⟨hglobal, by rw [h2, hc0], by omega, by omega⟩
  · rw [hglobal, hs] at h1
    cases h1

end
end PTX.Kernels.RmsNorm.Proof
