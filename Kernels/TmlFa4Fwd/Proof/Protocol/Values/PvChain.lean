-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Pv
import Kernels.TmlFa4Fwd.Proof.Mma.Export.BeforePv
import Kernels.TmlFa4Fwd.Proof.Mma.Export.PvSteps
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AccSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LoadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Results
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Score
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The value chain of the output accumulator

PV step `n` of tile `u` leaves the accumulator before the tile plus the first `16 (n + 1)` terms of
the tile's sum (`pv_result`), by induction over the tiles and their steps: a step after the first
accumulates on the step before; the first step of a later tile accumulates on the correction lane's
store of the tile's credit, when there is one, and else on the last step of the tile before. A
correction load of credit `q` reads the last step of tile `q - 1` (`corr_load`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {I : Nat → Inputs}
  {P : Nat → Nat → Nat → ℝ}

/-- **The probabilities of a CTA's softmax lanes.** -/
def CtaP (L : Launch) (X : Execution) (P : Nat → Nat → Nat → ℝ) (c : Nat) : Prop :=
  ∀ h, h < L.threads → Prologue.warpIndex L h < 8 → h / L.block = c → PStored L X h (P h)

/-- **The words a CTA's correction lanes store are numbers.** -/
def CorrF32 (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → X.TSt (h, i) a vals .s32x32b → F32s vals

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- The steps of a tile before an MMA of a later tile or a commit. -/
theorem pv_step_before {g K pc st v : Nat} {kK : TcKind} (hw : Prologue.warpIndex L g = 12)
    (hst : st < 2) (he : X.get (g, K) = some ⟨pc, .tc kK⟩)
    (hk : (∃ d s acc mask, kK = .mma d s acc mask) ∨ ∃ s, kK = .commit s)
    (hv : v + 1 ≤ pPolls L X g st K) (hne : ∀ j, ¬ Pv L X g K st v j) :
    ∀ (n : Nat) (j : Fin 8), j.val = n → ∃ i < K, Pv L X g i st v j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := Fin.ext hj
    obtain ⟨i, hi, hq⟩ := Mma.pv_before hp hX hFw hw hst he hk hv
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · exact ⟨i, h, hq⟩
    · exact absurd hq (hne 0)
  | succ n ih =>
    intro j hj
    obtain ⟨i, hi, hq⟩ := ih ⟨n, by have := j.isLt; omega⟩ rfl
    obtain ⟨i', -, hi', hq'⟩ := Mma.pv_next hp hX hFw hw hq (j' := j) (by simp only; omega) hi he hk
    rcases Nat.lt_or_eq_of_le hi' with h | rfl
    · exact ⟨i', h, hq'⟩
    · exact absurd hq' (hne j)

/-- An MMA writing a cell of the accumulator, of the issuer of another. -/
theorem pv_of_writer {g k st : Nat} {cell : Cell} {x : EvId} (hm : IsMma X (g, k))
    (hc : X.MmaCell (g, k) cell) (hO : InO st cell) (hx : IsMma X x) (hxc : X.MmaCell x cell) :
    x.1 = g ∧ ∃ u j, Pv L X g x.2 st u j := by
  have ht := scoreFacts hp hX hFw
  have h1 : x.1 = g := ht.tc_one hx (.inl hm) (by
    rw [mma_lead ht hx hxc, mma_lead ht hm hc])
  obtain ⟨-, u, j, h⟩ := pv_of_cell hp hX hFw hx hxc hO
  rw [h1] at h
  exact ⟨h1, u, j, h⟩

/-- **PV step `n` of tile `u`.** -/
theorem pv_result (hI : OperandBytes I L X) (hcorr : CorrF32 L X) {g st row col : Nat}
    (hst : st < 2) (hP : CtaP L X P (g / L.block)) (hrow : row < 128) (hcol : col < 128) :
    ∀ (u n : Nat) {k : Nat} {j : Fin 8}, j.val = n → Pv L X g k st u j →
      X.async.mmaDone (g, k) = true →
      Result L Assumptions.all X (g, k) ⟨g / L.block, row, 256 + 128 * st + col⟩ (.float .f32
        (before L X (P (softLane L (g / L.block) st row)) (I (g / L.block)) st
            ⟨g / L.block, row, 256 + 128 * st + col⟩ col u +
          pvSum (P (softLane L (g / L.block) st row)) (I (g / L.block)) u col (16 * (n + 1)))) := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hR : OReady L X := oready ht hH.s hH.o hH.route
  set cell : Cell := ⟨g / L.block, row, 256 + 128 * st + col⟩ with hcell
  set Q := P (softLane L (g / L.block) st row)
  set J := I (g / L.block)
  have hO : InO st cell := ⟨by simp only [hcell]; omega, by simp only [hcell]; omega⟩
  -- the issue, the cell and the arithmetic of a step
  have hstep : ∀ {u k : Nat} {j : Fin 8}, Pv L X g k st u j → ∃ db,
      X.MmaIssue (g, k) (256 + 128 * st) ⟨pvDsc, db, db, g / L.block, g / L.block,
        some (128 * st + 64 + 8 * j.val), {}⟩ (j.val != 0 || u != 0) [0, 0, 0, 0] ∧
      X.MmaCell (g, k) cell ∧ ∀ {db' : TcShared.Descriptor} {ops : AsyncCopy.MmaOperands}
        {old : Option Value} {prev : ℝ}, X.MmaIssue (g, k) (256 + 128 * st) ⟨pvDsc, db', db',
          g / L.block, g / L.block, some (128 * st + 64 + 8 * j.val), {}⟩ (j.val != 0 || u != 0)
          [0, 0, 0, 0] → X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops →
        Assumption.idealMmaAccumulator .f32 (j.val != 0 || u != 0) old = .ok prev →
        eval Assumptions.all pvDsc (j.val != 0 || u != 0) ops.a ops.b old row col =
          .ok (.float .f32 (∑ c ∈ Finset.range 16,
            Q u (16 * j.val + c) * J.v u (16 * j.val + c) col + prev)) := by
    intro u k j hq
    obtain ⟨pc, db, he⟩ := id hq.issue
    have hi : X.MmaIssue (g, k) _ _ _ _ := ⟨pc, he⟩
    refine ⟨db, hi, ⟨_, _, _, _, _, _, hi, pv_pos hst db hrow hcol⟩, ?_⟩
    intro db' ops old prev hi' hd hops hprev
    exact eval_mma hp hX hFw hi' hops (pv_pos hst db' hrow hcol)
      (fun c hc => pv_a hp hX hFw hst hP hq hi' hops hrow hc)
      (fun c hc => pv_b hp hI hst hq hi' hd hops hcol hc) hprev
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ihu =>
  intro n
  induction n with
  | zero =>
    intro k j hj hq hd
    obtain ⟨db, hi, hc, hev⟩ := hstep hq
    obtain ⟨ops, hops⟩ := operands_of_done hX hd
    have hj0 : j = 0 := Fin.ext hj
    subst hj0
    cases u with
    | zero =>
      have hv := hev (old := none) (prev := 0) hi hd hops rfl
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, add_zero] at hv
      have h0 : before L X Q J st cell col 0 = 0 := rfl
      rw [h0, zero_add]
      exact .overwrite hi (pv_pos hst db hrow hcol) hops hv
    | succ u =>
      have hw : Prologue.warpIndex L g = 12 := (mma_qkpv hp hX hFw (i := (g, k)) ⟨_, _, _, _, hi⟩).1
      obtain ⟨pc, he⟩ := id hi
      have hpp := hq.p
      -- the last step of the tile before
      obtain ⟨i, hik, hq7⟩ := pv_step_before hp hX hFw hw hst he (.inl ⟨_, _, _, _, rfl⟩) (v := u)
        (by omega) (fun j' h' => by have := h'.p; omega) 7 7 rfl
      obtain ⟨db7, hi7, hc7, -⟩ := hstep hq7
      have hp7 := hq7.p
      have hd7 := prev_done hp hX hFw hi7 hi hik hc7 hc hd
      have hres7 := ihu u (Nat.lt_succ_self u) 7 rfl hq7 hd7
      have hmax : ∀ k', k' < k ∧ X.MmaCell (g, k') cell → k' ≤ i := by
        rintro k' ⟨hk', hck'⟩
        obtain ⟨d', s', a', m', -, -, hi', -⟩ := id hck'
        obtain ⟨-, u', j', h'⟩ := pv_of_writer hp hX hFw ⟨_, _, _, _, hi⟩ hc hO
          (x := (g, k')) ⟨_, _, _, _, hi'⟩ hck'
        by_contra hgt
        have m1 := pPolls_mono (L := L) (X := X) (g := g) (st := st) (show i ≤ k' by omega)
        have m2 := pPolls_mono (L := L) (X := X) (g := g) (st := st) hk'.le
        have hp' := h'.p
        simp only at h' hp'
        rcases (by omega : u' = u ∨ u' = u + 1) with rfl | rfl
        · have := Mma.pv_order hp hX hFw hw _ rfl hq7 h' (by omega)
          have := j'.isLt
          omega
        · have := Mma.pv_order hp hX hFw hw _ rfl h' hq hk'
          simp at this
      have hthr_of : ∀ x : EvId, IsMma X x → X.MmaCell x cell → x.1 = g := fun x hx hcx =>
        (pv_of_writer hp hX hFw ⟨_, _, _, _, hi⟩ hc hO hx hcx).1
      have hfirst : ∀ x, IsMma X x → X.MmaCell x cell → u + 2 ≤ pPolls L X x.1 st x.2 →
          x = (g, k) ∨ k < x.2 := by
        rintro ⟨g', k'⟩ hx hcx hle
        obtain rfl : g' = g := hthr_of _ hx hcx
        simp only at hle ⊢
        rcases Nat.lt_trichotomy k' k with h | rfl | h
        · exfalso
          have := hmax k' ⟨h, hcx⟩
          have := pPolls_mono (L := L) (X := X) (g := g') (st := st) this
          omega
        · exact .inl rfl
        · exact .inr h
      have hlive : ∀ src, SourceLive L X src (g, k) cell := fun src =>
        sourceLive hT.live ⟨_, _, _, _, hi⟩ (.inl hc)
      have hsum : pvSum Q J (u + 1) col (16 * (0 + 1)) = ∑ c ∈ Finset.range 16,
          Q (u + 1) (16 * (0 : Fin 8).val + c) * J.v (u + 1) (16 * (0 : Fin 8).val + c) col := by
        simp [pvSum]
      rw [hsum, add_comm]
      have hacc : ((0 : Fin 8).val != 0 || u + 1 != 0) = true := by simp
      by_cases hex : ∃ y, CorrStored L X st cell (u + 1) y
      · -- the correction lane's store
        obtain ⟨y, hy⟩ := hex
        rw [before_stored hy (fun y' hy' => corrStored_unique hp hX hFw hO hy' hy)]
        obtain ⟨g', k', a, jj, vals, hs, hj', hceq, hpa, hval⟩ := hy
        obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hs)
        have h8 : 8 ≤ Prologue.warpIndex L g' := by
          by_contra h8
          have hP' := (ht.soft_st hgl (by omega) hs).1 jj hj'
          rw [hceq] at hP'
          unfold InP at hP'
          unfold InO at hO
          omega
        have hsrc := o_accSource_store hp ht ho hH.p hR hgl h8 hgw hs hj' (by rw [hceq]; exact hO)
          (c := (g, k)) ⟨_, _, _, _, hi⟩ (by rw [hceq]; exact hc) (by simp only; omega)
          (fun x hx hcx hle => hfirst x hx (by rw [hceq] at hcx; exact hcx) (by omega))
          (by rw [hceq]; exact hlive _)
        rw [hceq] at hsrc
        have hv := hev (old := some (.float .f32 y)) (prev := y) hi hd hops (by rw [hacc]; rfl)
        rw [hacc] at hi hv
        exact .accumulateStored hi (pv_pos hst db hrow hcol) hops
          ⟨a, vals, _, jj, hs, hval, by rw [tcDataCell_s32x32b, hceq]⟩ hsrc hv
      · -- the tile before
        rw [before_skip hex]
        have hsrc := o_accSource_skip ht ho hH.p hR hO hst (src := (g, i)) (c := (g, k))
          ⟨_, _, _, _, hi7⟩ hc7 ⟨_, _, _, _, hi⟩ hc (by simp only; omega)
          (by
            rintro ⟨g2, k2⟩ hx hcx hle
            obtain rfl : g2 = g := hthr_of _ hx hcx
            simp only at hle ⊢
            rcases Nat.lt_trichotomy k2 i with h | rfl | h
            · exact .inr h
            · exact .inl rfl
            · exfalso
              by_cases hk2 : k2 < k
              · have := hmax k2 ⟨hk2, hcx⟩
                omega
              · have := pPolls_mono (L := L) (X := X) (g := g2) (st := st) (show k ≤ k2 by omega)
                omega)
          (fun x hx hcx hle => hfirst x hx hcx (by simp only at hle; omega))
          (fun g2 k2 a2 j2 vals2 hs2 hj2 hceq2 hpa2 => by
            obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hs2)
            have h8 : 8 ≤ Prologue.warpIndex L g2 := by
              by_contra h8
              have hP' := (ht.soft_st hgl (by omega) hs2).1 j2 hj2
              rw [hceq2] at hP'
              unfold InP at hP'
              unfold InO at hO
              omega
            obtain ⟨y, hy⟩ := hcorr hgl h8 hgw hs2 vals2[j2] (List.getElem_mem hj2)
            exact hex ⟨y, g2, k2, a2, j2, vals2, hs2, hj2, hceq2, by simp only at hpa2; omega,
              by rw [List.getElem?_eq_getElem hj2, hy]⟩)
          (hlive _)
        have hv := hev (old := some (.float .f32 (acc L X Q J st cell col u)))
          (prev := acc L X Q J st cell col u) hi hd hops (by rw [hacc]; rfl)
        rw [hacc] at hi hv
        exact .accumulate hi (pv_pos hst db hrow hcol) hops hres7 hsrc hv
  | succ n ih =>
    intro k j hj hq hd
    obtain ⟨db, hi, hc, hev⟩ := hstep hq
    obtain ⟨ops, hops⟩ := operands_of_done hX hd
    have hw : Prologue.warpIndex L g = 12 := (mma_qkpv hp hX hFw (i := (g, k)) ⟨_, _, _, _, hi⟩).1
    rcases Mma.pv_prev hp hX hFw hw hq with ⟨h0, -⟩ | ⟨i, j', hik, hj', hq', hbt⟩
    · rw [h0] at hj; cases hj
    obtain ⟨db', hi', hc', -⟩ := hstep hq'
    have hd' := prev_done hp hX hFw hi' hi hik hc' hc hd
    have hprev := ih (by omega) hq' hd'
    have hsrc := pv_accSource_tile ht ho hH.p hR hT hst hi hc hO hik hc'
      (hq'.p.trans hq.p.symm) (by
        rintro k' ⟨hk', hck'⟩
        by_contra hgt
        obtain ⟨d2, s2, a2, m2, -, -, ⟨pc2, he2⟩, -⟩ := hck'
        obtain ⟨_, _, _, _, _, _, he3⟩ := hbt k' (by omega) hk'
        rw [he3] at he2
        cases he2)
    have hacc : (j.val != 0 || u != 0) = true := by rw [hj]; simp
    have hv := hev (old := some (.float .f32 (before L X Q J st cell col u +
      pvSum Q J u col (16 * (n + 1))))) hi hd hops (by rw [hacc]; rfl)
    have hsum : before L X Q J st cell col u + pvSum Q J u col (16 * (n + 1 + 1)) =
        ∑ c ∈ Finset.range 16, Q u (16 * j.val + c) * J.v u (16 * j.val + c) col +
          (before L X Q J st cell col u + pvSum Q J u col (16 * (n + 1))) := by
      unfold pvSum
      rw [sum_add16 _ (n + 1), hj]
      ring
    rw [hsum]
    rw [hacc] at hi hv
    exact .accumulate hi (pv_pos hst db hrow hcol) hops hprev hsrc hv

/-- **A correction load of credit `q` returns the accumulator after tile `q - 1`.** -/
theorem corr_load (hI : OperandBytes I L X) (hcorr : CorrF32 L X) {h i a j st : Nat}
    {vals : List Value} (h8 : 8 ≤ Prologue.warpIndex L h) (h12 : Prologue.warpIndex L h < 12)
    (hP : CtaP L X P (h / L.block)) (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length)
    (hO : InO st (tcDataCell32 L h a j)) :
    vals[j]? = some (.float .f32 (acc L X
      (P (softLane L (h / L.block) st (tcDataCell32 L h a j).lane)) (I (h / L.block)) st
      (tcDataCell32 L h a j) ((tcDataCell32 L h a j).column - (256 + 128 * st))
      (pArr L X h st i - 1))) := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hR : OReady L X := oready ht hH.s hH.o hH.route
  obtain ⟨hh, -⟩ := ht.tc_role (.inl hld)
  obtain ⟨hst, h1, y, K, s, hcom, hcy, hle⟩ := corr_commit hp hX hFw hh h8 h12 hld hj hO
  have hyw := commit_warp hp hX hFw hcom
  obtain ⟨pcK, heK⟩ := id hcom
  obtain ⟨k, hkK, hq⟩ := pv_step_before hp hX hFw hyw hst heK (.inr ⟨_, rfl⟩)
    (v := pArr L X h st i - 1) (by omega) (fun j' h' => by
      obtain ⟨_, _, e⟩ := h'.issue
      rw [heK] at e
      cases e) 7 7 rfl
  obtain ⟨hl, hcta⟩ := cell_lane hp (L := L) (h := h) (a := a) (j := j)
  have hc : X.MmaCell (y, k) (tcDataCell32 L h a j) :=
    pv_cell hp hX hFw hst hq (by rw [hcta, hcy]) hl hO
  have hm : IsMma X (y, k) := by
    obtain ⟨_, _, he⟩ := hq.issue
    exact ⟨_, _, _, _, _, he⟩
  have hqp := hq.p
  have hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      pPolls L X x.1 st x.2 ≤ pPolls L X y st k → x = (y, k) ∨ x.2 < k := by
    rintro ⟨g', k'⟩ hx hcx hle'
    obtain ⟨hg', u', j', hq'⟩ := pv_of_writer hp hX hFw hm hc hO hx hcx
    simp only at hg' hq' hle'
    subst hg'
    rcases Nat.lt_trichotomy k' k with hk | rfl | hk
    · exact .inr hk
    · exact .inl rfl
    · exfalso
      have m1 := pPolls_mono (L := L) (X := X) (g := g') (st := st) hk.le
      have hp' := hq'.p
      obtain rfl : u' = pArr L X h st i - 1 := by omega
      have := Mma.pv_order hp hX hFw hyw _ rfl hq hq' hk
      have := j'.isLt
      omega
  have hdone : DoneBefore L X (y, k) (h, i) := by
    obtain ⟨st', -, hcells, -⟩ := ho.corr_ld hh h8 h12 hld
    obtain rfl := inO_st (hcells j hj) hO
    exact hR hh h8 h12 (.inl hld) hcells hm ⟨_, hc, hO⟩ hcy (by simp only; omega)
  have hrs := o_readSource hp ht ho hH.p hR hh h8 h12 hld hj hO hm hc (by simp only; omega) hlast
    (fun cta r hr hcov rel hrel => .inl (hT.live (.inr (.inl ⟨j, loadCell32 hld hj⟩)) cta r hr hcov
      rel hrel))
  have hcolb : 256 + 128 * st ≤ (tcDataCell32 L h a j).column ∧
      (tcDataCell32 L h a j).column < 384 + 128 * st := hO
  have hres := pv_result hp hX hFw hI hcorr (row := (tcDataCell32 L h a j).lane)
    (col := (tcDataCell32 L h a j).column - (256 + 128 * st)) hst (P := P)
    (by rw [hcy]; exact hP) hl (by omega) _ 7 rfl hq (hdone.done hX.tcCommit)
  have hceq : (⟨y / L.block, (tcDataCell32 L h a j).lane, 256 + 128 * st +
      ((tcDataCell32 L h a j).column - (256 + 128 * st))⟩ : Cell) = tcDataCell32 L h a j := by
    have : 256 + 128 * st + ((tcDataCell32 L h a j).column - (256 + 128 * st)) =
        (tcDataCell32 L h a j).column := by omega
    rw [this, hcy, ← hcta]
  rw [hceq, hcy] at hres
  obtain ⟨word, hword, hcw⟩ :=
    hX.tcRead.1 _ a vals _ j _ _ _ hld (loadCell32 hld hj) hrs (.inl hres)
  rw [hword]
  rcases hcw with ⟨-, rfl⟩ | ⟨hb, -⟩
  · rfl
  · simp [Value.bytes, FloatFmt.bytes] at hb

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
