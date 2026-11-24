-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.SvOut
public import Kernels.InklingRelDecode.Proof.Result.MmaAll

@[expose] public section

/-!
# The S tile's load returns the exact scores (`Sv.SvPrem.score`)

`SLoadSrc` is the protocol layer's half of the S load: for the softmax thread's `tcgen05.ld` of
iteration `i`, the last QK MMA of block `i` (the lane's state at step 7 of iteration `i`, with the
Tensor Memory base the thread's) is the read source (`ReadSource .ld`) of each of the 64 cells the
load reads. It is the analogue of `Rs.oSource_of` for the S tile and uses `SO.s_doneBefore`
(the QK MMAs are done before the poll of `s_ready` returns), `Sr.PAliasSyncS` (the load has read
before a later store or MMA of the buffer) and the lane's program order; it is not proved here.

`ldS_cell`: register `j` of the load is the cell `Mma.sCell` of the thread's row and column
`64 · half + j`. `scoreEv_of`: from `SLoadSrc` and the premises of the MMA data path
(`Mma.score_load`), the load returns the f32 float of `Spec.score` of the key at each register: the
premise `Sv.ScoreEv` of the iteration invariant.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The cell register `j` of the S load reads**: row `row T`, column `tm + 128 (i % 2) +
64 · half + j` of the score buffer of the thread's CTA. -/
theorem ldS_cell (L : Launch) (g : Nat) {tm i : Nat} (htm : tm + 384 ≤ 512) (j : Nat) :
    tcDataCell L g (.s16x32bx2 64)
        (tm + 128 * (i % 2) + g % L.block / 32 * 2 ^ 21) j =
      sCell (g / L.block) tm i (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) := by
  unfold tcDataCell TcShape.base TcShape.laneIn TcShape.columnIn TcShape.lanes laneBase
    chunkOffset sCell Sm.row Sm.half laneOf
  split_ifs with h1 <;> congr 1 <;> omega

theorem row_div6 (T : Nat) : Sm.row T / 6 = Sm.tokOf T := by
  have key : ∀ x : Nat, x < 64 → x * 43 / 256 = x / 6 := by decide
  unfold Sm.tokOf
  rw [key _ (by unfold Sm.row; omega)]

theorem row_mod6 (T : Nat) : Sm.row T % 6 = Sm.remOf T := by
  unfold Sm.remOf
  rw [← row_div6]
  omega

/-- **The S tile's load, at the softmax thread's state of iteration `i`, has a last QK MMA as the
read source of each of its cells** (the protocol layer's half of `SvPrem.score`). -/
structure SLoadSrc (Q : Params) (L : Launch) (X : Execution) : Prop where
  src : ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}, g < L.threads →
    ValidRow Q L g → St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .qk 7 ∧ dm.i = d.i ∧
      d.e.tm = dm.tm ∧
      ∀ j < 64, ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j)

/-- **`SvPrem.score` from the read source of the S load.** -/
theorem scoreEv_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hcomp : Complete L X) (hc : KvCopies Q L X)
    (ho : KvOrder Q L X) (hw : MmaWords Q L X) (hq : QTile Q L X) (hch : QkChain Q L X)
    (S : SLoadSrc Q L X) {g k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (hvr : ValidRow Q L g) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .ldS) :
    ScoreEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d.i e := by
  intro a vals sh hk j hj
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hev⟩ := Sm.shape_ldS (Interface.fired_sm hF) hs
  have hk' := hk
  rw [hev] at hk'
  simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk'
  obtain ⟨ha, hvv, hsh⟩ := hk'
  subst ha hvv hsh
  rw [hev] at he
  obtain ⟨m, pcm, dst, sp, acc, mask, dm, P, hmg, hmc, hmget, hmst, hms, hmi, hmtm, hrs⟩ :=
    S.src hg hvr hσ hs he
  have hdm0 : dm.tm = 0 := hw.tm (m := m) ⟨P, hmst⟩
  have hT : g % L.block < 128 := (hf.reach hg hσ).1
  have hte : Sm.tileAddr L g d = d.e.tm + 128 * (d.i % 2) + g % L.block / 32 * 2 ^ 21 :=
    Sm.tileAddr_eq hT (by omega) (Interface.sm_bw' hpre hX hf hg hσ (by rw [hs]; trivial))
  have hcell : tcDataCell L g (.s16x32bx2 64) (Sm.tileAddr L g d) j =
      sCell (g / L.block) dm.tm dm.i (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) := by
    rw [hte, hmtm, hmi]
    exact ldS_cell L g (by omega) j
  have hreq := Result.Out.cta_eq (L := L) (g := g) (g' := m.1) hmc
  have hvr' : QRowValid Q L m.1 (Sm.row (g % L.block)) := by
    obtain ⟨h1, h2⟩ := hvr
    refine ⟨h1, ?_⟩
    rw [row_div6, hreq.1]
    exact h2
  have hh2 : Sm.half (g % L.block) < 2 := by unfold Sm.half; omega
  have hld : X.TLd (g, k) (Sm.tileAddr L g d) vals' (.s16x32bx2 64) := ⟨_, he⟩
  have hcl : LoadCell L X (g, k) j (sCell (m.1 / L.block) dm.tm dm.i (Sm.row (g % L.block))
      (64 * Sm.half (g % L.block) + j)) :=
    ⟨_, vals', _, hld, by omega, by rw [hmc, ← hcell]⟩
  have hrs' : ReadSource L X .ld m (g, k) (sCell (m.1 / L.block) dm.tm dm.i
      (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j)) := by
    rw [hmc, ← hcell]
    exact hrs j hj
  have := score_load hpre hf hX hcomp hc ho hw hq hch hmg hmget hmst hms hvr'
    (c := 64 * Sm.half (g % L.block) + j) (by omega) hld hcl hrs'
  rw [this]
  have e1 : reqOf L m.1 = ProA.cta L g .z := hreq.1
  have e2 : splitOf L m.1 = ProA.cta L g .x := hreq.2.1
  have e3 : kvhOf L m.1 = ProA.cta L g .y := hreq.2.2
  have e4 : 128 * blkOf Q L m.1 dm.i + (64 * Sm.half (g % L.block) + j) =
      keyB Q (ProA.cta L g .x) d.i (Sm.half (g % L.block)) j := by
    unfold blkOf keyB
    rw [e2, hmi]
    omega
  have e5 : group * ProA.cta L g .y + Sm.remOf (g % L.block) =
      ProA.cta L g .y * 6 + Sm.remOf (g % L.block) := by
    unfold group
    omega
  rw [e1, row_div6, e3, row_mod6, e4, e5]

/-- **The exchange with the partner lane** (the protocol layer's premise): for the two shuffle
events of one iteration of a valid row's thread, the partner lane's state `dp` has the thread's
entry numbers and running maximum, the first shuffle returned its row maximum and the second its
sum of probabilities computed with the thread's maximum (`Sm.PeerExchange`), and its visible scores
are the other half's. -/
structure ExchPrem (Q : Params) (L : Launch) (X : Execution) : Prop where
  exch : ∀ {g k : Nat} {d : Sm.D} {e5 e6 : Event}, g < L.threads → ValidRow Q L g →
    X.get (g, k) = some e5 → X.get (g, k + 1) = some e6 →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 →
    ExchEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d e5 e6

/-- **`SvPrem` from the read source of the S load and the exchange with the partner lane.** -/
theorem svPrem_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hcomp : Complete L X) (hc : KvCopies Q L X)
    (ho : KvOrder Q L X) (hw : MmaWords Q L X) (hq : QTile Q L X) (hch : QkChain Q L X)
    (S : SLoadSrc Q L X) (E : ExchPrem Q L X)
    (hM : ∀ {g k : Nat} {d : Sm.D} {e : Event}, g < L.threads → X.get (g, k) = some e →
      St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 →
      ∀ m av bv cv r o, e.kind = .shfl m av bv cv r o → d.RealIn r) : SvPrem Q L X where
  score := fun hg hvr he hσ hs => scoreEv_of hpre hX hf hcomp hc ho hw hq hch S hg hvr he hσ hs
  exch := E.exch
  real := hM

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
