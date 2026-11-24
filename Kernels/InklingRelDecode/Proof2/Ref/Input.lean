-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Sound
public import Kernels.InklingRelDecode.Proof2.ProA.Ref
public import Kernels.InklingRelDecode.Proof2.ProA.Shape
public import Kernels.InklingRelDecode.Proof.Thread.ClassBtAddr
public import Lemmas.Kernel.Source.Launch
public import Lemmas.Flow.Final
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The prologue's loads read the launch: the expectation from the input source

At a prologue state of the thread machine that holds its reference (`ProA.PRef`), the event meets
`ProA.Expect` (`pro_expect`). The source is the read-only input assumption
(`Assumptions.inputReadOnly`): a read at one of its sites returns the launch byte wherever the
launch gives one, with no fact about the other events of the execution. The addresses are the
register table's (`ProA.shape`), in closed form from the inherited registers
(`Proof.ProA.cu_addrs`, `Proof.ProA.lb_addr`); a block-table load's block exists by the gate and
the request words (`Proof.ProA.gate_iters`). A query load reads two bytes by its shape alone. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof.ProA (cta)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem inputReadOnly_mem : Assumptions.inputReadOnly ∈ Assumptions.all := by
  simp [Assumptions.all]

/-- **A four-byte read at an input site of launch bytes of a word returns the word's bytes.** -/
theorem input_word (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc A x : Nat}
    {a : Acc} {bs : List (Option Byte)} (he : X.get i = some ⟨pc, .rd a bs⟩)
    (hs : Assumptions.inputReadSites.contains pc = true)
    (ha : a = Proof.EvD.wordAcc ⟨.global, 0, A⟩) (hlen : bs.length = 4)
    (hm : ∀ j < 4, m ⟨.global, 0, A + j⟩ = some (some ((b32 x).byteAt j))) :
    bs = (b32 x).toBytes.map some := by
  subst ha
  refine Frame.bytes_of_pointwise (by rw [hlen]; rfl) fun j hj => ?_
  have hj4 : j < 4 := by simpa [b32, Value.bytes] using hj
  exact (hX.asm _ inputReadOnly_mem) i pc _ bs he hs j (by simpa [Proof.EvD.wordAcc] using hj4)
    _ (by simpa [Loc.at, Proof.EvD.wordAcc] using hm j hj4)

/-- A block below `num_iters` is inside the request's blocks, which fit 24 bits. -/
theorem blk_index (hpre : Pre Q L m) (hg : g < L.threads) {j : Nat}
    (hj : j < Q.numIters (cta L g .z) (cta L g .x)) :
    cta L g .x + j * Q.splits < Q.blocks (cta L g .z) ∧ Q.blocks (cta L g .z) ≤ 2 ^ 24 := by
  obtain ⟨-, -, hz⟩ := Proof.ProA.cta_lt hpre hg
  have hs := hpre.splitsPos
  refine ⟨?_, ?_⟩
  · unfold Params.numIters at hj
    have h1 := (Nat.le_div_iff_mul_le hs).mp (show j + 1 ≤ _ from hj)
    have h2 : (j + 1) * Q.splits = j * Q.splits + Q.splits := by ring
    omega
  · have := hpre.seqRange _ hz
    unfold Params.blocks
    omega

theorem lb_old (b : Fin 3) (h : Fin 2) :
    (ProA.Site.lb b h).old = Proof.ProA.lbSite (2 * b.val + h.val) := by
  fin_cases b <;> fin_cases h <;> rfl

/-- **A prologue block-table load of a preloaded block returns the page of its slab.** -/
theorem lb_bytes (hpre : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hR : ProA.PRef Q L g tm bw d) {bb : Fin 3} {hh : Fin 2} (hsl : d.site = .lb bb hh) :
    Q.page (cta L g .z) (2 * (cta L g .x + (2 * bb.val + hh.val) / 2 * Q.splits) +
        (2 * bb.val + hh.val) % 2) < 2 ^ 32 ∧
      ∀ a bs, e.kind = .rd a bs → bs = (b32 (Q.page (cta L g .z)
        (2 * (cta L g .x + (2 * bb.val + hh.val) / 2 * Q.splits) +
          (2 * bb.val + hh.val) % 2))).toBytes.map some := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, hat, ⟨hi, hx⟩, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hpre hg) hX he hσ
  have hx' : d.site ≠ .exit := fun h => by simp [Code.gatedExit, ProA.exitOf, h] at hx
  have hev : ∀ a bs, e.kind = .rd a bs → ProA.Ev L g d e := by
    intro a bs hk
    obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
      cases o with
      | some u => exact ⟨u, rfl⟩
      | none =>
        rcases fires_none_ends hf with ⟨f, hk'⟩ | hk' <;> rw [hk] at hk' <;> cases hk'
    exact ProA.shape (Startup.inh L g Q tm) hx' hat hi hc hf
  have hpc : e.pc = d.site.pc := EventFrame.fires_source_pc hf
  have hargs : Proof.ProA.ArgsOk L g d.dt.pro := hi.args
  obtain ⟨hpro, ⟨w0, w1, w2⟩, hG, -⟩ := hR
  obtain ⟨site, dt⟩ := d
  have hz := (Proof.ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  simp only at hsl
  subst hsl
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = 2 * bb.val + hh.val := ⟨_, rfl⟩
  have hk6 : kk < 6 := by omega
  have hold : (ProA.Site.lb bb hh).old = Proof.ProA.lbSite kk := hkk ▸ lb_old bb hh
  have hafter : (Proof.ProA.lbSite kk).afterSk = true := by
    subst hkk; fin_cases bb <;> fin_cases hh <;> decide
  have hblk : Proof.ProA.lbSite kk ∈ Proof.ProA.blkSites bb.val := by
    subst hkk; fin_cases bb <;> fin_cases hh <;> decide
  have hspl := hpre.splitsRange
  have hsc := hpre.scalarsRange
  have hN : dt.pro.w71 = Q.splits := by
    simp only at hpro; rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hSt : dt.pro.w67 = Q.strideBt := by
    simp only at hpro; rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hB : dt.pro.btB = Q.btBase := by simp only at hpro; rw [hpro]; rfl
  have hne : Proof.ProA.lbSite kk ≠ .sMax ∧ Proof.ProA.lbSite kk ≠ .ldCu0 := by
    constructor <;> (intro h; rw [h] at hafter; simp [Proof.ProA.Site.afterSk] at hafter)
  simp only [ProA.D.old, hold] at w0 w1 w2 hG
  have hm : Proof.ProA.WordsMatch Q (cta L g .z) dt :=
    ⟨w0 hne.1 hne.2, w1 (.inl hafter), w2 hafter⟩
  obtain ⟨c0, c1, c2⟩ := Proof.ProA.gate_iters hpre hg hargs hN hm
  obtain ⟨g0, g1, g2⟩ := hG
  have hj : bb.val < Q.numIters (cta L g .z) (cta L g .x) := by
    fin_cases bb
    · exact c0 (g0 hblk)
    · exact c1 (g1 hblk).1 (g1 hblk).2
    · exact c2 (g2 hblk).1 (g2 hblk).2.1 (g2 hblk).2.2
  obtain ⟨hI1, hI2⟩ := blk_index hpre hg hj
  obtain ⟨hx, -, -⟩ := Proof.ProA.cta_lt hpre hg
  have hs2 : 2 * (cta L g .x + kk / 2 * Q.splits) + kk % 2 < 2 * Q.blocks (cta L g .z) := by
    have e1 : kk / 2 = bb.val := by omega
    have e2 : kk % 2 = hh.val := by omega
    rw [e1, e2]
    omega
  have hbt' := hpre.btIndexRange _ hz _ hs2
  have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (cta L g .z * Q.strideBt +
      (2 * (cta L g .x + kk / 2 * Q.splits) + kk % 2)) + j) := fun j hj =>
    .inr (.inr (.inr (.inr (.inr ⟨_, hz, _, hs2, j, hj, rfl⟩))))
  have hrr0 := hpre.readsRange _ (hrd 3 (by omega))
  have haddr := Proof.ProA.lb_addr L g dt hk6 (by omega)
    (by rw [hSt, hN]; rw [Nat.mul_comm] at hbt'; omega) (by rw [hN]; omega)
  rw [hSt, hN, hB] at haddr
  have hA : Proof.ProA.loadAddr L g dt (Proof.ProA.lbSite kk) = Q.btBase +
      4 * (cta L g .z * Q.strideBt + (2 * (cta L g .x + kk / 2 * Q.splits) + kk % 2)) := by
    rw [haddr, Nat.mod_eq_of_lt (by rw [Nat.mul_comm Q.strideBt]; omega)]
    rw [Nat.mul_comm Q.strideBt]
    congr 1
    omega
  have hpg : Q.page (cta L g .z) (2 * (cta L g .x + kk / 2 * Q.splits) + kk % 2) < 2 ^ 32 := by
    have h1 := hpre.slabInside _ hz _ hs2 0 (by unfold kvHeads; omega)
    have h2 := hpre.rowsRange
    have h3 := hpre.pageRowsPos
    have h4 := Nat.le_mul_of_pos_right
      (Q.page (cta L g .z) (2 * (cta L g .x + kk / 2 * Q.splits) + kk % 2)) h3
    omega
  subst hkk
  refine ⟨hpg, fun a bs hk => ?_⟩
  obtain ⟨bs', hl, he'⟩ := hev a bs hk
  obtain ⟨pc, kd⟩ := e
  simp only [Event.mk.injEq] at he'
  obtain ⟨rfl, rfl⟩ := he'
  simp only [Kind.rd.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  rw [hold, hA] at he
  have hsite : Assumptions.inputReadSites.contains (ProA.Site.lb bb hh).pc = true := by
    fin_cases bb <;> fin_cases hh <;> decide
  exact input_word hX he hsite rfl hl fun j hj => hpre.btInput _ hz _ hs2 j hj

/-- **The expectation of a prologue state holds**: its loads return the launch's words. -/
theorem pro_expect (hpre : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hR : ProA.PRef Q L g tm bw d) : ProA.Expect Q L g d e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, hat, ⟨hi, hx⟩, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hpre hg) hX he hσ
  have hx' : d.site ≠ .exit := fun h => by simp [Code.gatedExit, ProA.exitOf, h] at hx
  have hev : ∀ a bs, e.kind = .rd a bs → ProA.Ev L g d e := by
    intro a bs hk
    obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
      cases o with
      | some u => exact ⟨u, rfl⟩
      | none =>
        rcases fires_none_ends hf with ⟨f, hk'⟩ | hk' <;> rw [hk] at hk' <;> cases hk'
    exact ProA.shape (Startup.inh L g Q tm) hx' hat hi hc hf
  have hpc : e.pc = d.site.pc := EventFrame.fires_source_pc hf
  have hargs : Proof.ProA.ArgsOk L g d.dt.pro := hi.args
  have hR' := hR
  obtain ⟨hpro, ⟨w0, w1, w2⟩, hG, -⟩ := hR
  obtain ⟨site, dt⟩ := d
  have hz := (Proof.ProA.cta_lt hpre hg).2.2
  have hb := hpre.bRange
  cases site with
  | ld kk =>
    intro a bs hk
    obtain ⟨bs', hl, he'⟩ := hev a bs hk
    obtain ⟨pc, kd⟩ := e
    simp only [Event.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    simp only [Kind.rd.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨h0, h1, h2⟩ := Proof.ProA.cu_addrs hpre hg hargs
    have hcu : ∀ r ≤ Q.b, ∀ j < 4, Q.cuBase + 4 * r + j < 2 ^ 64 := fun r hr j hj =>
      lt_of_le_of_lt (by omega) (hpre.readsRange (Q.cuBase + 4 * r + 3)
        (.inr (.inr (.inr (.inl ⟨r, hr, 3, by omega, rfl⟩)))))
    have hsq : ∀ j < 4, Q.seqBase + 4 * cta L g .z + j < 2 ^ 64 := fun j hj =>
      lt_of_le_of_lt (by omega) (hpre.readsRange (Q.seqBase + 4 * cta L g .z + 3)
        (.inr (.inr (.inr (.inr (.inl ⟨_, hz, 3, by omega, rfl⟩))))))
    generalize hA0 : Proof.ProA.loadAddr L g dt (ProA.Site.ld kk).old = A at he
    fin_cases kk
    · change Proof.ProA.loadAddr L g dt .ldCu0 = A at hA0
      rw [h0, Nat.mod_eq_of_lt (by have := hcu _ hz.le 0; omega)] at hA0
      subst hA0
      exact input_word hX he (by decide) rfl hl fun j hj => hpre.cuInput _ hz.le j hj
    · change Proof.ProA.loadAddr L g dt .ldCu1 = A at hA0
      rw [h1, Nat.mod_eq_of_lt (by have := hcu _ hz 0; omega)] at hA0
      subst hA0
      exact input_word hX he (by decide) rfl hl fun j hj => hpre.cuInput _ hz j hj
    · change Proof.ProA.loadAddr L g dt .ldSk = A at hA0
      rw [h2, Nat.mod_eq_of_lt (by have := hsq 0; omega)] at hA0
      subst hA0
      exact input_word hX he (by decide) rfl hl fun j hj => hpre.seqInput _ hz j hj
  | lb bb hh =>
    obtain ⟨hpg, hb⟩ := lb_bytes hpre hX he hσ hR' (bb := bb) (hh := hh) rfl
    exact ⟨_, hpg, hb⟩
  | ldq _ =>
    intro a bs hk
    obtain ⟨bs', hl, he'⟩ := hev a bs hk
    rw [he'] at hk
    simp only [Kind.rd.injEq] at hk
    rw [← hk.2]
    exact hl
  | _ => trivial

end
end PTX.Kernels.InklingRelDecode.Proof2
