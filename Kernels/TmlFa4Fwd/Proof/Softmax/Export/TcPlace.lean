-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Soft
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcAddr
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcCount
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of the softmax warps' collective `tcgen05` events

The ordinal of a collective `tcgen05` event of a softmax lane is the number its site and its rounds
give (`softN`), below the tile's total (`soft_tc_place`); a lane with a tile exits after the total
(`soft_tc_exit`). So the ordinal determines the site, and two lanes of a warp agree
(`soft_tc_uniform`, `soft_tc_unexited`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A site of a collective `tcgen05` event. -/
inductive TcS where
  | ld (r : Rd) (c : Fin 4)
  | ldw (c : Fin 4)
  | stw (r : Rd)
  | st (r : Rd) (q : Fin 4)
  | wt (r : Rd) (k : Fin 2)
  deriving DecidableEq

/-- The sites. -/
def TcS.all : List TcS :=
  List.flatten [allRd.flatMap fun r => (List.finRange 4).map (.ld r), (List.finRange 4).map .ldw,
    [.stw .first, .stw .bias], allRd.flatMap fun r => (List.finRange 4).map (.st r),
    allRd.flatMap fun r => (List.finRange 2).map (.wt r)]

/-- The site of the code. -/
def TcS.site : TcS → Site
  | .ld r c => .sld r c
  | .ldw c => .sldw c
  | .stw r => .pst r 0
  | .st r q => .pst r q
  | .wt r k => .pwst r k

/-- Whether the event is at sub-step 0 of its site. -/
def TcS.z : TcS → Bool
  | .ldw _ => false
  | .st r q => decide (r = .plain ∨ q ≠ 0)
  | _ => true

def TcS.rd : TcS → Rd
  | .ldw _ => .plain
  | .ld r _ | .stw r | .st r _ | .wt r _ => r

/-- The events of the round before the site's. -/
def TcS.off : TcS → Nat
  | .ld .plain c => 2 * c.val
  | .ld _ c => c.val
  | .ldw c => 2 * c.val + 1
  | .stw _ => 4
  | .st r q => (if r = .plain then 8 else 5) + q.val + if q = 3 then 1 else 0
  | .wt r k => (if r = .plain then 11 else 8) + 2 * k.val

/-- The ordinal of a site's event after `rb` biased and `rp` plain rounds. -/
def softN (s : TcS) (rb rp : Nat) : Nat :=
  match s.rd with
  | .first => s.off
  | .bias => 11 + 11 * rb + s.off
  | .plain => 11 + 11 * rb + 14 * rp + s.off

/-- The event's kind without its values. -/
def TcS.kind (L : Launch) (g : Nat) : TcS → TcKind
  | .ld _ c => .ld (colAddr L g (32 * c.val)) [] .s32x32b
  | .ldw _ | .stw _ => .waitLd
  | .st _ q => .st (colAddr L g (64 + 16 * q.val)) [] .s32x32b
  | .wt _ _ => .waitSt

/-- The classes' counts before a site. -/
def tcBase (lz : Bool) (s : Site) : Int :=
  (ptsOf lz .tcld).countP (before s) + (ptsOf lz .tcst).countP (before s) +
    6 * (ptsOf lz .nb).countP (before s) - 3 * (ptsOf lz .sb).countP (before s)

theorem tc_tab : [false, true].all (fun lz => TcS.all.all fun s =>
    decide (tcBase lz s.site + tcCorr s.site s.z = softN s 0 0) &&
    (inBias s.site.pos == decide (s.rd = .bias)) &&
    (inPlain s.site.pos == decide (s.rd = .plain)) &&
    (preR s.site == decide (s.rd = .first))) = true := by decide +kernel

theorem tc_rounds : [false, true].all (fun lz =>
    decide ((ptsOf lz .tcld).countP inBias = 4) && decide ((ptsOf lz .tcst).countP inBias = 4) &&
    decide ((ptsOf lz .nb).countP inBias = 1) && decide ((ptsOf lz .sb).countP inBias = 1) &&
    decide ((ptsOf lz .tcld).countP inPlain = 4) && decide ((ptsOf lz .tcst).countP inPlain = 4) &&
    decide ((ptsOf lz .nb).countP inPlain = 1) && decide ((ptsOf lz .sb).countP inPlain = 0) &&
    decide (tcBase lz (.exit true) + tcCorr (.exit true) true = 11) &&
    decide ((ptsOf lz .nb).countP (before (.exit true)) = 2) &&
    decide ((ptsOf lz .sb).countP (before (.exit true)) = 1)) = true := by decide +kernel

theorem mem_tcAll (s : TcS) (h : s ≠ .stw .plain) : s ∈ TcS.all := by
  cases s with
  | ld r c => clear h; revert c; cases r <;> decide
  | ldw c => clear h; revert c; decide
  | stw r => cases r <;> first | decide | exact absurd rfl h
  | st r q => clear h; revert q; cases r <;> decide
  | wt r k => clear h; revert k; cases r <;> decide

/-- The offsets determine the site of a round. -/
theorem off_inj : TcS.all.all (fun s => TcS.all.all fun s' =>
    !(decide (s.rd = s'.rd) && decide (s.off = s'.off)) || decide (s = s')) = true := by
  decide +kernel

theorem off_lt : TcS.all.all (fun s =>
    decide (s.off < if s.rd = .plain then 14 else 11)) = true := by
  decide +kernel

theorem off_inj' {s s' : TcS} (hs : s ∈ TcS.all) (hs' : s' ∈ TcS.all) (hr : s.rd = s'.rd)
    (ho : s.off = s'.off) : s = s' := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp off_inj s hs) s' hs'
  simpa [hr, ho] using h

private theorem st_z : ∀ (r : Rd) (q k : Fin 4), ¬ ((Site.pst r q).delayed && k.val == 0) = true →
    tcCorr (.pst r q) (k == 0) = tcCorr (TcS.st r q).site (TcS.st r q).z := by
  intro r
  cases r <;> decide

set_option maxHeartbeats 4000000 in
/-- **The site of a softmax state's collective `tcgen05` event**, with its kind. -/
theorem tcS_of {d : Softmax.Control.D} {pc : Nat} {tk : TcKind} {t : TState} {ins : Instr}
    {o : Option TState} (hev : Softmax.Ev p L g d ⟨pc, .tc tk⟩)
    (hc : isTcColl ⟨pc, .tc tk⟩ = true) (hw : ∀ c, d.site = .sldw c → d.k = 1)
    (hat : (Softmax.Control.code p L g).AtD d t) (hcd : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc, .tc tk⟩ o) :
    ∃ s ∈ TcS.all, d.site = s.site ∧ tcCorr d.site (d.k == 0) = tcCorr s.site s.z ∧
      tcStatic tk = s.kind L g := by
  obtain ⟨site, v, k, acc⟩ := d
  cases site
  case sld r c =>
    simp only [Softmax.Control.D.scheduler, Softmax.Ev, tcLdOrUb] at hev
    rcases hev with ⟨a, vals, sh, hk⟩ | ⟨f, hk⟩
    · cases hk
      obtain ⟨rfl, rfl⟩ := sld_addr (v := v.scheduler) hat hcd hf rfl
      exact ⟨.ld r c, mem_tcAll _ (by simp), rfl, by cases r <;> rfl, rfl⟩
    · cases hk
  case sldw c =>
    have hk1 := hw c rfl
    simp only at hk1
    subst hk1
    simp only [Softmax.Control.D.scheduler, Softmax.Ev, Fin.isValue, Fin.val_one, BEq.rfl,
      ↓reduceIte] at hev
    rcases hev with hk | ⟨f, hk⟩
    · cases hk
      exact ⟨.ldw c, mem_tcAll _ (by simp), rfl, rfl, rfl⟩
    · cases hk
  case pst r q =>
    simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev
    replace hev : if ((Site.pst r q).delayed && k.val == 0) = true then
        Kind.tc tk = Kind.tc .waitLd else (∃ a vals sh, Kind.tc tk = Kind.tc (.st a vals sh)) ∨
          ∃ f, Kind.tc tk = Kind.ub f := hev
    split at hev
    · rename_i hd
      change ((Site.pst r q).delayed && k.val == 0) = true at hd
      cases hev
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨hd, hk0⟩ := hd
      have hk0' : k = 0 := Fin.ext hk0
      subst hk0'
      cases r <;> fin_cases q <;> simp [Site.delayed] at hd
      · exact ⟨.stw .first, by decide, rfl, rfl, rfl⟩
      · exact ⟨.stw .bias, by decide, rfl, rfl, rfl⟩
    · rename_i hd
      change ¬ ((Site.pst r q).delayed && k.val == 0) = true at hd
      rcases hev with ⟨a, vals, sh, hk⟩ | ⟨f, hk⟩
      · cases hk
        obtain ⟨rfl, rfl⟩ := pst_addr (v := v.scheduler) hat hcd hf rfl
        exact ⟨.st r q, mem_tcAll _ (by simp), rfl, st_z r q k hd, rfl⟩
      · cases hk
  case pwst r k' =>
    simp only [Softmax.Control.D.scheduler, Softmax.Ev] at hev
    rcases hev with hk | ⟨f, hk⟩
    · cases hk
      exact ⟨.wt r k', mem_tcAll _ (by simp), rfl, rfl, rfl⟩
    · cases hk
  all_goals exfalso
  all_goals simp only [Softmax.Control.D.scheduler, Softmax.Ev, Epilogue.Ev, Softmax.Site.toE]
    at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (first | contradiction | (simp only [reduceCtorEq] at *; done))

/-- **The ordinal a place gives.** -/
theorem softN_of {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp N : Nat} {s : TcS} {z : Bool}
    (hQ : Softmax.RefQ p L g d c rb rp) (hs : s ∈ TcS.all) (hd : d.site = s.site)
    (hz : tcCorr d.site z = tcCorr s.site s.z)
    (hN : (N : Int) = c .tcld + c .tcst + 6 * c .nb - 3 * c .sb + tcCorr d.site z) :
    N = softN s rb rp ∧ inBias d.site.pos = decide (s.rd = .bias) ∧
      inPlain d.site.pos = decide (s.rd = .plain) ∧ preR d.site = decide (s.rd = .first) := by
  have hl : lz L g ∈ [false, true] := by cases lz L g <;> simp
  have t1 := List.all_eq_true.mp (List.all_eq_true.mp tc_tab _ hl) s hs
  have t2 := List.all_eq_true.mp tc_rounds _ hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t1 t2
  obtain ⟨⟨⟨h0, hB⟩, hP⟩, hR⟩ := t1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, p1⟩, p2⟩, p3⟩, p4⟩, -⟩, -⟩, -⟩ := t2
  have c1 := hQ.cnt .tcld rfl
  have c2 := hQ.cnt .tcst rfl
  have c3 := hQ.cnt .nb rfl
  have c4 := hQ.cnt .sb rfl
  have hpre := hQ.pre
  have hbias := hQ.bias
  unfold passed at c1 c2 c3 c4
  rw [hz] at hN
  rw [hd] at c1 c2 c3 c4 hpre hbias ⊢
  rw [b1, p1] at c1
  rw [b2, p2] at c2
  rw [b3, p3] at c3
  rw [b4, p4] at c4
  rw [hR] at hpre
  rw [hB] at hbias
  refine ⟨?_, hB, hP, hR⟩
  simp only [tcBase] at h0
  generalize (ptsOf (lz L g) .tcld).countP (before s.site) = x1 at *
  generalize (ptsOf (lz L g) .tcst).countP (before s.site) = x2 at *
  generalize (ptsOf (lz L g) .nb).countP (before s.site) = x3 at *
  generalize (ptsOf (lz L g) .sb).countP (before s.site) = x4 at *
  generalize tcCorr s.site s.z = y at *
  clear hd hz hB hP hR hQ b1 b2 b3 b4 p1 p2 p3 p4
  have hrd : s.rd = .first ∨ s.rd = .bias ∨ s.rd = .plain := by cases s.rd <;> simp
  rcases hrd with h | h | h
  · obtain ⟨h1, h2⟩ := hpre (by simp [h])
    subst h1 h2
    simp only [softN, h] at h0 ⊢
    omega
  · obtain ⟨h2, -⟩ := hbias (by simp [h])
    subst h2
    simp only [softN, h] at h0 ⊢
    omega
  · simp only [softN, h] at h0 ⊢
    omega

/-- **The total at the end of a lane with a tile.** -/
theorem softN_exit {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp N B P : Nat}
    (hQ : Softmax.RefQ p L g d c rb rp) (hd : d.site = .exit true)
    (hN : (N : Int) = c .tcld + c .tcst + 6 * c .nb - 3 * c .sb + tcCorr (.exit true) true)
    (hsb : c .sb = 1 + B) (hnb : c .nb = 2 + B + P) : N = 11 + 11 * B + 14 * P := by
  have hl : lz L g ∈ [false, true] := by cases lz L g <;> simp
  have t2 := List.all_eq_true.mp tc_rounds _ hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at t2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, p1⟩, p2⟩, p3⟩, p4⟩, h11⟩, x1⟩, x2⟩ := t2
  have c1 := hQ.cnt .tcld rfl
  have c2 := hQ.cnt .tcst rfl
  have c3 := hQ.cnt .nb rfl
  have c4 := hQ.cnt .sb rfl
  unfold passed at c1 c2 c3 c4
  rw [hd] at c1 c2 c3 c4
  rw [b1, p1] at c1
  rw [b2, p2] at c2
  rw [b3, p3, x1] at c3
  rw [b4, p4, x2] at c4
  unfold tcBase at h11
  rw [x1, x2] at h11
  generalize (ptsOf (lz L g) .tcld).countP (before (.exit true)) = y1 at *
  generalize (ptsOf (lz L g) .tcst).countP (before (.exit true)) = y2 at *
  generalize tcCorr (.exit true) true = y at *
  clear b1 b2 b3 b4 p1 p2 p3 p4 x1 x2 hl hd hQ
  omega

/-- The ordinals determine the round's part and the offset. -/
theorem softN_inj {s s' : TcS} {rb rb' rp rp' B P : Nat} (hN : softN s rb rp = softN s' rb' rp')
    (o1 : s.off < if s.rd = .plain then 14 else 11)
    (o2 : s'.off < if s'.rd = .plain then 14 else 11)
    (hb1 : s.rd = .bias → rb < B) (hb2 : s'.rd = .bias → rb' < B)
    (hq1 : s.rd = .plain → rb = B ∧ rp < P) (hq2 : s'.rd = .plain → rb' = B ∧ rp' < P) :
    s.rd = s'.rd ∧ s.off = s'.off := by
  unfold softN at hN
  generalize s.rd = r at *
  generalize s'.rd = r' at *
  generalize s.off = o at *
  generalize s'.off = o' at *
  cases r <;> cases r' <;> simp at hN o1 o2 hb1 hb2 hq1 hq2 ⊢ <;> omega

/-- The ordinals are below the tile's total. -/
theorem softN_lt {s : TcS} {rb rp B P : Nat} (o1 : s.off < if s.rd = .plain then 14 else 11)
    (hb1 : s.rd = .bias → rb < B) (hq1 : s.rd = .plain → rb = B ∧ rp < P) :
    softN s rb rp < 11 + 11 * B + 14 * P := by
  unfold softN
  generalize s.rd = r at *
  generalize s.off = o at *
  cases r <;> simp at o1 hb1 hq1 ⊢ <;> omega

/-- The addresses are one for a warp. -/
theorem kind_warp (hp : Pre p L m) {h : Nat} (hw : SameWarp L g h) (s : TcS) :
    s.kind L g = s.kind L h := by
  have hb := hp.block
  have hwi : g % L.block / 32 = h % L.block / 32 := hw.2
  have tab : ∀ x < 512, Arith32.andi (Arith32.shl (BitVec.ofNat 64 x) 16) 6291456 =
      Arith32.andi (Arith32.shl (BitVec.ofNat 64 (x / 32 * 32)) 16) 6291456 := by decide +kernel
  have ht : tmS L g = tmS L h := by
    have hs : stg L g = stg L h := by simp only [stg, warpW, hwi]
    have hq : Arith32.andi (Arith32.shl (tidW L g) 16) 6291456 =
        Arith32.andi (Arith32.shl (tidW L h) 16) 6291456 := by
      have h1 := tab (g % L.block) (by rw [hb]; exact Nat.mod_lt _ (by decide))
      have h2 := tab (h % L.block) (by rw [hb]; exact Nat.mod_lt _ (by decide))
      rw [← hwi] at h2
      rw [tidW_eq hp, tidW_eq hp]
      exact h1.trans h2.symm
    simp only [tmS, hs, hq]
  have hc : ∀ n, colAddr L g n = colAddr L h n := fun n => by unfold colAddr; rw [ht]
  cases s <;> simp only [TcS.kind, hc]

private theorem lt_toNat {r : Nat} {n : Int} (h : (r : Int) < n) : r < n.toNat := by omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The place of a softmax lane's collective `tcgen05` event.** -/
theorem soft_tc_place (hw : Prologue.warpIndex L g < 8) {k pc : Nat} {tk : TcKind}
    (he : X.get (g, k) = some ⟨pc, .tc tk⟩) (hc : isTcColl ⟨pc, .tc tk⟩ = true) :
    ∃ s ∈ TcS.all, ∃ rb rp B P, pc = s.site.pc ∧ tcStatic tk = s.kind L g ∧
      tileS p L g = some (B, P) ∧ ((X.tr g).take k).countP isTcColl = softN s rb rp ∧
      (s.rd = .bias → rb < B) ∧ (s.rd = .plain → rb = B ∧ rp < P) := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .tc tk⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · rw [start_tcFree hev hi.2] at hc
    cases hc
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
  obtain ⟨t, ins, o, hat, -, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  obtain ⟨s, hs, hd, hz, hkd⟩ := tcS_of hev.1 hc hQ.wait hat hcd hf
  have hN := soft_tc hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0
  have l1 := hLk .tcld rfl
  have l2 := hLk .tcst rfl
  have l3 := hLk .nb rfl
  have l4 := hLk .sb rfl
  rw [← l1, ← l2, ← l3, ← l4] at hN
  obtain ⟨hN', hB, hP, -⟩ := softN_of hQ hs hd hz hN
  have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ hub
  have tile : ∃ R bal, Picked p L g R bal ∧ nB p L g d.v.scheduler = nB p L g (refVS p L g R bal) ∧
      nP p L g d.v.scheduler = nP p L g (refVS p L g R bal) := by
    obtain ⟨hFE, hu⟩ := hF
    have hep : SmWarp.epi d.site = .ready 0 ∧ d.site.hasUk = true := by
      rw [hd]
      cases s <;> exact ⟨rfl, rfl⟩
    simp only [Epilogue.Fits, SmWarp.toE, show d.scheduler.site = d.site from rfl, hep.1] at hFE
    obtain ⟨R, bal, hC, h0, h1⟩ := hFE
    exact ⟨R, bal, hC.1, nBP_ref (d := d.scheduler) hC h0 h1 (hu hep.2)⟩
  obtain ⟨R, bal, hPk, eB, eP⟩ := tile
  refine ⟨s, hs, rb, rp, _, _, by rw [hpc, hd], hkd, tileS_of hPk, hN', fun h => ?_, fun h => ?_⟩
  · have hb := hQ.bias (hB.trans (decide_eq_true h))
    obtain ⟨-, -, hb, -⟩ := hb
    have hb' : (rb : Int) < nB p L g d.v.scheduler := hb
    rw [eB] at hb'
    exact lt_toNat hb'
  · have hb := hQ.plain (hP.trans (decide_eq_true h))
    obtain ⟨-, h1, -, h2⟩ := hb
    have h1' : (rp : Int) < nP p L g d.v.scheduler := h1
    have h2' : Done rb (nB p L g d.v.scheduler) := h2
    have h3 := done_toNat h2'
    rw [eB] at h3
    rw [eP] at h1'
    exact ⟨h3.symm, lt_toNat h1'⟩

/-- **A softmax lane with a tile exits after all its tile's collective `tcgen05` events.** -/
theorem soft_tc_exit (hw : Prologue.warpIndex L g < 8) {k pc B P : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (hT : tileS p L g = some (B, P)) :
    ((X.tr g).take k).countP isTcColl = 11 + 11 * B + 14 * P := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, hJ, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exact (start_noexit hJ hev).elim
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
  obtain ⟨l, hl⟩ := soft_exit_site' hev.1
  have hl' : d.site = .exit l := hl
  have hN := soft_tc hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0
  have hPk : ∃ R bal, Picked p L g R bal := by
    by_contra hn
    rw [tileS_none hn] at hT
    cases hT
  cases l with
  | false =>
    exfalso
    obtain ⟨hFE, -⟩ := hF
    exact noPicked_exit (d := SmWarp.toE d) hFE
      (by simp only [SmWarp.toE, show d.scheduler.site = d.site from rfl, hl']; rfl) hPk
  | true =>
    obtain ⟨R, bal, hPk', hsb, hnb⟩ :=
      soft_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0 (by rw [hl']; rfl)
    rw [tileS_of hPk'] at hT
    simp only [Option.some.injEq, Prod.mk.injEq] at hT
    obtain ⟨hB, hP⟩ := hT
    have l1 := hLk .tcld rfl
    have l2 := hLk .tcst rfl
    have l3 := hLk .nb rfl
    have l4 := hLk .sb rfl
    rw [← l1, ← l2, ← l3, ← l4] at hN
    rw [← l3] at hnb
    rw [← l4] at hsb
    have hz : tcCorr d.site (d.k == 0) = tcCorr (.exit true) true := by rw [hl']; rfl
    rw [hz] at hN
    have h := softN_exit hQ hl hN hsb hnb
    rw [hB, hP] at h
    exact h

/-- **The softmax warps' collective `tcgen05` events agree across a warp.** -/
theorem soft_tc_uniform {e f : EvId} {k pc pc' : Nat} {ke kf : TcKind} (hw : SameWarp L e.1 f.1)
    (h8 : Prologue.warpIndex L e.1 < 8) (hke : X.TcK e k) (hkf : X.TcK f k)
    (he : X.get e = some ⟨pc, .tc ke⟩) (hf : X.get f = some ⟨pc', .tc kf⟩) :
    pc = pc' ∧ tcStatic ke = tcStatic kf := by
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨ev, he', hme⟩, hc⟩ := hke
  obtain ⟨⟨fv, hf', hmf⟩, hc'⟩ := hkf
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  have h8' : Prologue.warpIndex L h < 8 := by
    have : Prologue.warpIndex L g = Prologue.warpIndex L h := hw.2
    exact this ▸ h8
  obtain ⟨s, hs, rb, rp, B, P, hp1, hk1, hT1, hN1, hb1, hq1⟩ := soft_tc_place hp hX hFw h8 he hme
  obtain ⟨s', hs', rb', rp', B', P', hp2, hk2, hT2, hN2, hb2, hq2⟩ :=
    soft_tc_place hp hX hFw h8' hf hmf
  rw [tileS_warp (p := p) hw.1.2.2 hw.2, hT2] at hT1
  simp only [Option.some.injEq, Prod.mk.injEq] at hT1
  obtain ⟨rfl, rfl⟩ := hT1
  simp only at hc hc'
  have hN : softN s rb rp = softN s' rb' rp' := by rw [← hN1, ← hN2, hc, hc']
  have o1 := of_decide_eq_true (List.all_eq_true.mp off_lt s hs)
  have o2 := of_decide_eq_true (List.all_eq_true.mp off_lt s' hs')
  have key : s = s' := by
    have hrd := softN_inj hN o1 o2 hb1 hb2 hq1 hq2
    exact off_inj' hs hs' hrd.1 hrd.2
  subst key
  exact ⟨by rw [hp1, hp2], by rw [hk1, hk2, kind_warp hp hw]⟩

/-- **A softmax lane exits after its warp's collective `tcgen05` events.** -/
theorem soft_tc_unexited {e f : EvId} {k : Nat} (hw : SameWarp L e.1 f.1)
    (h8 : Prologue.warpIndex L e.1 < 8) (hke : X.TcK e k) : ¬ X.ExitedShort isTcColl f k := by
  rintro ⟨⟨pcx, hx⟩, hle⟩
  obtain ⟨g, i⟩ := e
  obtain ⟨h, j⟩ := f
  obtain ⟨⟨⟨pc, kd⟩, he, hme⟩, hc⟩ := hke
  obtain ⟨tk, rfl⟩ := isTcColl_kind hme
  have h8' : Prologue.warpIndex L h < 8 := by
    have : Prologue.warpIndex L g = Prologue.warpIndex L h := hw.2
    exact this ▸ h8
  obtain ⟨s, hs, rb, rp, B, P, -, -, hT1, hN1, hb1, hq1⟩ := soft_tc_place hp hX hFw h8 he hme
  rw [tileS_warp (p := p) hw.1.2.2 hw.2] at hT1
  have hN2 : ((X.tr h).take j).countP isTcColl = 11 + 11 * B + 14 * P :=
    soft_tc_exit hp hX hFw h8' hx hT1
  have hsub : ((X.tr h).take j).countP isTcColl ≤ (X.tr h).countP isTcColl :=
    (List.take_sublist _ _).countP_le
  have o1 := of_decide_eq_true (List.all_eq_true.mp off_lt s hs)
  have hlt := softN_lt o1 hb1 hq1
  have hc' : ((X.tr g).take i).countP isTcColl = k := hc
  have hN1' : ((X.tr g).take i).countP isTcColl = softN s rb rp := hN1
  have hle' : (X.tr h).countP isTcColl ≤ k := hle
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
