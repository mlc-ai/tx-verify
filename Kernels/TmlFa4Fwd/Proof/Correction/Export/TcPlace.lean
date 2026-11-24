-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcAddr
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcStates
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld1
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The places of the correction warps' collective `tcgen05` events

The ordinal of a collective `tcgen05` event of a correction lane is 25 per accepted rescale ballot
before it and its site's offset (`corr_tc_place`, from `corr_tcC`); a lane with a tile exits after
all of them (`corr_tc_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (cinj refV rvN toE rc)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The site is in a rescale stage. -/
def Correction.resc : Correction.Site → Option (Fin 2)
  | .rld st _ | .rldw st _ | .rst st _ | .rwait st => some st
  | _ => none

/-- The event's kind at a site, without its values. -/
def Correction.tcKind (L : Launch) (g : Nat) : Correction.Site → TcKind
  | .rld st c => .ld (accAddr L g st (16 * c.val)) [] .s32x32b
  | .rst st c => .st (accAddr L g st (16 * c.val)) [] .s32x32b
  | .fld st j => .ld (accAddr L g st (8 * j.val)) [] .s32x32b
  | .rwait _ => .waitSt
  | _ => .waitLd

open Correction (tw pend resc tcKind finc brv bnb vv)

/-- The collective `tcgen05` sites. -/
def tcSites : List Correction.Site :=
  allSites.filter fun s => decide (0 < tw s)

theorem corr_tab : tcSites.all (fun s => decide (pend s ≤ 25) &&
    (match resc s with
      | some st => decide (0 < pend s) && decide (finc s = 0) && decide (brv s = st.val + 1) &&
          inRound s.pc
      | none => decide (pend s = 0) && decide (0 ≤ finc s) && decide (finc s < 64) &&
          decide (brv s = 0) && tailR s) && decide (bnb s = (ptsOf (.nb 0)).countP (before s)) &&
    decide (CorrWarp.epi s = .ready 0) && s.hasUk && !Progress.Cr.late s && !s.noTile) = true := by
  decide +kernel

theorem corr_inj : tcSites.all (fun s => tcSites.all fun s' =>
    !(decide (resc s = resc s') && decide (pend s = pend s') && decide (finc s = finc s')) ||
      decide (s = s')) = true := by decide +kernel

theorem corr_tcEnd : pend (.exit true) = 0 ∧ finc (.exit true) = 64 ∧ brv (.exit true) = 0 ∧
    bnb (.exit true) = 2 ∧ (ptsOf (.nb 0)).countP inRound = 1 := by decide +kernel

theorem mem_tcSites {s : Correction.Site} (h : 0 < tw s) : s ∈ tcSites :=
  List.mem_filter.mpr ⟨mem_allSites s, by simpa using h⟩

/-- **The kind of a correction state's collective `tcgen05` event.** -/
theorem tcKind_of {d : Correction.Control.D} {pc : Nat} {tk : TcKind} {t : TState} {ins : Instr}
    {o : Option TState} (hev : Correction.Control.Ev p L g d ⟨pc, .tc tk⟩)
    (hc : isTcColl ⟨pc, .tc tk⟩ = true) (hk : d.site.isFst = false → d.k = kIn d.site)
    (hat : (Correction.Control.code p L g).AtD d t) (hcd : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc, .tc tk⟩ o) :
    0 < tw d.site ∧ tcStatic tk = tcKind L g d.site := by
  obtain ⟨site, v, k⟩ := d
  cases site
  case rld st c =>
    simp only [Control.Ev, Control.D.scheduler, Correction.Ev] at hev
    rcases hev with ⟨a, vals, sh, h⟩ | ⟨f, h⟩
    · cases h
      obtain ⟨rfl, rfl⟩ := rld_addr hat hcd hf rfl
      exact ⟨Nat.one_pos, rfl⟩
    · cases h
  case rldw st c =>
    have hk1 : k = 1 := hk rfl
    subst hk1
    have hl : Control.loadOk (.rld st c) (.rldw st c) true = true := by
      fin_cases st
      · exact Control.rld_table0 c
      · exact Control.rld_table1 c
    obtain ⟨ds, ta, hc', hw, -⟩ := Control.load_of_ok hl
    obtain rfl := Option.some.inj (hcd.symm.trans hc')
    obtain ⟨h1, h2, -⟩ := hat
    have hw' : Assumptions.all.any (·.tcLdWait t.pc) = true := h1 ▸ hw
    have hs : t.sub ≠ 0 := by
      rw [h2]
      exact Nat.one_ne_zero
    simp only [eventTmpl, tcLdTmpl, hw', ↓reduceIte, hs, Fires] at hf
    have he := congrArg Event.kind hf.1
    simp only [Kind.tc.injEq] at he
    subst he
    exact ⟨Nat.one_pos, rfl⟩
  case rst st c =>
    simp only [Control.Ev, Control.D.scheduler, Correction.Ev] at hev
    rcases hev with ⟨a, vals, sh, h⟩ | ⟨f, h⟩
    · cases h
      obtain ⟨rfl, rfl⟩ := rst_addr hat hcd hf rfl
      exact ⟨Nat.one_pos, rfl⟩
    · cases h
  case rwait st =>
    simp only [Control.Ev, Control.D.scheduler, Correction.Ev] at hev
    rcases hev with h | ⟨f, h⟩
    · cases h; exact ⟨Nat.one_pos, rfl⟩
    · cases h
  case fld st c =>
    simp only [Control.Ev, Control.D.scheduler, Correction.Ev] at hev
    rcases hev with ⟨a, vals, sh, h⟩ | ⟨f, h⟩
    · cases h
      obtain ⟨rfl, rfl⟩ := fld_addr hat hcd hf rfl
      exact ⟨Nat.one_pos, rfl⟩
    · cases h
  case fwl st c =>
    simp only [Control.Ev, Control.D.scheduler, Correction.Ev] at hev
    cases hev
    exact ⟨Nat.one_pos, rfl⟩
  case rvote st =>
    obtain ⟨_, _, h⟩ := hev
    cases h
  all_goals exfalso
  all_goals simp only [Control.Ev, Control.D.scheduler, Correction.Ev, Epilogue.Ev,
    Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals (first | contradiction | (simp only [reduceCtorEq] at *; done))

/-- The addresses are one for a warp. -/
theorem tcKind_warp (hp : Pre p L m) {h : Nat} (hw : SameWarp L g h) (s : Correction.Site) :
    tcKind L g s = tcKind L h s := by
  have hb := hp.block
  have hwi : g % L.block / 32 = h % L.block / 32 := hw.2
  have tab : ∀ x < 512, Arith32.shru (Arith32.andi (BitVec.ofNat 64 x) 127) 5 =
      Arith32.shru (Arith32.andi (BitVec.ofNat 64 (x / 32 * 32)) 127) 5 := by decide +kernel
  have hq : quarter L g = quarter L h := by
    have h1 := tab (g % L.block) (by rw [hb]; exact Nat.mod_lt _ (by decide))
    have h2 := tab (h % L.block) (by rw [hb]; exact Nat.mod_lt _ (by decide))
    rw [← hwi] at h2
    simp only [quarter, rowW]
    rw [tidW_eq hp, tidW_eq hp]
    exact h1.trans h2.symm
  have hc : ∀ st n, accAddr L g st n = accAddr L h st n := fun st n => by
    simp only [accAddr, tm0, tm1, hq]
  cases s <;> simp only [tcKind, hc]

private theorem lt_half {r : Nat} {B : Int} (h : (r : Int) + 1 < B) : r < rvN B / 2 := by
  simp only [rvN]
  split <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X)
include hp hX hFw hub

/-- The rescale ballots, the vote ordinal and the tile at a state in the rounds or the tail. -/
theorem corr_tc_place (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k pc : Nat} {tk : TcKind} (he : X.get (g, k) = some ⟨pc, .tc tk⟩)
    (hc : isTcColl ⟨pc, .tc tk⟩ = true) :
    ∃ s ∈ tcSites, ∃ R, pc = s.pc ∧ tcStatic tk = tcKind L g s ∧ tileC p L g = some R ∧
      (((X.tr g).take k).countP isTcColl : Int) + pend s =
        25 * ((X.tr g).take k).countP isRv + finc s ∧
      (∀ st, resc s = some st → ∃ r < R, ((X.tr g).take k).countP isRb = 2 * r + st.val + 1 ∧
        ordEv X isRb isRv g (((X.tr g).take k).countP isRb - 1) = true) ∧
      (resc s = none → ((X.tr g).take k).countP isRb = 2 * R) := by
  have hg := Frame.lt_of_get hX he
  have hne : ∀ f, (⟨pc, .tc tk⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hne with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · rw [start_tcFree hev hi.2] at hc
    cases hc
  obtain ⟨hRc, hF⟩ := hR h0
  obtain ⟨r, ℓ, hQ⟩ := hRc.counts
  obtain ⟨t, ins, o, hat, -, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hne
  obtain ⟨htw, hkd⟩ := tcKind_of hev hc hQ.sub hat hcd hf
  have hs := mem_tcSites htw
  have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ hne
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hT : TcC X g k d.site n := by
    rcases corr_tcC hp hX hFw hub hg hw hw1 k hk _ hσ with ⟨s, n', h, -⟩ | ⟨d', n', h, hT⟩
    · cases h
    · cases h; exact hT
  have ht := List.all_eq_true.mp corr_tab d.site hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ht
  obtain ⟨⟨⟨⟨⟨⟨-, hcase⟩, hbn⟩, hep⟩, huk⟩, hl⟩, hnt⟩ := ht
  have hnb0 := hQ.cnt (.nb 0) (by simp)
  have hnb : n (.corr (.nb 0)) = (ptsOf (.nb 0)).countP (before d.site) +
      r * (ptsOf (.nb 0)).countP inRound := hnb0
  obtain ⟨-, -, -, -, e5⟩ := corr_tcEnd
  rw [e5] at hnb
  have hball := hT.ballots
  -- the tile
  obtain ⟨rv, -, -, hFE, hu⟩ := hF
  simp only [Epilogue.Fits, toE, show d.scheduler.site = d.site from rfl, hep] at hFE
  obtain ⟨R0, bal, hC, hq0, hq1⟩ := hFE
  have hBs : Bs p L g d.v.scheduler = Bs p L g (refV p L g R0 bal) :=
    CorrWarp.bs_ref (d := d.scheduler) hC hq0 hq1 (hu huk)
  refine ⟨d.site, hs, _, hpc, hkd, tileC_of hC.1, hT.tc, fun st hst => ?_, fun hst => ?_⟩
  · rw [hst] at hcase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcase
    obtain ⟨⟨⟨hpe, -⟩, hbr⟩, hin⟩ := hcase
    have hlp : (r : Int) + 1 < Bs p L g d.v.scheduler := (hQ.loop hin).1
    rw [hBs] at hlp
    refine ⟨r, lt_half hlp, by omega, (hT.taken hpe).2⟩
  · rw [hst] at hcase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcase
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hbr⟩, hta⟩ := hcase
    have htl : (r : Int) + 1 = Bs p L g d.v.scheduler ∨ (r = 0 ∧ Bs p L g d.v.scheduler < 2) :=
      hQ.tail hta
    rw [hBs] at htl
    rw [rvN_half htl]
    omega

/-- **A correction lane with a tile exits after its collective `tcgen05` events.** -/
theorem corr_tc_exit (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k pc R : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) (hT : tileC p L g = some R) :
    ((X.tr g).take k).countP isTcColl = 25 * ((X.tr g).take k).countP isRv + 64 ∧
      ((X.tr g).take k).countP isRb = 2 * R := by
  have hg := Frame.lt_of_get hX he
  have hne : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hne with ⟨s, n, -, -, hJ, -, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · exact (start_noexit hJ hev).elim
  obtain ⟨hRc, hF⟩ := hR h0
  have hevd : Correction.Ev p L g d.scheduler ⟨pc, .exit⟩ :=
    hev.data_or_vote.resolve_right (by rintro ⟨_, _, h⟩; cases h)
  obtain ⟨site, v, kk⟩ := d
  obtain ⟨l, hl⟩ := corr_exit_site hevd
  simp only at hl
  subst hl
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hTC : TcC X g k (.exit l) n := by
    rcases corr_tcC hp hX hFw hub hg hw hw1 k hk _ hσ with ⟨s, n', h, -⟩ | ⟨d', n', h, hT⟩
    · cases h
    · cases h; exact hT
  have hPk : ∃ R bal, Picked p L g R bal := by
    by_contra hn
    rw [tileC_none hn] at hT
    cases hT
  cases l with
  | false =>
    exfalso
    obtain ⟨rv, -, -, hFE, -⟩ := hF
    exact noPicked_exit hFE rfl hPk
  | true =>
    obtain ⟨R0, bal, hPk', h2, h3⟩ :=
      corr_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ h0 rfl
    rw [tileC_of hPk'] at hT
    simp only [Option.some.injEq] at hT
    obtain ⟨e1, e2, e3, e4, -⟩ := corr_tcEnd
    have h1 := hTC.tc
    have h4 := hTC.ballots
    rw [e1, e2] at h1
    rw [e3, e4] at h4
    rw [← h3] at hT
    constructor <;> omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
