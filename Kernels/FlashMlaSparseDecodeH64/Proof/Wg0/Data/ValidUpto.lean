-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.LdStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Lemmas.Flow.RoleStep
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # A lane's prefix is valid up to a live event

`w0_upto`: along the lane up to its event `k` with a live thread state there, every prefix is
valid and the data machine's states hold their loaded words (`LdOk`): the induction takes
`w0_valid_snoc` over each event (none before `k` is undefined behaviour) and `ldOk_step` over each
data step. -/

/-! # The data machine's step along a lane

`w0_data_step`: the state of warpgroup 0's data machine after an event is the data step of the
state before it. -/

/-! # The event at a state of the data machine

An event that is no undefined behaviour is at its state's pc and has the kind its site's shape
gives (`w0_state_ev`): a score, accumulator or `old` load is a `32x32b` Tensor Memory load, the
validity, peer, exchange and row-sum reads are reads. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0.Data

theorem sel_range {s : Site} (h : ((∃ a k, s = .sld a k) ∨ (∃ k, s = .rld k) ∨ ∃ k, s = .old k) ∨
    (s = .vm ∨ (∃ k, s = .pld k) ∨ s = .mld ∨ s = .eld)) : 103 ≤ s.pc ∧ s.pc < 1842 := by
  rcases h with (⟨a, k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩) | (rfl | ⟨k, rfl⟩ | rfl | rfl)
  · cases a <;> fin_cases k <;> simp [Site.pc]
  · fin_cases k <;> simp [Site.pc]
  · fin_cases k <;> simp [Site.pc]
  · simp [Site.pc]
  · fin_cases k <;> simp [Site.pc]
  · simp [Site.pc]
  · simp [Site.pc]

/-- **The event at a state of warpgroup 0's data machine**: at the site's pc, of the site's kind. -/
theorem w0_state_ev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {n : Nat} {e : Event} (he : X.get (g, n) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) {s : (threadD P L g).D}
    (hst : Frame.stateAt (threadD P L) X g n = some (some s)) {d : D}
    (hd : s.1 = .inr ⟨.inl .wg0, d⟩) :
    e.pc = d.c.site.pc ∧
    (((∃ a k, d.c.site = .sld a k) ∨ (∃ k, d.c.site = .rld k) ∨ ∃ k, d.c.site = .old k) →
      ∃ x vals, e.kind = .tc (.ld x vals .s32x32b)) ∧
    ((d.c.site = .vm ∨ (∃ k, d.c.site = .pld k) ∨ d.c.site = .mld ∨ d.c.site = .eld) →
      ∃ x bs, e.kind = .rd x bs) := by
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc := Frame.event_pcU hsD hX he hst hub
  obtain ⟨q, n'⟩ := s
  obtain rfl : q = .inr ⟨.inl .wg0, d⟩ := hd
  have hpd : e.pc = d.c.site.pc := hpc
  have key : 103 ≤ d.c.site.pc ∧ d.c.site.pc < 1842 → ∃ d0 : Control.D, d0 = d.c ∧
      EvK P L g (warpW L g) d0 e := fun hr' => by
    obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
    have hcd := control_of_data hst
    rw [hσ] at hcd
    have hσst := Option.some.inj (Option.some.inj hcd)
    obtain ⟨d0, n0, hσe, -, ⟨-, hE⟩, -⟩ := wg0_state hJ hi hev hpc' (by rw [hpd]; exact hr')
    rw [hσe] at hσst
    simp [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, wg0Erase] at hσst
    exact ⟨d0, hσst.1, hE⟩
  refine ⟨hpd, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨d0, rfl, hE⟩ := key (sel_range (Or.inl hs))
    exact kind_tc hE hub hs
  · obtain ⟨d0, rfl, hE⟩ := key (sel_range (Or.inr hs))
    exact kind_rd hE hub hs

end Wg0.Data

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

namespace Wg0.Data

/-- **The data step**: the state after the event at index `j` is the data step of the state before
it, for a control step `c'`. -/
theorem w0_data_step {j : Nat} {ev : Event} (hev : X.get (g, j) = some ev) {d : D}
    {s : (threadD P L g).D} (hst : Frame.stateAt (threadD P L) X g j = some (some s))
    (hd : s.1 = .inr ⟨.inl .wg0, d⟩)
    {s' : (threadD P L g).D} (hst' : Frame.stateAt (threadD P L) X g (j + 1) = some (some s'))
    {d' : D} (hd' : s'.1 = .inr ⟨.inl .wg0, d'⟩) :
    ∃ c', Control.succ P L g (warpW L g) d.c ev = some (some c') ∧ d' = dataNext L d c' ev := by
  obtain ⟨q, n⟩ := s
  obtain rfl : q = .inr ⟨.inl .wg0, d⟩ := hd
  rw [Frame.stateAt_succ hev, hst] at hst'
  obtain ⟨d'', hn', hs''⟩ := Code.roleThread_next_role hst'
  rw [hd'] at hs''
  simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hs''
  subst hs''
  change Wg0.Data.succ P L g (warpW L g) d ev = _ at hn'
  simp only [Wg0.Data.succ] at hn'
  cases hc : Control.succ P L g (warpW L g) d.c ev with
  | none => rw [hc] at hn'; cases hn'
  | some o =>
    rw [hc] at hn'
    cases o with
    | none => cases hn'
    | some c' =>
      simp only [Option.map_some] at hn'
      exact ⟨c', rfl, (Option.some.inj (Option.some.inj hn')).symm⟩

end Wg0.Data

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The empty trace is valid. -/
theorem w0Valid_empty (sc : ℝ) : W0Valid sc [] := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
    simp only [List.length_nil, nonpos_iff_eq_zero] at hj <;> subst hj <;>
    simp [W0Now, W0Early, W0EpiOk, w0Fin, w0Scan, w0SkWord, w0EpiPe, w0EpiO, w0SkRaw, w0Last,
      w0NegInf]

/-- An event below pc 103 is quiet. -/
theorem w0Quiet_of_lt {e : Event} (h : e.pc < 103) : W0Quiet e :=
  ⟨⟨⟨by unfold w0ArrSPc; omega, by unfold w0ArrLPc; omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, by omega, by omega, by omega, fun k hk hc => by omega⟩,
    ⟨by omega, by simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; omega⟩,
    ⟨by omega, by omega⟩⟩

namespace Wg0.Data

private theorem hasPw_smr : ∀ j ∈ List.range 8, hasPw j .smr = false := by decide

/-- A state at the `setmaxnreg` holds no loaded word yet. -/
theorem ldOk_smr {d : D} (hs : d.c.site = .smr) : LdOk d := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun j hj h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  all_goals first
    | (rw [hs, hasPw_smr j (List.mem_range.mpr hj)] at h; exact absurd h (by decide))
    | (simp [hasLo, hasHi, hasMw, hasPm, hasO, hasPe, accPcs, hs, Site.pc] at h)

/-- The state a startup state enters warpgroup 0 at is at the `setmaxnreg`. -/
theorem enter_smr {b : Startup.D} {d : D}
    (h : Code.enter (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) b = .inr ⟨.inl .wg0, d⟩) :
    d.c.site = .smr := by
  unfold Code.enter at h
  split at h
  · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases eq_of_heq h
    rfl
  · cases h

/-- The state a startup state enters warpgroup 0 at holds no loaded word yet. -/
theorem ldOk_enter {b : Startup.D} {d : D}
    (h : Code.enter (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) b = .inr ⟨.inl .wg0, d⟩) : LdOk d :=
  ldOk_smr (enter_smr h)

/-- **The words a state has loaded are the lane's**: `LdOk` and the words of the data machine are
the trace's (`InvW`, `InvE`). -/
theorem w0Loaded_of {l : List Event} {d : D} (hL : LdOk d) (hW : InvW l d) (hE : InvE l d) :
    W0Loaded l d.c.site.pc := by
  obtain ⟨hlo, hhi, hmw, hpw, hpm, hO, hpe⟩ := hL
  have e1 := hW.lo
  have e2 := hW.hi
  have e3 := hW.mw
  have e5 := hW.pm
  rw [← w0Fin_snd] at e1 e2 e3 e5
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun j hj h1 h2 => ?_, fun h1 h2 => ?_,
    fun h => ?_, fun h => ?_⟩
  · have hl := hlo (by simp only [hasLo]; simp; omega)
    have hh := hhi (by simp only [hasHi]; simp; omega)
    exact ⟨e1 ▸ hl, e2 ▸ hh⟩
  · exact e3 ▸ hmw (by simp only [hasMw]; simp; omega)
  · have := hW.pw j
    rw [← w0Fin_snd] at this
    exact this ▸ hpw j hj (by simp only [hasPw]; simp; omega)
  · exact e5 ▸ hpm (by simp only [hasPm]; simp; omega)
  · have := hE.o
    rw [← w0Fin_snd] at this
    exact this ▸ hO (by simpa [hasO, accPcs] using h)
  · have := hE.pe
    rw [← w0Fin_snd] at this
    refine this ▸ hpe ?_
    simp only [hasPe, Bool.and_eq_true, decide_eq_true_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega

private theorem site_tc_of_pc {s : Site}
    (h : s.pc = 278 ∨ s.pc = 280 ∨ s.pc = 283 ∨ s.pc = 285 ∨ s.pc ∈ w0OPcs) :
    (∃ a k, s = .sld a k) ∨ (∃ k, s = .rld k) ∨ ∃ k, s = .old k := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨false, 0, site_pc_inj (by rw [h]; rfl)⟩
  · exact Or.inl ⟨false, 1, site_pc_inj (by rw [h]; rfl)⟩
  · exact Or.inl ⟨true, 0, site_pc_inj (by rw [h]; rfl)⟩
  · exact Or.inl ⟨true, 1, site_pc_inj (by rw [h]; rfl)⟩
  · rcases site_pc_oPcs h with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inr (Or.inl ⟨k, hk⟩)
    · exact Or.inr (Or.inr ⟨k, hk⟩)

private theorem site_rd_of_pc {s : Site} (h : s.pc = 289 ∨ s.pc = 572 ∨ s.pc = 1157) :
    s = .vm ∨ (∃ k, s = .pld k) ∨ s = .mld ∨ s = .eld := by
  rcases h with h | h | h
  · exact Or.inl (site_pc_inj (by rw [h]; rfl))
  · exact Or.inr (Or.inr (Or.inl (site_pc_inj (by rw [h]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (site_pc_1157 h)))

end Wg0.Data

/-- **A live thread state is live before**: the thread machine of a followed lane never dies
silently, so a live state at `k` has live states at every earlier index. -/
theorem threadLive_le (hFw : Follow P L X) (hg : g < L.threads) {k i : Nat}
    (h : ThreadLive P L X g k) (hi : i ≤ k) : ThreadLive P L X g i := by
  obtain ⟨σ, hσ⟩ := h
  exact Frame.stateAt_live (fun g' k' hg' => (follow_iff.mp hFw g' hg' k').1) hg hσ hi

open Wg0 Wg0.Data in
/-- **A lane's prefixes are valid up to a live event**, and the data machine's states hold their
loaded words (`LdOk`). -/
theorem w0_upto (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hP : W0Payloads P L X) (hg : g < L.threads)
    {k : Nat} {ek : Event} (hek : X.get (g, k) = some ek)
    (hσ : ThreadLive P L X g k) :
    ∀ n ≤ k, W0Valid P.scale ((X.tr g).take n) ∧
      ∀ s, Frame.stateAt (threadD P L) X g n = some (some s) → ∀ d,
        s.1 = .inr ⟨.inl .wg0, d⟩ → LdOk d := by
  have hbef := noUbBefore_of_get hX hek
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hek).1
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hsc := hp.scalePos
  have hget : ∀ n, n ≤ k → ∃ e, X.get (g, n) = some e := fun n hn =>
    ⟨_, List.getElem?_eq_getElem (l := X.tr g) (i := n) (by omega)⟩
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨w0Valid_empty _, fun s hs d hd => ?_⟩
    obtain rfl := Option.some.inj (Option.some.inj (Frame.stateAt_zero.symm.trans hs))
    exact ldOk_enter (b := (startupCode P L g).init) hd
  | succ n ih =>
    intro hnk
    obtain ⟨hv, hLd⟩ := ih (by omega)
    obtain ⟨en, hen⟩ := hget n (by omega)
    have hub : ∀ f, en.kind ≠ .ub f := hbef.ne (by omega) hen
    have hTL : ∀ i, i ≤ k → ThreadLive P L X g i := fun i hi => threadLive_le hFw hg hσ hi
    obtain ⟨⟨q0, n0⟩, hst, hslot, hpre, hI, hPrev, hB⟩ :=
      followW_st hp hX hFw hw hen (hTL n (by omega)) (w0_scale_rd hp) hv n le_rfl
    have hv1 : W0Valid P.scale ((X.tr g).take (n + 1)) := by
      rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
      · obtain rfl : q0 = .inl b := hb
        obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX hen hst hub
        have h1 := startup_pc (d := b) (n := n0) hinv
        have h2 : en.pc = (thread P L g).pc (.inl b, n0) := Frame.event_pcU hsD hX hen hst hub
        rw [trace_take_succ hen]
        exact W0Valid.snoc_quiet hsc (w0Quiet_of_lt (by omega)) hv
      · obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
        obtain ⟨hpcd, kT, kR⟩ := w0_state_ev hp hX hFw hen hub hst rfl
        obtain ⟨hIW, -, -, -, hIE, -⟩ := hI d rfl
        have hb' : W0Bound ((X.tr g).take n) en.pc := fun a ha h103 => by
          rw [hpcd]; exact (hB d rfl).1 a ha h103
        have hld : W0Loaded ((X.tr g).take n) en.pc := by
          rw [hpcd]; exact w0Loaded_of (hLd _ hst d rfl) hIW hIE
        refine w0_valid_snoc hp hX hFw hw hP hg hen hub (hbef.mono (by omega)) hv hb' hld
          (fun h => ?_) (fun h => ?_)
        · obtain ⟨x, vals, hk⟩ := kT (site_tc_of_pc (by rw [← hpcd]; exact h))
          exact ⟨x, vals, _, hk⟩
        · exact kR (site_rd_of_pc (by rw [← hpcd]; exact h))
    refine ⟨hv1, fun s' hs' d' hd' => ?_⟩
    have hs'' : (threadD P L g).next (q0, n0) en = some (some s') := by
      rw [Frame.stateAt_succ hen, hst] at hs'
      exact hs'
    rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain rfl : q0 = .inl b := hb
      obtain ⟨b', -, hb'⟩ := Code.roleThread_next_start hs''
      exact ldOk_enter (hb'.symm.trans hd')
    · obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
      obtain ⟨c', hc', hde⟩ := w0_data_step hen hst rfl hs' hd'
      obtain ⟨hpcd, kT, kR⟩ := w0_state_ev hp hX hFw hen hub hst rfl
      obtain ⟨en1, hen1⟩ := hget (n + 1) hnk
      obtain ⟨s1, hs1, -, -, hI1, -⟩ :=
        followW_st hp hX hFw hw hen1 (hTL (n + 1) hnk) (w0_scale_rd hp) hv1 (n + 1) le_rfl
      obtain rfl := Option.some.inj (Option.some.inj (hs1.symm.trans hs'))
      obtain ⟨-, hOk', -⟩ := hI1 d' hd'
      subst hde
      exact ldOk_step (hLd _ hst d rfl) hc' hOk' hpcd kT kR (hP g n en hg hw hen)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
