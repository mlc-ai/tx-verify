-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
public import Lemmas.Flow.PollSynced
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.LdWarp.Pos
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.EvPc
import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
import Kernels.TmlFa4Fwd.Proof.Lib.ElectOrd
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
import Lemmas.Flow.PollMeet
import Lemmas.Flow.PollRounds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Two lanes of a loader warp polling at one position

They poll one barrier, or they are ordered by their shuffles: a ring slot's poll of a later packet
follows at least 32 shuffles more (`LFits`: 32 per committed packet, beside the scans'). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The loader's poll sites. -/
private def ldPolls : List Loader.Site :=
  (Loader.pers.flatMap fun per => [.slot per false, .slot per true]) ++
    (List.finRange 7).map .tw ++ (List.finRange 3).map .dw ++ [.dq]

private theorem ld_pc : ∀ s ∈ ldPolls, ∀ s' ∈ ldPolls, s.pc = s'.pc → s = s' := by decide

/-- A loader lane's poll: its state, site and use. -/
private theorem ld_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {k pc par : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩) :
    ∃ b d n, Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)) ∧
      n .ub = 0 ∧ Loader.Ref p L g (Prologue.warpIndex L g) (d, LdWarp.lcn n) ∧
      Loader.LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) ∧
      d.site ∈ ldPolls ∧ pc = d.site.pc ∧ ((∃ per v, d.site = .slot per v ∧
        l = obj L g (56 + 8 * (n (.load .commit) % 3))) ∨
        (∃ j, d.site = .dw j ∧ l = obj L g (56 + 8 * ((n (.load .commit) + j.val) % 3))) ∨
        ((∀ per v, d.site ≠ .slot per v) ∧ (∀ j, d.site ≠ .dw j) ∧
          l = obj L g ((match d.site with | .tw t => Loader.twOff t | _ => 24)))) := by
  rcases LdWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    obtain ⟨c, hc⟩ := start_mbar (l := l) hev hi.2 rfl
    cases hc
  · obtain ⟨hb, hR⟩ := hR
    obtain ⟨hJ, hF⟩ := hR h0
    have hpc := ev_pc hp hX he hσ
    have hJ' := hJ
    rw [← hb] at hJ'
    have hcm := hJ.commit
    refine ⟨b, d, n, hσ, h0, hJ, hF, ?_⟩
    cases ld_use (l := l) hp hJ'.toRefRing hev rfl with
    | slot per v ok' hs hl hk =>
      refine ⟨by rw [hs]; cases per <;> cases v <;> decide, hpc, .inl ⟨per, v, hs, ?_⟩⟩
      rw [hl, show n (.load .commit) = Loader.pkOf per v (Loader.posK (d, LdWarp.lcn n)) from
        hcm.trans (by rw [show (d, LdWarp.lcn n).1.site = _ from hs]; rfl)]
    | tw t ok' hs hl hk =>
      refine ⟨by rw [hs]; simp [ldPolls], hpc, .inr (.inr ⟨?_, ?_, ?_⟩)⟩
      · intro per v h; rw [hs] at h; cases h
      · intro j h; rw [hs] at h; cases h
      · rw [hl, hs]
    | dw j ok' hs hl hk =>
      refine ⟨by rw [hs]; simp [ldPolls], hpc, .inr (.inl ⟨j, hs, ?_⟩)⟩
      exact hl
    | dq ok' hs hl hk =>
      refine ⟨by rw [hs]; decide, hpc, .inr (.inr ⟨?_, ?_, ?_⟩)⟩
      · intro per v h; rw [hs] at h; cases h
      · intro j h; rw [hs] at h; cases h
      · rw [hl, hs]
    | arrive _ _ _ _ hk | ta _ _ _ _ hk | da _ _ _ hk => cases hk
    | tc _ _ _ _ _ _ hk => cases hk

/-- The shuffles at a slot's poll: 32 per committed packet, beside those of the first pass. -/
private theorem slot_shfl {d : Loader.D} {ns nv nc : Nat} {per : Loader.Per} {v : Bool}
    (hF : Loader.LFits p L g d ns nv nc) (hs : d.site = .slot per v) :
    ∃ R bal, Epilogue.Picked p L g R bal ∧
      ns = 32 * nc + (3 + 7 * (R + 1) + Epilogue.selN bal) := by
  obtain ⟨s, vv, kk⟩ := d
  simp only at hs
  subst hs
  simp only [Loader.LFits, Loader.lc, Loader.pktSh, Nat.add_zero, Nat.sub_zero] at hF
  obtain ⟨h1, hE, -⟩ := hF
  simp only [Epilogue.Fits, Loader.toE, Loader.Site.epi] at hE
  obtain ⟨R, bal, ⟨hP, -, -, -, -, -, -, hns, -⟩, -⟩ := hE
  exact ⟨R, bal, hP, by omega⟩

/-- A lane polling a ring slot exits after more shuffles. -/
private theorem slot_no_exit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat}
    {b : Bool} {d : Loader.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    {R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L g R bal)
    (hn : n .shfl = 32 * n (.load .commit) + (3 + 7 * (R + 1) + Epilogue.selN bal)) :
    k < (X.tr g).length → ¬ ShflExited X g (n .shfl) := by
  rintro hk ⟨j, pc, hx, hle⟩
  obtain ⟨⟨σ, n'⟩, hσ', hR⟩ := good_state hp hX hx (by intro _ _ h; cases h)
    (LdWarp.good hp hX hw hg rfl j)
  have hkj : k ≤ j := by
    have hlen := Execution.exit_last hX hg hx
    omega
  have hcc := countP_take_mono (cls L g (.load .commit)) (X.tr g) hkj
  rw [count hσ, count hσ'] at hcc
  have hs' := count hσ' .shfl
  simp only [cls] at hs'
  rw [hs'] at hle
  rcases σ with s | ⟨i, d'⟩
  · obtain ⟨hev, hx', -⟩ := start_fired hp hX hx hσ'
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx'
  cases i with
  | loader b' =>
    obtain ⟨hJ, hF⟩ := hR.2 (ub_zero hX hx hσ')
    have hev := (LdWarp.lfired hp hX hx hσ').1
    have hsite : d'.site = .exit := by
      obtain ⟨site, v, kk⟩ := d'
      cases site
      case exit => rfl
      all_goals exfalso
      all_goals simp only [Loader.Ev, Epilogue.Ev, Loader.Site.toE] at hev
      all_goals simp at hev
    simp only [Loader.LFits, hsite, Loader.lc] at hF
    obtain ⟨l, h32, hE, ht, hf⟩ := hF
    cases l
    · exact Loader.noPick hE hP
    · simp only [Epilogue.Fits, Epilogue.Fits.ExitAt, Epilogue.PassStart, ↓reduceIte] at hE
      obtain ⟨n0, v0, ⟨R1, bal1, hP1, hn0, -⟩, R2, -, h⟩ := hE
      obtain ⟨rfl, rfl⟩ := hP1.unique hP
      have : n0 + 7 ≤ n' .shfl - 32 * n' (.load .commit) := by
        rcases h with ⟨-, h, -⟩ | ⟨_, -, -, h, -⟩ <;> omega
      omega
  | _ => exact hR.elim

/-- **Two lanes of a loader warp polling at one position poll one barrier, or are ordered.** -/
theorem ld_poll_same (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    (hs : SameWarp L g h)
    {k k' pc par par' : Nat} {l l' : Loc} {ok acq ok' acq' : Bool} {sc sc' : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait l' par' ok' acq' sc'⟩) :
    l = l' ∨ PollBefore L kernel X (g, k) (h, k') ∨ PollBefore L kernel X (h, k') (g, k) := by
  have hwe : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  have hobj : ∀ o, obj L g o = obj L h o := fun o => by simp only [obj, hs.1.2.2]
  obtain ⟨b, d, n, hσ, h0, hJ, hF, hm, hpc, hl⟩ := ld_poll hp hX hFw hw he
  obtain ⟨b', d', n', hσ', h0', hJ', hF', hm', hpc', hl'⟩ := ld_poll hp hX hFw (hwe ▸ hw) he'
  have hsite := ld_pc _ hm _ hm' (hpc.symm.trans hpc')
  have hl1 := (List.getElem?_eq_some_iff.mp he).1
  have hl2 := (List.getElem?_eq_some_iff.mp he').1
  rcases hl with ⟨per, v, hsl, hl⟩ | ⟨j, hsl, hl⟩ | ⟨hn1, hn2, hl⟩
  · rcases hl' with ⟨per', v', hsl', hl'⟩ | ⟨j', hsl', -⟩ | ⟨hn1', -⟩
    rotate_left
    · rw [← hsite, hsl] at hsl'; cases hsl'
    · exact absurd (hsite ▸ hsl) (hn1' per v)
    obtain ⟨R, bal, hP, hns⟩ := slot_shfl hF hsl
    obtain ⟨R', bal', hP', hns'⟩ := slot_shfl hF' hsl'
    obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hs.1.2.2.symm hP').unique hP
    have hc1 := count hσ .shfl
    have hc2 := count hσ' .shfl
    simp only [cls] at hc1 hc2
    rcases Nat.lt_trichotomy (n (.load .commit)) (n' (.load .commit)) with hlt | heq | hlt
    · refine .inr (.inl (meet_shfl hX (elect_ord hX) hs he rfl hc1 (by rw [hc2]; omega) hl2
        (slot_no_exit hp hX (Frame.lt_of_get hX he) hw hσ hP hns hl1)))
    · left; rw [hl, hl', heq, hobj]
    · refine .inr (.inr (meet_shfl hX (elect_ord hX) (SameWarp.symm hs) he' rfl hc2
        (by rw [hc1]; omega) hl1
        (slot_no_exit hp hX (Frame.lt_of_get hX he') (hwe ▸ hw) hσ' hP' hns' hl2)))
  · rcases hl' with ⟨per', v', hsl', -⟩ | ⟨j', hsl', hl'⟩ | ⟨-, hn2', -⟩
    · rw [← hsite, hsl] at hsl'; cases hsl'
    rotate_left
    · exact absurd (hsite ▸ hsl) (hn2' j)
    left
    have hj : j = j' := by rw [← hsite, hsl] at hsl'; injection hsl'
    subst hj
    simp only [Loader.LFits, hsl, hsl', Loader.lc] at hF hF'
    obtain ⟨l1, -, hE1, ht1, hf1⟩ := hF
    obtain ⟨l2, -, hE2, ht2, hf2⟩ := hF'
    have hcm : n (.load .commit) = n' (.load .commit) := by
      cases l1 <;> cases l2
      · rw [hf1 rfl, hf2 rfl]
      · exfalso
        obtain ⟨⟨R, bal, hP, -⟩, -⟩ := ht2 rfl
        exact Loader.noPick hE1 (Epilogue.Picked.cta hs.1.2.2.symm hP)
      · exfalso
        obtain ⟨⟨R, bal, hP, -⟩, -⟩ := ht1 rfl
        exact Loader.noPick hE2 (Epilogue.Picked.cta hs.1.2.2 hP)
      · obtain ⟨⟨R, bal, hP, hr⟩, hA⟩ := ht1 rfl
        obtain ⟨⟨R', bal', hP', hr'⟩, hA'⟩ := ht2 rfl
        obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hs.1.2.2.symm hP').unique hP
        rw [hA, hA', hr, hr', Loader.r28Ref_cta hs.1.2.2]
    rw [hl, hl', hcm, hobj]
  · rcases hl' with ⟨per', v', hsl', -⟩ | ⟨j', hsl', hl'⟩ | ⟨-, -, hl'⟩
    · exact absurd (hsite ▸ hsl') (hn1 per' v')
    · exact absurd (hsite ▸ hsl') (hn2 j')
    · left; rw [hl, hl', hsite, hobj]

end
end PTX.Kernels.TmlFa4Fwd.Proof
