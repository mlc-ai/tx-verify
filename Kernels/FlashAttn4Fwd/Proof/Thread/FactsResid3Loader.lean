-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Warp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderPollColl

@[expose] public section

/-! # The loader's part of `Cross.PollRest`

The loader polls at its six item polls, which are rendezvous positions (`Loader.wait_rdv`), and
in its drain (`drain k`, `drainQ`), which are not. A drain poll is made once per thread: the
drain only moves forward (`Loader.dRank_le`), and a successful poll at a drain site moves past it
(`Loader.dRank_lt`). So, by the run invariant `drainJ` (no successful poll yet at a drain site at
or after the current one), a loader lane's poll at a position that is not a rendezvous position
is in round 0 (`loader_round_zero`), and no lane of the warp polls there in an earlier round:
the premise of `PollRest` that asks for an order fails (`Cross.PollRest_loader`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader

/-- A site's place in the drain: `drain k` is `k + 1`, `drainQ` 7, the tail 8, the sites before
the drain 0. -/
def dRank : Site → Nat
  | .drain k => k.val + 1
  | .drainQ => 7
  | .elTail | .arriveTail | .exit => 8
  | _ => 0

/-- The item polls are rendezvous positions. -/
theorem wait_rdv (u : UseK) :
    rdvPos ((Site.wait u).pc + 1) = true := by
  cases u <;> decide +kernel

/-- **The drain only moves forward.** -/
theorem dRank_le {g : Nat} {d d' : D} {e : Event} (hn : next L g d e = some (some d')) :
    dRank d.site ≤ dRank d'.site := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site <;> simp only [dRank, Nat.zero_le]
  all_goals simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp
  all_goals omega

/-- **A successful poll at a drain site moves past it.** -/
theorem dRank_lt {g : Nat} {d d' : D} {e : Event} {m : Loc} {p : Nat} {acq : Bool}
    {sc : MbarScope} (hr : 0 < dRank d.site) (hk : e.kind = .wait m p true acq sc)
    (hn : next L g d e = some (some d')) : dRank d.site < dRank d'.site := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site <;> simp only [dRank, Nat.lt_irrefl] at hr
  all_goals simp only [next, hk, ↓reduceIte] at hn
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals (try split_ifs)
  all_goals simp [dRank]
  all_goals omega

end Loader

/-- No successful poll yet at a drain site at or after the loader's current site (and none at
any drain site in the prologue). -/
def drainJ : ThreadD → List Event → Prop
  | .inl _, es => ∀ s : Loader.Site, 0 < Loader.dRank s → pollRound s.pc es = 0
  | .inr (.loader d), es => ∀ s : Loader.Site, 0 < Loader.dRank s →
      Loader.dRank d.site ≤ Loader.dRank s → pollRound s.pc es = 0
  | .inr _, _ => True

theorem pollRound_snoc (pc : Nat) (es : List Event) (e : Event) :
    pollRound pc (es ++ [e]) = pollRound pc es + if okPollAt pc e then 1 else 0 := by
  simp [pollRound, List.countP_append]

theorem okPollAt_proKind {pc : Nat} {e : Event} (h : Prologue.ProKind e.kind) :
    okPollAt pc e = false := by
  obtain ⟨epc, k⟩ := e
  cases k <;> simp_all [Prologue.ProKind, okPollAt]

/-- **`drainJ` is a run invariant.** -/
theorem drainJ_run (hpre : Pre P L mem0) {g : Nat} : RunInv L g drainJ where
  init := fun _ _ => rfl
  step := by
    intro d d' pre e t u ins hJ hat hi hc hf hn
    rcases d with p | r
    · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
      have hat' : At t p.site.pc (Prologue.facts L g p) :=
        ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
      cases hx : Prologue.next L g p e with
      | none => rw [hx] at hn; cases hn
      | some x =>
        cases x with
        | none => rw [hx] at hn; cases hn
        | some x =>
          have hk := (Prologue.event_ok hpre hat' hc hf hx).proKind
          have H : ∀ s : Loader.Site, 0 < Loader.dRank s → pollRound s.pc (pre ++ [e]) = 0 := by
            intro s hs
            rw [pollRound_snoc, okPollAt_proKind hk, hJ s hs]
            rfl
          rcases d' with p' | r'
          · exact H
          · cases r' <;> first | trivial | exact fun s hs _ => H s hs
    · obtain ⟨r', rfl, hk⟩ := code_next_inr hn
      cases r with
      | loader d =>
        cases r' <;> simp only [Role.kind, reduceCtorEq] at hk
        rename_i d''
        have hn' := next_role (fun _ _ h => Role.loader.inj h) hn
        have hle := Loader.dRank_le hn'
        intro s hs hs'
        rw [pollRound_snoc, hJ s hs (by omega)]
        cases hok : okPollAt s.pc e
        · rfl
        · exfalso
          obtain ⟨epc, ek⟩ := e
          cases ek <;> simp only [okPollAt, Bool.false_eq_true] at hok
          rename_i m pp okb acq sc
          cases okb <;> simp only [Bool.false_eq_true, beq_iff_eq] at hok
          have hpc : epc = d.site.pc := Loader.fires_pc hf
          have hwp : d.site.pc ∈ Loader.waitPcs :=
            OpPcsFast.mem Loader.kernel_wait_pcs hc (Loader.waitOp_of hf rfl)
          have hds : d.site = s :=
            Loader.poll_site_inj _ _ hwp (by rw [← hok, hpc]; exact hwp) (by rw [← hpc, hok])
          have hlt := Loader.dRank_lt (hds ▸ hs) rfl hn'
          rw [hds] at hlt
          omega
      | _ => cases r' <;> trivial

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A loader poll at a position that is not a rendezvous position is in round 0.** -/
theorem loader_round_zero {g k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : warpOf L g = 14) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (hu : rdvPos (pc + 1) = false) :
    pollRound pc ((X.tr g).take k) = 0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  have hpc : pc = d.site.pc := Loader.fires_pc hf
  have hwp := OpPcsFast.mem Loader.kernel_wait_pcs hc (Loader.waitOp_of hf rfl)
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hJ := RunInv.holds hpre hX hg (drainJ_run hpre) hk hσ
  have hr : 0 < Loader.dRank d.site := by
    rcases Loader.site_wait d.site hwp with ⟨u, hs⟩ | ⟨kk, hs⟩ | hs
    · rw [hpc, hs, Loader.wait_rdv] at hu
      cases hu
    · rw [hs]
      simp [Loader.dRank]
    · rw [hs]
      simp [Loader.dRank]
  rw [hpc]
  exact hJ d.site hr le_rfl

/-- **`Cross.PollRest`, loader part**: two lanes of the loader warp polling at one position that
is not a rendezvous position are both in round 0, so the premise that asks for an order fails. -/
theorem Cross.PollRest_loader {g h k k' pc p' : Nat} {m' : Loc} {ok' acq' : Bool}
    {sc' : MbarScope} (hw : warpOf L g = 14) (hs : SameWarp L g h)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hu : rdvPos (pc + 1) = false) :
    ¬ pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') := by
  rw [loader_round_zero hpre hX ht (SameWarp.warp_eq hs ▸ hw) he' hu]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
