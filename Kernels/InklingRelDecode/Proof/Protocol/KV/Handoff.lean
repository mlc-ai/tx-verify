-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.KV.PollCount
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
public import Lemmas.Protocol.UnitNotify
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.Elect

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.MbarRow MbarRow

open Classical in
/-- The warp's elected issuer, defaulting to lane zero before an election. -/
noncomputable def leader (L : Launch) (X : Execution) (c w : Nat) : Nat :=
  if h : ∃ g, g < L.threads ∧ g / L.block = c ∧ g % L.block / 32 = w ∧
      Elected (X.tr g) (laneOf L g) then h.choose else c * L.block + 32*w

theorem leader_eq {L m X g} (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (won : Elected (X.tr g) (laneOf L g)) :
    leader L X (g / L.block) (g % L.block / 32) = g := by
  unfold leader
  split
  · rename_i h
    obtain ⟨hh,hc,hw,hel⟩ := h.choose_spec
    exact electLead_unique hX.elect ⟨⟨hh,hg,hc⟩,hw⟩ (Lib.electMask_full hX _)
      (Lib.electMask_full hX _) hel won (Lib.electLead_of_elected hX hel)
      (Lib.electLead_of_elected hX won)
  · rename_i hn
    exact False.elim (hn ⟨g,hg,rfl,rfl,won⟩)

/-- W, MMA election row: executing the guarded empty commit requires a winning election. -/
def WonCommit (L : Launch) (X : Execution) : Prop :=
  ∀ {g k sp}, X.get (g,k) = some ⟨2546,.tc (.commit sp)⟩ → Elected (X.tr g) (laneOf L g)

theorem wonCommit {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : WonCommit L X := by
  intro g k sp he
  obtain ⟨e,hm,hw⟩ := Mma.Export.elected hp hX hf he (fun _ => nofun)
    (by change 2546 ∈ _; decide)
  exact ⟨e,(List.take_sublist k _).subset hm,hw⟩

theorem empty_use {Q L X c g k e s} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some e) (hm : Frame.MbarOf e (Ring.empty.obj L c s)) :
    e.kind = .mbInit (Ring.empty.obj L c s) 1 ∨
    (∃ q, Wait e (Ring.empty.obj L c s) q) ∨
    (e.pc = 2546 ∧ g % L.block / 32 = 7 ∧ Commit e (Ring.empty.obj L c s)) := by
  cases ring_use rows hg he hm with
  | init _ hk => exact .inl hk
  | emptyWait _ _ hk => exact .inr (.inl ⟨_,hk⟩)
  | notify pc hw hk => exact .inr (.inr ⟨pc,hw,hk⟩)

theorem empty_obj {Q L X m} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (hi : Mbar.InitRows L X) (c : Nat) (s : Fin 3) :
    MbarRing.Notify.Obj X (Ring.empty.obj L c s) (leader L X c 7) (Ring.empty.obj L c s)
      (1 - preload Q L c s) := by
  refine MbarRing.Notify.Obj.of_commits hX (Mbar.initFirst hX rows hi _) ?_ ?_
    (fun he _ => Lib.no_copy hX he) (fun he _ => Lib.no_asyncArrive hX he)
    (Lib.no_clc hX) (Lib.no_inval hX) ?_ ?_ (by omega)
  · intro g k pc tx cnt rel sc he
    rcases empty_use rows (Frame.lt_of_get hX he) he rfl with bad | ⟨_,_,bad⟩ | ⟨_,_,_,bad,_⟩
    all_goals cases bad
  · rintro ⟨g,k⟩ pc a sp he hm
    rcases empty_use rows (Frame.lt_of_get hX he) he hm with bad | ⟨_,_,bad⟩ | ⟨_,_,_,bad,_⟩
    all_goals cases bad
  · rintro ⟨g,k⟩ pc sp rank he ht
    have hg := Frame.lt_of_get hX he
    have hmo : Frame.MbarOf ⟨pc,.tc (.commit sp)⟩ (Ring.empty.obj L c s) := ⟨rank,ht⟩
    rcases empty_use rows hg he hmo with bad | ⟨_,_,bad⟩ | ⟨hp,hw,sp',hk,hl,_⟩
    · cases bad
    · cases bad
    · obtain rfl : pc = 2546 := hp
      obtain rfl := TcKind.commit.inj (Kind.tc.inj hk)
      have hc := use_cta rows hg he hmo
      have hlane := leader_eq hX hg (wonCommit hp hX hf he)
      rw [hc,hw] at hlane
      exact ⟨hlane.symm,hl⟩
  · intro g k pc p ac sc he
    exact wait_parity rows (Frame.lt_of_get hX he) he

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
