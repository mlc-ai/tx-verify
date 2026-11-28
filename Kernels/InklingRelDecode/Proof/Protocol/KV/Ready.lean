-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Loader.Export.Election
import Kernels.InklingRelDecode.Proof.Protocol.KV.Obj
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll

import Kernels.InklingRelDecode.Proof.Protocol.KV.LoaderBudget
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.MbarRow MbarRow

private theorem arr_sites {Q L X g k pc tx n rel sc c s} (rows : MbarRows Q L X)
    (hg : g < L.threads) (he : X.get (g,k) = some ⟨pc,.arrive (Ring.ready.obj L c s) tx n rel sc⟩) :
    tx = 65536 ∧ n = 1 ∧ (pc = 2378 ∨ pc ∈ [193,237,279]) := by
  have hu := ring_use rows hg he (r := .ready) (s := s) rfl
  generalize h : Event.mk pc (.arrive (Ring.ready.obj L c s) tx n rel sc) = ev at hu
  cases hu with
  | init _ hk => cases h; cases hk
  | preload hp hk | arrive hp _ hk =>
    cases h
    obtain ⟨_,rfl,rfl,_,_⟩ := Kind.arrive.inj hk
    exact ⟨rfl,rfl,by first | exact .inl hp | exact .inr hp⟩
  | preloadCopy _ hx | copy _ _ hx => cases h; obtain ⟨_,_,hk,_⟩ := hx; cases hk
  | readyWait _ _ hx => cases h; obtain ⟨_,hk⟩ := hx; cases hk

private theorem issue_sites {Q L X g k pc a sp c s} (rows : MbarRows Q L X)
    (hg : g < L.threads) (he : X.get (g,k) = some ⟨pc,.tensorIssue a sp⟩)
    (hm : sp.mbar = Ring.ready.obj L c s) :
    TensorTransfer.bytes sp.descriptor = 8192 ∧ ((g % L.block / 32 = 6 ∧
      pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) ∨ 27 ≤ pc ∧ pc < 574) := by
  have hu := ring_use rows hg he hm
  cases hu with
  | init _ hk | preload _ hk | arrive _ _ hk => cases hk
  | readyWait _ _ hx => obtain ⟨_,hk⟩ := hx; cases hk
  | preloadCopy hp hx =>
    obtain ⟨_,_,hk,_,hbytes⟩ := hx
    obtain ⟨_,rfl⟩ := Kind.tensorIssue.inj hk
    have bounds : ∀ j : Fin 3, ∀ p ∈ preloadCopies j, 27 ≤ p ∧ p < 574 := by decide
    exact ⟨hbytes,.inr (bounds _ _ hp)⟩
  | copy hpc hw hx =>
    obtain ⟨_,_,hk,_,hbytes⟩ := hx
    obtain ⟨_,rfl⟩ := Kind.tensorIssue.inj hk
    exact ⟨hbytes,.inl ⟨hw,hpc⟩⟩

theorem ring_events {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (hi : Mbar.InitRows L X)
    (hc : c < L.grid) :
    (decl Q L X c).Events L kernel Assumptions.all X .cta := by
  obtain ⟨ht6,hc6,hw6⟩ := leader_warp (X := X) hp hc (by decide : 6 < 8)
  obtain ⟨ht7,hc7,hw7⟩ := leader_warp (X := X) hp hc (by decide : 7 < 8)
  refine { δ_le := fun s => ?_, arrive := ?_, arrive_empty := ?_, issue := ?_, issue_empty := ?_,
           commit := ?_, commit_full := ?_, no_bulk := Lib.no_copy hX,
           no_arriveOn := Lib.no_asyncArrive hX, no_clc := Lib.no_clc hX,
           no_inval := Lib.no_inval hX,
           full_init := fun s => Mbar.initFirst hX rows hi _,
           empty_init := fun s => Mbar.initFirst hX rows hi _,
           full_parity := fun _ {_ _ _ _ _ _} he =>
             wait_parity (r := .ready) rows (Frame.lt_of_get hX he) he,
           empty_parity := fun _ {_ _ _ _ _ _} he =>
             wait_parity (r := .empty) rows (Frame.lt_of_get hX he) he,
           spins := fun _ _ _ _ _ _ he => (Lib.poll_site hX he).2, full_acq := ?_, empty_acq := ?_,
           cta := ?_, pre_cta := ?_, pre_ne := ?_, pre_inj := fun s _ => precopy_inj hp hc s }
  · change preload Q L c s ≤ 1
    unfold preload
    split <;> decide
  · intro s g k pc tx n rel sc he
    obtain ⟨rfl,rfl,hp'⟩ := arr_sites rows (Frame.lt_of_get hX he) he
    refine ⟨by change 65536 = 8 * 8192; decide,rfl,?_⟩
    rcases hp' with rfl | hpc
    · exact .inl (arrival_budget hp hX hf rows
        (fun h => Protocol.Shared.role_bytes hp hX h) he)
    · have bounds : ∀ p ∈ [193,237,279], 27 ≤ p ∧ p < 574 := by decide
      obtain ⟨lo,hi'⟩ := bounds pc hpc
      obtain ⟨hcta,ht,hs,_,_,_,hz⟩ := rows.prologue.1.arrive lo hi' he
      have hg := Nat.div_add_mod g L.block
      rw [hcta,ht,Nat.add_zero,Nat.mul_comm] at hg
      refine .inr ⟨by change preload Q L c s = 1; simp [preload,hs],?_⟩
      subst g
      change X.get (_,k) = some ⟨pc,.arrive (Ring.ready.obj L c s) 65536 1 rel sc⟩ at he
      have hpos := position_at (f := arrivesOn (Ring.ready.obj L c s)) he
        (by simp [arrivesOn,sourceArrive])
      change ((X.tr _).take k).countP (arrivesOn (Ring.ready.obj L c s)) = 0 at hz
      rw [hz] at hpos
      exact Prod.ext rfl hpos.symm
  · intro s g k pc tx n rel sc he
    rcases empty_use rows (Frame.lt_of_get hX he) he rfl with hk | ⟨_,_,hk⟩ | ⟨_,_,_,hk,_⟩
    all_goals cases hk
  · intro s g k pc a sp he hm
    have hg := Frame.lt_of_get hX he
    have hcta := use_cta rows hg he hm
    obtain ⟨hb,hp'⟩ := issue_sites rows hg he hm
    refine ⟨hb,?_⟩
    rcases hp' with ⟨hw,hpc⟩ | ⟨lo,hi'⟩
    · have hbud := issue_budget hp hX hf rows
        (fun h => Protocol.Shared.role_bytes hp hX h) hw he hm
      obtain ⟨ev,hev,hwin⟩ := Loader.Export.elected hp hX hf he (fun _ => nofun) hpc
      have hlead := leader_eq hX hg ⟨ev,(List.take_sublist k _).subset hev,hwin⟩
      rw [hw,hcta] at hlead
      exact .inl ⟨hlead.symm,hm ▸ hbud⟩
    · obtain ⟨_,hs,hw,hel,_,hcnt⟩ := rows.prologue.1.copy lo hi' he hm
      change sp.mbar = Ring.ready.obj L c s at hm
      let idx := ((X.tr g).take k).countP (issuesTo (Ring.ready.obj L c s))
      let w := g % L.block / 32
      have hidx : idx < 4 := hcnt
      have hw' : w < 2 := hw
      let i : Fin 8 := ⟨4*w+idx,by omega⟩
      have hdiv : i.val / 4 = w := by dsimp [i]; omega
      have hmod : i.val % 4 = idx := by dsimp [i]; omega
      have hel' : Elected (X.tr g) (laneOf L g) := by
        obtain ⟨ev,hev,rest⟩ := hel
        exact ⟨ev,(List.take_sublist k _).subset hev,rest⟩
      have hl : leader L X c w = g := hcta ▸ leader_eq hX hg hel'
      refine .inr ⟨by change preload Q L c s = 1; simp [preload,hs],i,?_⟩
      change (g,k) = preCopy L X c s i
      simp only [preCopy,hdiv,hmod,hl,Prod.mk.injEq,true_and]
      exact (position_at he (by simp [issuesTo,hm] : issuesTo (Ring.ready.obj L c s) _ = true)).symm
  · intro s g k pc a sp he hm
    rcases empty_use rows (Frame.lt_of_get hX he) he hm with hk | ⟨_,_,hk⟩ | ⟨_,_,_,hk,_⟩
    all_goals cases hk
  · intro s g k pc sp rank he ht
    have hg := Frame.lt_of_get hX he
    rcases empty_use rows hg he ⟨rank,ht⟩ with hk | ⟨_,_,hk⟩ | ⟨hpc,hw,_⟩
    · cases hk
    · cases hk
    · obtain ⟨rfl,hcta,hr,hm,_⟩ := empty_commit hp hX hf hw he ht
      have hl := leader_eq hX hg (wonCommit hp hX hf he)
      rw [hcta,hw] at hl
      exact ⟨hl.symm,hr,hm,commit_budget hp hX hf rows
        (fun h => Protocol.Shared.role_bytes hp hX h) he hm⟩
  · intro s g k pc sp rank he ht
    cases ring_use rows (Frame.lt_of_get hX he) he (r := .ready) (s := s) ⟨rank,ht⟩ with
    | init _ hk | preload _ hk | arrive _ _ hk => cases hk
    | preloadCopy _ h | copy _ _ h => obtain ⟨_,_,hk,_⟩ := h; cases hk
    | readyWait _ _ h => obtain ⟨_,hk⟩ := h; cases hk
  · intro s g k pc q ac sc he
    obtain ⟨_,ha,hs,_⟩ := wait_info (r := .ready) rows (Frame.lt_of_get hX he) he
    exact ⟨ha,hs⟩
  · intro s g k pc q ac sc he
    obtain ⟨_,ha,hs,_⟩ := wait_info (r := .empty) rows (Frame.lt_of_get hX he) he
    exact ⟨ha,hs⟩
  · intro a
    change SameCta L (if a = 0 then c*L.block+192 else leader L X c 6) (leader L X c 7)
    split
    · refine ⟨?_,ht7,?_⟩ <;> simp only [Launch.threads,hp.block] at * <;> omega
    · exact ⟨ht6,ht7,hc6.trans hc7.symm⟩
  · intro s _ i
    have : i.val < 8 := i.isLt
    obtain ⟨ht,hc',_⟩ := leader_warp (X := X) hp hc (by omega : i.val / 4 < 8)
    exact ⟨ht,ht7,hc'.trans hc7.symm⟩
  · intro s _
    refine ⟨by change c*L.block ≠ c*L.block + 192; omega,?_⟩
    intro i h
    have : i.val < 8 := i.isLt
    obtain ⟨_,_,hw⟩ := leader_warp (X := X) hp hc (by omega : i.val / 4 < 8)
    change leader L X c (i.val/4) = leader L X c 6 at h
    rw [h,hw6] at hw
    omega

theorem ready_slot {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (hi : Mbar.InitRows L X)
    (hc : c < L.grid) (s : Fin 3) :
    SingleTmaRing.Hyp L kernel Assumptions.all X ((decl Q L X c).slot s) .cta :=
  SingleTmaRing.Decl.hyp hX (ring_events hp hX hf rows hi hc) s

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
