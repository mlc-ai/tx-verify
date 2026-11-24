-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FrBias
public import Kernels.InklingRelDecode.Proof.Interface.FrShfl
public import Kernels.InklingRelDecode.Proof.Interface.FrNnSt
public import Kernels.InklingRelDecode.Proof.Interface.Lk3Upd
public import Kernels.InklingRelDecode.Proof.Protocol.FrLdL
public import Kernels.InklingRelDecode.Proof.Interface.PlFault
public import Kernels.InklingRelDecode.Proof.Interface.FrEpi
public import Kernels.InklingRelDecode.Proof.Interface.EpBcast

@[expose] public section

/-!
# The softmax region's machine does not fault at a followed event

`Sm.next` is `none` in seven kinds of place: the event is not of the kind the site matches on
(the site's shape, which every continuing event has), the bytes a load returned do not rebuild
(the bias loads `FrBias`, the scratch load `FrLdL`), a word of the S load is not four bytes
(`ldS`: `SmSLoadOk`, a fact of the words the S load reads, `Qy.smSLoad_of`), an instruction of the
score stage's first half faults (`waitLd`: `SmScoreOk`, a fact of the same words, `Qy.smScore_of`),
a minimum or
comparison of the lazy-rescale test has no outcome (`FrShfl`), a product of the O rescale faults
(`waitLdO`: `SmOLoadOk`, a fact of the words the rescale load reads, `Qy.smOLoad_of`), the row
sum's `add` at `shfl6` faults (it does not: the received word is the partner's sum of
probabilities, `shfl6_recv`), and the edge into the `P` store (`Sm.toBar20`) faults where the
words of the stage are not `.f32` data (they always are: `Sm.NumInv`). Each has a proof below, so
`Sm.next` is never `none` at an event of a launched thread, and `DComp.smNext` is `none` only at
the loop's exit where the bridge faults (`Sm.NnInv`, `exit_noFault`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

theorem afterSetup_ne_none (L : Launch) (g : Nat) (d : Sm.D) : Sm.afterSetup L g d ≠ none := by
  unfold Sm.afterSetup
  split_ifs <;> simp

theorem toBar20_ne_none {d : Sm.D} (h : NumInv d) : Sm.toBar20 d ≠ none := by
  simp [Sm.toBar20, updOk_of h]

/-- **The rescale load's check**: at a followed `waitLdO` the 64 products of the O rescale have
outcomes (`Sm.D.owOk`). It is a fact about the values of the words the rescale load reads (their
read sources, `Qy.smOLoad_of`), which nothing in the thread layer gives. -/
def SmOLoadOk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → k ≤ (X.tr g).length →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .waitLdO → d.owOk

/-- **The S load's check**: at a followed `ldS` every word the load returned has four bytes. It is
a fact about the values of the words the S load reads (their read sources, `Qy.smSLoad_of`), which
nothing in the thread layer gives. -/
def SmSLoadOk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}, g < L.threads →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ → ∀ x ∈ vals, x.bytes = 4

/-- **The score stage's check**: at a followed `waitLd` no instruction of the score stage's first
half faults (`Sm.D.s1Ok`). It is a fact about the values of the words the S load reads (`f32`
numbers, `Qy.smScore_of`), which nothing in the thread layer gives. -/
def SmScoreOk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → k ≤ (X.tr g).length →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .waitLd → Sm.D.s1Ok L g d

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hR : RoleReads L X) (hz : Rs.SmBaseZero Q L X) (hI : ∀ i, ScratchIt Q L X i)
    (hso : SmOLoadOk Q L X) (hss : SmSLoadOk Q L X) (hsc : SmScoreOk Q L X)
include hpre hX hf hR hz hI hso hss hsc

/-- **`Sm.next` is never `none` at an event of a launched thread.** -/
theorem sm_next_ne_none (hM : SmMaxOk Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    Sm.next L g d e ≠ none := by
  have hre : SmReal Q L X := smReal_of_max hX hM
  have hIv : Sm.Inv L g d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  have hF' := fired_sm hF
  have hS := ProA.sharedOk_of_pre hpre
  have hNum := numInv_state hσ
  cases hs : d.site with
  | setMaxReg => simp [Sm.next, hs]
  | bar0 =>
    simp only [Sm.next, hs]
    split <;> first | exact afterSetup_ne_none _ _ _ | simp
  | pre j =>
    obtain ⟨ac, bs, x, hk, hx⟩ := Sv.rebuild_pre hpre hX hf hg he hσ hIv hs
    simp only [Sm.next, hs, hk, hx]
    split_ifs <;> first | exact afterSetup_ne_none _ _ _ | simp
  | nxt j =>
    obtain ⟨ac, bs, x, hk, hx⟩ := Sv.rebuild_nxt hpre hX hf hg he hσ hIv hs
    simp only [Sm.next, hs, hk, hx]
    split_ifs <;> first | exact afterSetup_ne_none _ _ _ | simp
  | waitS =>
    obtain ⟨ok, rfl⟩ := Sm.shape_waitS hF' hs
    simp [Sm.next, hs]
  | shfl4 =>
    obtain ⟨recv, ok, rfl⟩ := Sm.shape_shfl4 hF' hs
    have hr := sm_recv hpre hX hf hg he hσ hs
    have hT : g % L.block < 128 := hIv.tid
    simp only [Sm.next, hs, hr, Raw.laneOk_b32 (show g % L.block / 32 < 4 by omega)]
    simp
  | ldS =>
    obtain ⟨vals, hlen, rfl⟩ := Sm.shape_ldS hF' hs
    have hb := hss hg hσ hs he
    simp only [Sm.next, hs]
    rw [dite_eq_left ⟨hlen, hb⟩]
    simp
  | waitLd =>
    have hok := hsc hg (len_of_get he).le hσ hs
    simp [Sm.next, hs, hok]
  | shfl5 =>
    obtain ⟨recv, ok, rfl⟩ := Sm.shape_shfl5 hF' hs
    have hRI := hM hg he hσ hs _ _ _ _ _ _ rfl
    simp [Sm.next, hs, hRI]
  | shfl6 =>
    obtain ⟨recv, ok, rfl⟩ := Sm.shape_shfl6 hF' hs
    obtain ⟨y, rfl, -⟩ := shfl6_recv hpre hX hf hre hg he hσ hs rfl
    have hv : d.rsOut (.float .f32 y) = .ok (.float .f32 (d.sumP + y)) := by
      unfold Sm.D.rsOut
      rw [(hIv.re (hre hσ)).sw]
      exact floatE_add_fin (Sm.valFloat_float _) (Sm.valFloat_float _)
    simp only [Sm.next, hs, hv]
    split_ifs
    · exact toBar20_ne_none (numInv_afterSum hNum hv)
    · simp
  | bar22 => simp [Sm.next, hs]
  | shfl7 =>
    obtain ⟨recv, ok, rfl, v, hv⟩ := shfl_min_ok hpre hX hf hz (k := 0) (by omega) hg he hσ hs
    have hv' : minE [d.stg.al, recv] = .ok v := hv
    simp [Sm.next, hs, hv']
  | shfl8 =>
    obtain ⟨recv, ok, rfl, v, hv⟩ := shfl_min_ok hpre hX hf hz (k := 1) (by omega) hg he hσ hs
    have hv' : minE [d.stg.cm1, recv] = .ok v := hv
    simp [Sm.next, hs, hv']
  | shfl9 =>
    obtain ⟨recv, ok, rfl, v, hv⟩ := shfl_min_ok hpre hX hf hz (k := 2) (by omega) hg he hσ hs
    have hv' : minE [d.stg.cm2, recv] = .ok v := hv
    simp [Sm.next, hs, hv']
  | shfl10 =>
    obtain ⟨recv, ok, rfl, v, hv⟩ := shfl_min_ok hpre hX hf hz (k := 3) (by omega) hg he hσ hs
    have hv' : minE [d.stg.cm3, recv] = .ok v := hv
    simp [Sm.next, hs, hv']
  | store10 => simp [Sm.next, hs]
  | bar23 => simp [Sm.next, hs]
  | ldL =>
    obtain ⟨ac, bs, x, hk, hx⟩ := ldL_rebuild hpre hX hf hR hz hI hg he hσ hs
    simp [Sm.next, hs, hk, hx]
  | shfl11 =>
    obtain ⟨recv, ok, rfl, x, y, hx, hy⟩ := shfl11_ok hpre hX hf hI hg he hσ hs
    rw [next_shfl11 L g hs rfl hx hy]
    simp
  | shfl12 =>
    obtain ⟨recv, ok, rfl, b, hb⟩ := shfl12_ok hpre hX hf hI hg he hσ hs
    simp only [Sm.next, hs, hb]
    split_ifs
    · exact toBar20_ne_none hNum
    · simp
  | waitO =>
    obtain ⟨ok, rfl⟩ := Sm.shape_waitO hS hF' hs
    simp [Sm.next, hs]
  | ldO =>
    obtain ⟨vals, -, rfl⟩ := Sm.shape_ldO hF' hs
    simp [Sm.next, hs]
  | waitLdO => simp [Sm.next, hs, hso hg (len_of_get he).le hσ hs]
  | bar24 => simp [Sm.next, hs]
  | stO =>
    obtain ⟨vals, -, -, -, rfl⟩ := Sm.shape_stO hF' hs
    simp [Sm.next, hs]
  | waitStO =>
    simp only [Sm.next, hs]
    exact toBar20_ne_none hNum
  | bar20 =>
    simp [Sm.next, hs, Sm.psOk_float (hIv.re (hre hσ)).pv]
  | tmemSt =>
    obtain ⟨vals, -, -, -, rfl⟩ := Sm.shape_tmemSt hF' hs
    simp [Sm.next, hs]
  | tmemWait => simp [Sm.next, hs]
  | bar21 =>
    simp only [Sm.next, hs]
    split <;> first | exact afterSetup_ne_none _ _ _ | simp
  | arrive =>
    obtain ⟨-, rfl⟩ := Sm.shape_arrive hS hF' hs
    simp only [Sm.next, hs]
    exact afterSetup_ne_none _ _ _

/-- **The softmax region's successor in the default-partition machine is never `none`** at an
event of a launched thread: `Sm.next` is not, and the loop's exit does not fault. -/
theorem smNext_ne_none (hM : SmMaxOk Q L X) (hg : g < L.threads) {k : Nat} {d : Sm.D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    DComp.smNext L g d e ≠ none := by
  have hre : SmReal Q L X := smReal_of_max hX hM
  unfold DComp.smNext
  split
  · unfold DComp.exitNext
    have hn := exit_noFault hpre hX hf hre hg he hσ
    simp [hn]
  · intro h
    exact sm_next_ne_none hpre hX hf hR hz hI hso hss hsc hM hg he hσ (Option.map_eq_none_iff.mp h)

omit hpre hX hf hR hz hI hso hss hsc in
/-- **The epilogue's load**: at a followed `waitLd` the 64 loaded words pack into pairs and the
products by the reciprocal have outcomes (`Epi.D.loadOk`). It is a fact about the values of the
words of the `O` tile (their source classification), which nothing in the thread layer gives. -/
def EpiLoadOk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Epi.D} {e : Event}, g < L.threads → (X.tr g)[k]? = some e →
    (X.tr g)[k + 1]? ≠ none → St Q L X g k = some (some (.d (.epi d))) → d.site = .waitLd →
    d.loadOk = true

/-- **`FaultRest`**: the softmax region's states and the epilogue's `wait`, `shfl` and `waitLd`
do not reject a followed event (the epilogue's broadcast receives the warp index, `epi_recv`),
given the value chain's premises (`RoleReads`, `Rs.SmBaseZero`, `ScratchIt` of every
iteration), `SmOLoadOk`, `SmSLoadOk`, `SmScoreOk` and `EpiLoadOk`. -/
theorem faultRest_of (hM : SmMaxOk Q L X) (hload : EpiLoadOk Q L X) :
    FaultRest Q L X := by
  have hre : SmReal Q L X := smReal_of_max hX hM
  intro g k s e hg he hne hσ hopen
  obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.mp hne
  have hge : X.get (g, k) = some e := he
  cases s with
  | d s =>
    cases s with
    | dstart d => exact hopen.elim
    | pro d => exact hopen.elim
    | sm d =>
      intro h
      rw [next_d] at h
      exact smNext_ne_none hpre hX hf hR hz hI hso hss hsc hM hg hge hσ
        (Option.map_eq_none_iff.mp h)
    | epi d =>
      obtain ⟨h1, h2⟩ := epi_wait_ok hpre hX hf hre hg hσ
      have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
      exact epi_followed hpre hX hf hg he he' hσ (fun _ => ⟨h1, fun _ => h2⟩)
        (fun hs => hload hg he hne hσ hs) (fun hs pc m av b c recv ok hev => by
          rw [hm.w]
          exact epi_recv hpre hX hf hg (hev ▸ hge) hσ hs)
  | w s => exact hopen.elim

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
