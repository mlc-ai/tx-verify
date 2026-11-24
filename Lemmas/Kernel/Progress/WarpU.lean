-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Warp
public import Lemmas.Kernel.FrameTrackedU

@[expose] public section
namespace PTX.Sched

open PTX Classical

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Flow.Code K A L g} {κ : Type} {key : Nat → κ}

theorem shape_recU (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).SoundU) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) {F : κ → Nat → CollShape}
    (hrec : ∀ {g k : Nat} {e : Event} {d : (C g).D}, g < L.threads →
      Frame.stateAt C X g k = some (some d) → X.get (g, k) = some e → isWarpColl e = true →
      kindShape e.kind = some (F (key g) (((X.tr g).take k).countP isWarpColl)))
    {x : Nat} (hx : x < L.threads) :
    ∀ k e, (X.tr x)[k]? = some e → isWarpColl e = true →
      kindShape e.kind = some (F (key x) (((X.tr x).take k).countP isWarpColl)) := by
  intro k e he hc
  obtain ⟨d, hd⟩ := Frame.state_of_noUbU hsound hX htr hub (g := x) (k := k) he
  exact hrec hx hd he hc

theorem rec_maskU (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).SoundU) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) (hw : WarpRec C X key) {x k : Nat} {e : Event} {s : CollShape}
    (he : X.get (x, k) = some e) (hc : isWarpColl e = true) (hs : kindShape e.kind = some s) :
    s.Full := by
  obtain ⟨F, hfull, hrec⟩ := id hw
  have hx : x < L.threads := by
    by_contra hx
    have := len_of_get he
    rw [hX.outside x (by omega)] at this
    simp at this
  exact rec_full hfull (shape_recU hX hsound htr hub hrec hx k e he hc) hs

/-- **No lane is past a lane that has not exited.** A lane of the warp of `g`, whose run has
not stopped, has made at most as many warp collectives as `g`. -/
theorem no_aheadU (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
    (hk : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).SoundU) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) (hw : WarpRec C X key) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    (hlt : (X.tr g).countP isWarpColl < (X.tr h).countP isWarpColl) : False := by
  obtain ⟨F, hfull, hrec⟩ := id hw
  have hh : h < L.threads := hs.1.2.1
  have hsh : SameWarp L h g := sameWarp_symm hs
  have hkey : key h = key g := (hk hs).symm
  have hrg := shape_recU hX hsound htr hub hrec hg
  have hrh := shape_recU hX hsound htr hub hrec hh
  obtain ⟨j, e, hj, hc, hjn⟩ := MbarRing.Slot.exists_nth_countP isWarpColl
    (xs := X.tr h) (c := (X.tr g).countP isWarpColl) hlt
  have hjl : j ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp hj).1.le
  have hse := hrh j e hj hc
  rw [hjn, hkey] at hse
  -- the events of a kind before `h`'s `n`-th warp collective are as many as in `g`'s trace
  have cnt : ∀ (q : Event → Bool) (i : Nat), (∀ e, q e = true → isWarpColl e = true) →
      (∀ e s, kindShape e.kind = some s → q e = (s.tag == i)) →
      ((X.tr h).take j).countP q = (X.tr g).countP q := by
    intro q i hq hqr
    rw [count_shape F (key h) hrh q (fun s => s.tag == i) hq hqr j hjl,
      ← List.take_length (l := X.tr g),
      count_shape F (key g) hrg q (fun s => s.tag == i) hq hqr _ le_rfl, hjn, hkey,
      List.take_length]
  have hnx : ∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩ := fun k pc hk => hr.no_exit hk
  have hlg : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [isWarpColl, Bool.false_eq_true] at hc
  case shfl m a b c recv ok =>
    have hc' := cnt Execution.isShfl 0 shfl_coll shfl_tag
    rcases Step.shfl_lane_of_ready hX hj ⟨⟨_, _, _, _, _, _, _, hj⟩, rfl⟩ hsh with
      ⟨j', hk'⟩ | ⟨k, pce, hex, -⟩
    · have := Step.ShflK.lt_count hk'
      simp only at this
      omega
    · exact hnx k pce hex
  case elect mask inst leader =>
    have hc' := cnt isElectEv 1 elect_coll elect_tag
    have hef : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l →
        mask = 4294967295 := fun {e} _ _ _ _ he' =>
      rec_maskU hX hsound htr hub hw (x := e.1) (k := e.2) he' rfl rfl
    have hel : X.Elect (h, j) pc mask inst leader := hj
    have hmem : ∀ {x y} z pc' m i l, X.Elect (x, z) pc' m i l → electMember m (laneOf L y) :=
      fun z _ _ _ _ he' => by
        rw [hef he']; exact full_member (Nat.mod_lt _ (by decide))
    obtain ⟨x, hp⟩ := ElectOrd.partner hX hsh hel (hmem j _ _ _ _ hel)
    have heq := ElectOrd.ordinal_eq hX hsh (fun z => hmem z) (fun z => hmem z) hp
    obtain ⟨_, _, _, _, _, _, _, -, hx⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hx)
    have := PTX.countP_take_lt (p := isElectEv) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [elections] at heq
    omega
  case warpBar mask inst =>
    have hc' := cnt Execution.isWarpBar 2 warpBar_coll warpBar_tag
    have hmask : ∀ {x} (hx : x < L.threads) {y m i}, X.WarpBar (x, y) m i → m = 4294967295 := by
      intro x hx y m i ⟨p, hp⟩
      exact rec_full hfull (shape_recU hX hsound htr hub hrec hx y _ hp rfl) rfl
    have hwb : X.WarpBar (h, j) mask inst := ⟨pc, hj⟩
    obtain ⟨x, hp⟩ := WarpBar.partner hX hsh hwb (by rw [hmask hh hwb]; exact full_member hlg)
    have heq := WarpBar.ordinal_eq hX hsh
      (fun y m i hy => by rw [hmask hh hy]; exact full_member hlg)
      (fun y m i hy => by rw [hmask hg hy]; exact full_member (Nat.mod_lt _ (by decide))) hp
    obtain ⟨_, _, -, p', hp'⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hp')
    have := PTX.countP_take_lt (p := Execution.isWarpBar) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [warpBars] at heq
    omega
  case vote mask a ballot =>
    have hc' := cnt Flow.isBallot 3 vote_coll vote_tag
    have hm : mask = 4294967295 := rec_full hfull hse rfl
    subst hm
    -- a vote event of a launched thread counts as a full-mask vote exactly when it is a ballot
    have hvc : ∀ x, x < L.threads → ∀ ev ∈ X.tr x,
        (voteClass ev.kind).any (·.mask == 4294967295) = true ↔ Flow.isBallot ev = true := by
      intro x hx ev hev
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hev
      have hget : X.get (x, k) = some (X.tr x)[k] := List.getElem?_eq_getElem hk
      revert hget
      generalize (X.tr x)[k] = ev
      intro hget
      obtain ⟨pc', kd⟩ := ev
      cases kd <;> simp [voteClass, Flow.isBallot]
      case vote m' a' b' => exact rec_maskU hX hsound htr hub hw hget rfl rfl
      case voteMode md m' a' d' => exact fun _ => no_voteMode hK hX hget
    have hbit : (4294967295 : Nat).testBit (laneOf L g) = true := (full_member hlg).2
    have hk : X.MaskK voteClass (h, j) 4294967295 (((X.tr h).take j).countP
        fun ev => (voteClass ev.kind).any (·.mask == 4294967295)) := ⟨⟨_, _, hj, rfl, rfl⟩, rfl⟩
    rcases Step.vote_lane_of_ready hX hk hsh hbit with ⟨j', hk'⟩ | ⟨k, pce, hex⟩
    · have hlt := Step.MaskK.lt_count hk'
      unfold Step.maskCount at hlt
      rw [List.countP_congr (hvc g hg), List.countP_congr
        (fun ev hev => hvc h hh ev (List.mem_of_mem_take hev))] at hlt
      omega
    · exact hnx k pce hex

end
end PTX.Sched
