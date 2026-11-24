-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsRdv

@[expose] public section

/-!
# The S/P/O handshake package from the threads' states

`pkg_of` builds `Sr.SrPkg` with the data of `HsData` (`cmOf`, `p0Of`, `tmOf`, `MmaOf`) from the
thread layer's facts, the scratch words of every iteration (for the agreement of the lazy-rescale
decisions, `Lk.decAgree_every`) and `PkgRest`, the statement that is not proved:

* `laneCommit` (`Mbar.Route.lane_commit`): a lane of the MMA warp other than the committing one
  polls `p_ready b` before the commit to `s_ready b` in the dependency order.

Everything else is proved: `SO.Facts` (`facts_of` with the parities of `HsParity`), the other
fields of `Mbar.Route` (`HsRoute`, `Safety.poll_spins`, `soft_bar` by `softBar_of` of `HsRdv`),
`Mbar.Bar128Witness` (`Bar.bar128Witness`), the `o_done` parity (`o_parity`), and
`Sr.Lane.tmOk`, `cm_ok`, `pAcq`, `sAcq`, `mma` (`qkAt_of`, `pvAt_of`), `st` (`HsStore`, with
the rendezvous `stRdv_of` of `HsRdv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `Mbar.Route.lane_commit` for CTA `c` with the committing lane `cmOf L X c` and the MMA warp's
lanes `MmaOf L c`. -/
def LaneCommit (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∀ {h b j i pc : Nat} {sp : TcCommit.Spec}, MmaOf L c h → h ≠ cmOf L X c → b < 2 →
    X.get (cmOf L X c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = sReady L c b →
    j < ((X.tr (cmOf L X c)).take i).countP (commitsTo (sReady L c b)) →
      j < okPolls (pReady L c b) (X.tr h) ∧
        Relation.TransGen (DepStep L kernel X)
          (.thread (h, MbarRing.Poll.nth X (pReady L c b) h j), true)
          (.thread (cmOf L X c, i), false)

/-- **What is open of the handshake package**, for every launched CTA. -/
structure PkgRest (L : Launch) (X : Execution) : Prop where
  laneCommit : ∀ c < L.grid, LaneCommit L X c
  /-- Every broadcast of warp 7 receives 7 (`Mb.mmaBcast_of`). -/
  bcast : Mma.MmaBcast L X

/-- An MMA event fires at a QK or a PV step of an MMA state. -/
theorem mma_state_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      ((∃ j, d.site = .qk j) ∨ ∃ j, d.site = .pv j) := by
  have hg : g < L.threads := event_thread_lt hX he
  obtain ⟨d, P, hσ, hsh⟩ :=
    mma_event_state hpre hX hf.sound hf.tracked hg he (.inl ⟨_, _, _, _, rfl⟩)
  refine ⟨d, P, hσ, ?_⟩
  unfold EvW.MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | exact .inr ⟨_, rfl⟩
    | (exfalso; simp at hsh)

/-- **`Sr.Lane.mma`**: every MMA of the CTA is a QK or PV MMA of its block. -/
theorem lane_mma (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hb : BaseWordRead L X)
    (hn : NumWordRead Q L X) (hB : Mma.MmaBcast L X) {c : Nat} {x : EvId} (hx : IsMma X x)
    (hxc : x.1 / L.block = c) :
    (∃ i, Sr.QkAt L X c (cmOf L X c) (tmOf c) x i) ∨
      ∃ m, Sr.PvAt L X c (cmOf L X c) (tmOf c) x m := by
  obtain ⟨g, k⟩ := x
  obtain ⟨pc, dst, sp, acc, mask, he⟩ := hx.get
  have hg : g < L.threads := event_thread_lt hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, ⟨j, hs⟩ | ⟨j, hs⟩⟩ := mma_state_site hpre hX hf he
  · left
    simp only at hxc
    subst hxc
    exact ⟨_, qkAt_of hpre hX hf hR hb hn hB hg hk hσ hs⟩
  · right
    simp only at hxc
    subst hxc
    exact ⟨_, (pvAt_of hpre hX hf hR hb hn hB hg hk hσ hs).2⟩

/-- **The handshake package.** -/
def pkg_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hb : BaseWordRead L X)
    (hn : NumWordRead Q L X) (hI : ∀ i, Lk.ScratchIt Q L X i)
    (r : PkgRest L X) :
    Sr.SrPkg L kernel asms mem0 X where
  cm := cmOf L X
  p0 := p0Of L
  tm := tmOf
  Mma := MmaOf L
  ctx c hc :=
    { cons := hX
      facts := facts_of hpre hX hf (fun hb' he => s_parity hpre hX hf hb' he)
        (fun hb' he => p_parity hpre hX hf hR hb' he) (fun he => f_parity hpre hX hf he)
      route :=
        { spin := fun _ _ _ _ _ _ he => Safety.poll_spins hX he
          p0_soft := p0_soft hpre hc
          cm_mma := cm_mma hpre hc
          soft_thread := fun h => h
          arrive_polls := fun hb' he => arrive_polls hpre hX hf hb' he
          soft_bar := softBar_of hpre hX hf (Lk.decAgree_every hpre hX hf hI) c
          qk_polls := fun hb' he hm => qk_polls hpre hX hf hR r.bcast hb' he hm
          pv_polls := fun he hm => pv_polls hpre hX hf hR r.bcast he hm
          lane_commit := r.laneCommit c hc }
      bar := Bar.bar128Witness hpre hX hf.sound hf.tracked
      opar := fun he => o_parity hpre hX hf he }
  lane c hc :=
    { tmOk := tmOk c
      cm_ok := cm_ok hpre hc
      pAcq := fun _ he => poll_acq hpre hX hf he
      sAcq := fun _ he => poll_acq hpre hX hf he
      mma := fun hx hxc => lane_mma hpre hX hf hR hb hn r.bcast hx hxc
      st := fun he htc => lane_st hpre hX hf hb
        (stRdv_of hpre hX hf (Lk.decAgree_every hpre hX hf hI) c) he htc }

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
