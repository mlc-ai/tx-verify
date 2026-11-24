-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftScore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Warp
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2

@[expose] public section

/-! # The second P-ready objects, the warp barriers and the Tensor Memory roles

Only the elected softmax lane arrives on a second P-ready object (`P2Facts_p2_arrive`): the
loader arrives on ring full barriers, the MMA warp on the handshake barrier, the store warp on
the free barriers, the correction warps on the credit, staged and first P-ready barriers. At its
`p2Arr` site the thread has made one arrival per earlier tile, one warp barrier per tile
(`Counts.warpBar`), and led every election of its trace (`Counts.lead` with the dichotomy of
`Static.elect_dichotomy_take`). A softmax warp barrier names every lane (its code's mask is
`-1`). Tensor Memory loads and stores are instructions of the softmax and correction sites only
(`ScoreFacts_tc_role`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Only softmax threads arrive on a second P-ready object.** -/
theorem soft_p2_only {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive (pReady2Bar L c st) tx cnt rel sc⟩) :
    warpOf L g < 8 := by
  obtain ⟨r, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h) (fun h => h)
  have hw := Cross.role_of_state hpre hX hg hσ
  have hk : (⟨pc, .arrive (pReady2Bar L c st) tx cnt rel sc⟩ : Event).kind =
      .arrive (pReady2Bar L c st) tx cnt rel sc := rfl
  have hb := pReady2Bar_eq L c ⟨st, hst⟩
  cases r with
  | softmax d => exact hi.warp
  | store d =>
    exfalso
    obtain ⟨st0, -, h1, -⟩ := Store.ev_arrive (Store.shape hpre hat hi hc hf)
    rw [Store.freeAt_eq, freeBar_fbar L _ st0.isLt, hb] at h1
    exact absurd (FBar.loc_inj h1).1 (by simp)
  | loader d =>
    exfalso
    obtain ⟨b', hb', hm', -⟩ := Loader.arrive_fact hpre hg hJ hi
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf hk
    rw [hb] at hm'
    obtain ⟨rfl, -⟩ := FBar.loc_inj hm'
    simp [FBar.isFull] at hb'
  | mma d =>
    exfalso
    obtain ⟨-, hm', -⟩ := arrive_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hf) hk
    rw [hb] at hm'
    exact absurd (FBar.loc_inj hm').1 (by simp)
  | corr d =>
    exfalso
    obtain ⟨hw8, hw12⟩ := hw
    obtain ⟨-, -, d', -, -, -, -, h⟩ := corr_arrive hpre hX ht hw8 hw12 he
    rcases h with ⟨a, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', -, hm⟩ <;>
      simp only [pReady2Bar, Correction.ownLoc, Correction.leadLoc, Correction.sb,
        Loc.mk.injEq] at hm <;> omega
  | idle s =>
    exfalso
    obtain ⟨b, off, tx', c', cl, sc0, st', hop, -⟩ := fires_arrive_flags hf hk
    exact (Idle.site_not_poll s.site).2 (OpPcsFast.mem kernel_arrive_pcs hc (by rw [hop]; rfl))

/-- **`P2Facts.p2_arrive`**: an arrival on a second P-ready object is the elected softmax lane's
of the stage, of the pair led by the object's CTA, one release unit at cluster scope, after one
arrival per earlier tile, the tile's warp barrier and an election that returned its lane. -/
theorem P2Facts_p2_arrive {g k pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .arrive (pReady2Bar L c st) tx cnt rel sc⟩) :
    leadCta (ctaOf L g) = c ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
      tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster ∧
      arrivals (pReady2Bar L c st) ((X.tr g).take k) + 1 = sPolls L X g st k ∧
      warpBars X g k = sPolls L X g st k ∧
      ∃ e pce inst, e < k ∧ X.get (g, e) = some ⟨pce, .elect fullMask inst (laneOf L g)⟩ := by
  have hw := soft_p2_only hpre hX ht hg hst he
  obtain ⟨d, -, hc, hi, hpc, htx, hcnt, h⟩ := soft_arrive hpre hX ht hw he
  have hat := Static.arrive_attr hX he
  have hso : Softmax.stOf L g = warpOf L g / 4 := rfl
  rcases h with ⟨lp, -, hm⟩ | ⟨lp, hs, hm⟩
  · simp only [pReady2Bar, Softmax.leadLoc, Softmax.sb, Loc.mk.injEq] at hm
    omega
  have hm' := hm
  simp only [pReady2Bar, Softmax.leadLoc, Softmax.sb, Loc.mk.injEq] at hm'
  obtain ⟨-, hcc, hoff⟩ := hm'
  have hst' : warpOf L g / 4 = st := by omega
  subst hst'
  have hcl : leadCta (ctaOf L g) = c := by simp only [leadCta]; omega
  subst hcl
  have hlead := hc.lead lp hs
  have hL : ElectLead L g ((X.tr g).take k) :=
    (Static.elect_dichotomy_take hX g k).resolve_right hlead
  have ht0 := hi.tile0
  have htr := hi.trip
  refine ⟨rfl, hw, rfl, htx, hcnt, hat.1, hat.2 (by rw [← hpc, hs]; exact (soft_arr_cluster lp).2),
    ?_, ?_, ?_⟩
  · unfold sPolls
    rw [soft_pReady2Bar, hc.pReady2 hL, soft_sFullBar, hc.score]
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 htr ⊢
    subst hs
    cases lp <;> simp [Softmax.p2Pos, Softmax.sPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.inTrip, Softmax.Site.tile0Ld, Softmax.Site.afterP2] at ht0 htr ⊢
    omega
  · unfold sPolls warpBars
    rw [hc.warpBar, soft_sFullBar, hc.score]
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ht0 htr ⊢
    subst hs
    cases lp <;> simp [Softmax.wbPos, Softmax.sPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.inTrip, Softmax.Site.tile0Ld, Softmax.Site.afterWB] at ht0 htr ⊢
    omega
  · simp only [ElectNonLead, not_forall, Classical.not_not] at hlead
    obtain ⟨x, hx, mask, inst, ld, hk, hld⟩ := hlead
    obtain ⟨j, hj, hxj⟩ := get_of_mem_take hx
    have hmask := Static.elect_mask hX g x (List.mem_of_mem_take hx) mask inst ld hk
    subst hld hmask
    refine ⟨j, x.pc, inst, hj, ?_⟩
    rw [hxj]
    obtain ⟨xp, xk⟩ := x
    simp only at hk ⊢
    rw [hk]
    rfl

/-- **`P2Facts.soft_warpBar`**: a softmax thread's warp barriers name every lane. -/
theorem P2Facts_soft_warpBar {h j m inst : Nat} (_hh : h < L.threads) (hw : warpOf L h < 8)
    (he : X.WarpBar (h, j) m inst) : m = fullMask := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨d, t, ins, o, -, -, -, -, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  cases hsd : d.site with
  | warpBar lp =>
    rw [hsd] at hcode hf
    have hop : ins.op = .warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩ := by
      cases lp
      · exact congrArg Instr.op (Option.some.inj (hcode.symm.trans Flow.code_warpBar_0))
      · exact congrArg Instr.op (Option.some.inj (hcode.symm.trans Flow.code_warpBar_1))
    rw [hop] at hf
    simp only [eventTmpl, warpTmpl_barWarp, warpBarTmpl, readBits, pure, Except.pure] at hf
    split_ifs at hf
    · obtain ⟨inst', hk, -⟩ := hf
      injection hk with h1 h2
      injection h2 with h3 h4
    · simp [Fires] at hf
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

/-- **`ScoreFacts.tc_role`**: Tensor Memory loads and stores are made by softmax and correction
threads. -/
theorem ScoreFacts_tc_role {g i a : Nat} {vals : List Value} {sh : TcShape}
    (htc : X.TLd (g, i) a vals sh ∨ X.TSt (g, i) a vals sh) : g < L.threads ∧ warpOf L g < 12 := by
  obtain ⟨pc, tk, he, htk⟩ : ∃ pc tk, X.get (g, i) = some ⟨pc, .tc tk⟩ ∧
      (tk = .ld a vals sh ∨ tk = .st a vals sh) := by
    rcases htc with ⟨pc, he⟩ | ⟨pc, he⟩
    · exact ⟨pc, _, he, .inl rfl⟩
    · exact ⟨pc, _, he, .inr rfl⟩
  have hg := Frame.lt_of_get hX he
  refine ⟨hg, ?_⟩
  obtain ⟨r, t, ins, u, hσ, -, -, hi, hc, hf⟩ :=
    role_event hpre hX ht he (fun h => by rcases h with ⟨f, h⟩ | h <;> cases h)
      (by simp [Prologue.ProKind])
  have hw := Cross.role_of_state hpre hX hg hσ
  have hd : tcDataOp ins.op = true :=
    fires_tcData_op hf (by rcases htk with rfl | rfl <;> rfl)
  have hany : tcAnyOp ins.op = true := by
    revert hd; cases ins.op <;> simp [tcDataOp, tcAnyOp]
  cases r with
  | softmax d => exact Nat.lt_trans hi.warp (by decide)
  | corr d => exact hw.2
  | loader d =>
    exact absurd (OpPcsFast.mem Loader.kernel_tc_pcs hc hany) (Loader.site_not_tc d.site)
  | store d => exact absurd he (Cross.hi_no_tc hpre hX ht (.inl hw))
  | idle s => exact absurd he (Cross.hi_no_tc hpre hX ht (.inr hw))
  | mma d =>
    have := Mma.tcData_ops.op (s := d.site) rfl hc
    rw [hd] at this
    cases this

/-- **`ScoreFacts.tc_shape`**: Tensor Memory loads and stores have the shape `.32x32b`, the shape
of every `tcgen05.ld` and `tcgen05.st` of the kernel (`kernel_tc_shape`). -/
theorem ScoreFacts_tc_shape {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (htc : X.TLd e a vals sh ∨ X.TSt e a vals sh) : sh = .s32x32b := by
  obtain ⟨g, i⟩ := e
  rcases htc with ⟨pc, he⟩ | ⟨pc, he⟩
  · exact tc_shape_of_get hpre hX ht he (.inl rfl)
  · exact tc_shape_of_get hpre hX ht he (.inr rfl)

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
