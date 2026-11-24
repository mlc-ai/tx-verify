-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaReg
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBarAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAcc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Stops
public import Kernels.FlashAttn4Fwd.Proof.Safety.Resource
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Every thread's register request (`Safety.RegFacts`)

* **No reentry.** No role's step enters its `setmaxnreg` site: the roles' parts
  `Cross.NoRegReentry_soft`, `_corr`, `_mma`, `_store`, `_loader`, `_idle` give
  `Cross.NoRegReentry` for every role (`noRegReentry_all`).
* **First request.** An event of a register request fires at a site of the register-request
  kind (`reg_kind`). A thread at a prologue state or at a register-request site has made no
  request (`reg_state_first`): the prologue has no register-request site, and no role step
  enters one. So a thread's request is its first.
* **Site and count.** The site of the request is its role's `setmaxnreg` site (`Cross.reg_site`)
  and its role is that of the thread's warp (`Cross.role_of_state`). The instruction at the site
  gives the direction and count (`Flow.code_setMaxReg_0` to `Flow.code_setMaxReg_5`).
* **Exit.** An exit fires at a role's exit site, which is past the role's register request, so
  the thread has made a request before it (`Cross.reg_made`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Cross.NoRegReentry` for every role.** -/
theorem noRegReentry_all : Cross.NoRegReentry L := by
  intro g r r' e h
  cases r with
  | softmax d => exact Cross.NoRegReentry_soft h
  | corr d => exact Cross.NoRegReentry_corr h
  | mma d => exact Cross.NoRegReentry_mma h
  | store d => exact Cross.NoRegReentry_store h
  | loader d => exact Cross.NoRegReentry_loader h
  | idle s => exact Cross.NoRegReentry_idle h

/-- A register request fires at a site of the register-request kind. -/
theorem reg_kind {g : Nat} {d : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e o)
    (hr : Cross.isReg e = true) : nextKind d = .reg := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [Cross.isReg, Bool.false_eq_true] at hr
  have hop := fires_setMaxReg_op hf rfl
  have hk := Cross.site_kindOp d hc
  rw [hop] at hk
  generalize nextKind d = k at hk
  cases k <;> first | rfl | simp [Cross.kindOp] at hk

/-- **A thread at a prologue state or at a register-request site has made no request.** -/
theorem reg_state_first (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g : Nat}
    (hg : g < L.threads) :
    ∀ j d, Frame.stateAt (code L) X g j = some (some d) →
      (nextKind d = .reg ∨ ∃ p, d = .inl p) → ∀ x ∈ (X.tr g).take j, Cross.isReg x = false := by
  have htr := Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg
  have h := Code.run_inv (sound hpre hg) htr
    (fun d es => (nextKind d = .reg ∨ ∃ p, d = .inl p) → ∀ x ∈ es, Cross.isReg x = false)
    (fun _ x hx => (List.not_mem_nil hx).elim) ?_
  · exact fun j d hσ => h j d hσ
  intro d d' pre e t ins o hJ _ _ hc hf hn hd' x hx
  rcases d with p | r
  · rcases List.mem_append.mp hx with hx | hx
    · exact hJ (.inr ⟨p, rfl⟩) x hx
    · rw [List.mem_singleton.mp hx]
      cases hr : Cross.isReg e
      · rfl
      · have := reg_kind hc hf hr
        obtain ⟨s⟩ := p
        cases s <;> simp [nextKind, prologueKind] at this
  · obtain ⟨r', rfl, -⟩ := code_next_inr hn
    rcases hd' with hk | ⟨p, hp⟩
    · exact absurd hk (noRegReentry_all hn)
    · cases hp

/-- **A thread's register request is its first, at its warp's site, with its warpgroup's
direction and count.** -/
theorem reg_request (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc n inst : Nat} {inc : Bool} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    SetMaxNReg.ordinal X (g, k) = 0 ∧ pc = Safety.regPc (warpOf L g) ∧
      (inc, n) = Safety.regOf (warpOf L g) := by
  obtain ⟨d, t, ins, u, hσ, -, -, -, hc, hf⟩ :=
    Cross.event_cont hpre hX ht (J := fun _ _ _ => True) (fun g _ => Cross.trueJ_run L g) he
      (by rintro (⟨f, hf⟩ | hf) <;> cases hf)
  have hreg : nextKind d = .reg := reg_kind hc hf rfl
  refine ⟨?_, ?_⟩
  · refine List.countP_eq_zero.mpr fun x hx => ?_
    have h0 := reg_state_first hpre hX hg k d hσ (.inl hreg) x hx
    change ¬ Cross.isReg x = true
    simp [h0]
  have hpc := EventFrame.fires_source_pc hf
  have hop := fires_setMaxReg_op hf rfl
  simp only at hpc
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases s <;> simp [nextKind, prologueKind] at hreg
  have hw := Cross.role_of_state hpre hX hg hσ
  rcases Cross.reg_site r hreg with ⟨s, rfl, hs⟩ | ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩ |
      ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩ | ⟨d, rfl, hs⟩
  · change kernel.code[s.site.pc]? = some ins at hc
    change pc = s.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    simp [Safety.regPc, Safety.regOf, hw, hpc, Idle.Site.pc]
  · change kernel.code[d.site.pc]? = some ins at hc
    change pc = d.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_1)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    simp [Safety.regPc, Safety.regOf, hw, hpc, Loader.Site.pc]
  · change kernel.code[d.site.pc]? = some ins at hc
    change pc = d.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_2)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    simp [Safety.regPc, Safety.regOf, hw, hpc, Mma.Site.pc]
  · change kernel.code[d.site.pc]? = some ins at hc
    change pc = d.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_3)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    simp [Safety.regPc, Safety.regOf, hw, hpc, Store.Site.pc]
  · change kernel.code[d.site.pc]? = some ins at hc
    change pc = d.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_4)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    simp [Safety.regPc, Safety.regOf, hw, hpc, Softmax.Site.pc]
  · change kernel.code[d.site.pc]? = some ins at hc
    change pc = d.site.pc at hpc
    rw [hs] at hc hpc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [Role.kind, RoleKind.Warp] at hw
    have h8 : ¬ warpOf L g < 8 := by omega
    have h12 : warpOf L g < 12 := hw.2
    simp [Safety.regPc, Safety.regOf, h8, h12, hpc, Correction.Site.pc]

/-- **A thread exits after its register request.** -/
theorem reg_exit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) : 1 ≤ SetMaxNReg.ordinal X (g, k) := by
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => Cross.trueJ_run L g) he
      nofun
  have hk := Cross.site_kindOp d hc
  have hex : nextKind d = .exit := by
    generalize nextKind d = k at hk
    rcases fires_exit_op hf rfl with hop | hop <;> rw [hop] at hk <;>
      cases k <;> first | rfl | simp [Cross.kindOp] at hk
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases s <;> simp [nextKind, prologueKind] at hex
  obtain ⟨x, hx, hr⟩ := Cross.reg_made hpre hX hg k r hσ (by rw [hex]; decide)
  exact List.countP_pos_iff.mpr ⟨x, hx, hr⟩

/-- **The thread layer's facts for the register requests** (`Safety.RegFacts`). -/
theorem RegFacts_holds (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : Safety.RegFacts L X where
  request hg hreq := reg_request hpre hX ht hg hreq
  exit hg he := reg_exit hpre hX ht hg he

end
end PTX.Kernels.FlashAttn4Fwd.Proof
