-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.VoteInv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Carry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceSk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Lemmas.Flow.RoleStep
import Lemmas.Flow.StoreElem
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The data thread machine follows a lane of warpgroup 0

`FollowW P L X g k sc`: up to the event `k` of the lane `g`, the data machine of the lane (a
startup state, then warpgroup 0's) is in a state with the invariants of `Wg0/Data` on the trace
so far: the block's loads (`InvW`), the epilogue's reads (`InvE`), the chain's flag (`OkInv`), the
carried statistics (`CarryW`) and the vote (`VoteInv`). Only the statement is public; the machine
stays in the body. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

/-- **The step into a state**: on the chain, the state reached by event `j` follows a state at the
pc of event `j - 1` (or that event closes a block). -/
def PrevPc (P : Params) (L : Launch) (X : Execution) (g j : Nat) (d : D) : Prop :=
  ∀ i, j = i + 1 → (d.c.site = .smr ∧ ∀ f ∈ (X.tr g).take j, f.pc < 103) ∨
    ∃ f c, (X.tr g)[i]? = some f ∧ c.site.pc = f.pc ∧
      Control.succ P L g (warpW L g) c f = some (some d.c) ∧
      (d.ok = true → c.site = .arrS ∨ succOk c d.c = true)

/-- A state of a lane of warps 0-3: the startup's or warpgroup 0's. -/
private theorem w0_slot (hFw : Follow P L X) (hw : warp L g < 4)
    (hg : g < L.threads) {i : Nat} {s : (threadD P L g).D}
    (hs : Frame.stateAt (threadD P L) X g i = some (some s)) :
    (∃ b, s.1 = .inl b) ∨ ∃ d, s.1 = .inr ⟨.inl .wg0, d⟩ := by
  have hJ := (follow_iff.mp hFw g hg i).2 _ (control_of_data hs)
  obtain ⟨q, n⟩ := s
  rcases q with b | ⟨e | r, d⟩
  · exact .inl ⟨b, rfl⟩
  · cases e with
    | wg0 => exact .inr ⟨d, rfl⟩
    | wg1 | dequant =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

/-- A role entered from the startup starts at its first state. -/
private theorem w0_enter {sc : ℝ} {b : Startup.D} {d : D} {l : List Event}
    (h : Code.enter (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) b = .inr ⟨.inl .wg0, d⟩)
    (hl : ∀ f ∈ l, f.pc < 103) :
    (InvW l d ∧ OkInv d ∧ CarryW sc l d ∧ VoteInv l d ∧ InvE l d ∧ InvSk l d) ∧
      d.c.site = .smr := by
  unfold Code.enter at h
  split at h
  · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases eq_of_heq h
    have h0 : (code P L g (warpW L g)).init.ok = false := rfl
    refine ⟨⟨invW_pre hl, okInv_init, ?_, ?_, invE_pre hl, invSk_pre hl⟩, rfl⟩
    · intro h _; cases (h0.symm.trans h)
    · intro h _; cases (h0.symm.trans h)
  · cases h

/-- **The data thread machine follows the lane** up to its event `k`, with the invariants. -/
private theorem followW0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ)) {sc : ℝ}
    (hx : Rd (.bits 32 (scX L)) (sc : EReal)) (hv : W0Valid sc ((X.tr g).take k)) :
    ∀ j ≤ k, ∃ s, Frame.stateAt (threadD P L) X g j = some (some s) ∧
      (∀ b, s.1 = .inl b → ∀ f ∈ (X.tr g).take j, f.pc < 103) ∧
      (∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → InvW ((X.tr g).take j) d ∧ OkInv d ∧
        CarryW sc ((X.tr g).take j) d ∧ VoteInv ((X.tr g).take j) d ∧
        InvE ((X.tr g).take j) d ∧
        InvSk ((X.tr g).take j) d) ∧
      (∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → PrevPc P L X g j d) ∧
      ∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → PcBound ((X.tr g).take j) d ∧
        PcSeen ((X.tr g).take j) d := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σk, hσk⟩ := hσ
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  intro j hj
  induction j with
  | zero =>
    refine ⟨_, Frame.stateAt_zero, fun b _ f hf => by simp at hf, fun d hd => ?_,
      fun d _ i hi => by omega, fun d hd => ⟨pcBound_early d (fun f hf => by simp at hf),
        pcSeen_smr (w0_enter (sc := sc) (l := (X.tr g).take 0) (b := (startupCode P L g).init) hd
          (fun f hf => by simp at hf)).2⟩⟩
    exact (w0_enter (sc := sc) (b := (startupCode P L g).init) hd (fun f hf => by simp at hf)).1
  | succ j ih0 =>
    obtain ⟨s, hst0, hpre, hI, -, hB⟩ := ih0 (by omega)
    have hev : X.get (g, j) = some ((X.tr g)[j]'(by omega)) := List.getElem?_eq_getElem _
    generalize (X.tr g)[j]'(by omega) = ev at hev
    have hevu : ∀ fl, ev.kind ≠ .ub fl := fun fl h => by
      obtain ⟨pc, kd⟩ := ev
      cases h
      have := ub_last hX hev he
      omega
    have hsg := control_of_data hst0
    have hcc : Frame.stateAt (thread P L) X g (j + 1) =
        (thread P L g).next (eraseThread P L g s) ev := by
      rw [Frame.stateAt_succ hev, hsg]; rfl
    obtain ⟨τ, hτ⟩ : ∃ τ, (thread P L g).next (eraseThread P L g s) ev = some (some τ) := by
      rcases h : (thread P L g).next (eraseThread P L g s) ev with _ | _ | τ
      · rw [Frame.stateAt_none_mono (hcc.trans h) (show j + 1 ≤ k by omega)] at hσk
        cases hσk
      · exact absurd (hcc.trans h) (follow_iff.mp hFw g hg (j + 1)).1
      · exact ⟨τ, rfl⟩
    have hpp := Frame.event_pcU hsD hX hev hst0 hevu
    obtain ⟨-, -, -, -, hinv, -, -⟩ := Frame.fired_siteU hsD hX hev hst0 hevu
    have hsplit : (X.tr g).take (j + 1) = (X.tr g).take j ++ [ev] := by
      have hev' : (X.tr g)[j]? = some ev := hev
      rw [List.take_add_one, hev']; rfl
    have hvj : W0Valid sc ((X.tr g).take j ++ [ev]) := by
      rw [← hsplit]
      have := hv.take (j := j + 1)
      rwa [List.take_take, min_eq_left (by omega)] at this
    rw [Frame.stateAt_succ hev, hst0, hsplit]
    obtain ⟨q, n⟩ := s
    rcases w0_slot hFw hw hg hst0 with ⟨b, hb⟩ | ⟨d, hd⟩
    · obtain rfl : q = .inl b := hb
      obtain ⟨s', hs'⟩ := Code.roleThread_next_start_of (R' := fragD P L g) (n' := n) hτ
      have hlt : ∀ f' ∈ (X.tr g).take j ++ [ev], f'.pc < 103 := by
        intro f' hev'
        rcases List.mem_append.mp hev' with h | h
        · exact hpre b rfl f' h
        · obtain rfl := List.mem_singleton.mp h
          have := startup_pc (d := b) (n := n) hinv
          have h2 : f'.pc = (thread P L g).pc (.inl b, n) := hpp
          omega
      refine ⟨s', hs', fun b' hb' => ?_, fun d' hd' => ?_, fun d' hd' i hi => ?_,
        fun d' hd' => by
          obtain ⟨b', -, hb'⟩ := Code.roleThread_next_start hs'
          exact ⟨pcBound_early d' hlt,
            pcSeen_smr (w0_enter (sc := sc) (hb'.symm.trans hd') hlt).2⟩⟩
      · intro f' hev'
        exact hlt f' hev'
      · obtain ⟨b', -, hb'⟩ := Code.roleThread_next_start hs'
        exact (w0_enter (sc := sc) (hb'.symm.trans hd') hlt).1
      · obtain ⟨b', -, hb'⟩ := Code.roleThread_next_start hs'
        exact .inl ⟨(w0_enter (sc := sc) (hb'.symm.trans hd') hlt).2, hsplit ▸ hlt⟩
    · obtain rfl : q = .inr ⟨.inl .wg0, d⟩ := hd
      obtain ⟨c', hc, -⟩ := Code.roleThread_next_role hτ
      have hn : (fragD P L g .wg0).next d ev = some (some (dataNext L d c' ev)) := by
        change Wg0.Data.succ P L g (warpW L g) d ev = _
        simp only [Wg0.Data.succ, show Control.succ P L g (warpW L g) d.c ev = some (some c')
          from hc, Option.map_some]
      obtain ⟨s', hs'⟩ : ∃ s', (threadD P L g).next (.inr ⟨.inl .wg0, d⟩, n) ev =
          some (some s') := Code.roleThread_next_of_role hn
      have hd2 : ∀ d₁, s'.1 = .inr ⟨.inl .wg0, d₁⟩ → d₁ = dataNext L d c' ev := fun d₁ hd₁ => by
        obtain ⟨d'', hn', hs''⟩ := Code.roleThread_next_role hs'
        rw [hs''] at hd₁
        simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hd₁
        subst hd₁
        exact (Option.some.inj (Option.some.inj (hn.symm.trans hn'))).symm
      refine ⟨s', hs', fun b' hb' => ?_, fun d₁ hd₁ => ?_, fun d₁ hd₁ i hi => ?_,
        fun d₁ hd₁ => ?_⟩
      · obtain ⟨d'', -, hs''⟩ := Code.roleThread_next_role hs'
        rw [hs''] at hb'; cases hb'
      · obtain ⟨d'', hn', hs''⟩ := Code.roleThread_next_role hs'
        rw [hs''] at hd₁
        simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hd₁
        subst hd₁
        have hd'' : d'' = dataNext L d c' ev :=
          (Option.some.inj (Option.some.inj (hn.symm.trans hn'))).symm
        subst hd''
        obtain ⟨hIW, hOk, hCar, hVote, hIE, hSk⟩ := hI d rfl
        refine ⟨invW_step hIW hinv hpp hc, okInv_next hOk hn', carryW_step hx hIW hCar hpp hc hvj,
          voteInv_step hVote hpp hc, invE_step hIE hpp, invSk_step hSk hpp⟩
      · obtain rfl := hd2 d₁ hd₁
        have hij : i = j := by omega
        subst hij
        refine .inr ⟨ev, d.c, hev, hpp.symm, ?_, fun hok => ?_⟩
        · rw [dataNext_c]
          exact hc
        by_cases hs : d.c.site = .arrS
        · exact .inl hs
        · refine .inr ?_
          rw [dataNext_eq hs] at hok
          rw [dataNext_c]
          exact (Bool.and_eq_true_iff.mp hok).2
      · rw [hd2 d₁ hd₁]
        exact ⟨pcBound_step (hB d rfl).1 hpp hc, pcSeen_step (hB d rfl).2 hpp hc⟩

end Wg0

open Wg0.Data in
/-- The scale word of the launch reads as the scale of the parameters. -/
theorem w0_scale_rd (hp : Pre P L m) : Rd (.bits 32 (scX L)) (P.scale : EReal) := by
  obtain ⟨b, hb, hbytes, hval⟩ := hp.paramScale
  obtain ⟨hs32, hbs⟩ := scaleBits_spec hp
  have hbe : ∀ k < 4, leByte b k = leByte (scaleBits L) k := fun k hk =>
    Option.some.inj ((hbytes k hk).symm.trans (hbs k hk))
  have e : ∀ k < 4, (b / 256 ^ k) % 256 = (scaleBits L / 256 ^ k) % 256 := fun k hk => by
    have := congrArg BitVec.toNat (hbe k hk)
    simpa [leByte] using this
  have h0 := e 0 (by norm_num)
  have h1 := e 1 (by norm_num)
  have h2 := e 2 (by norm_num)
  have h3 := e 3 (by norm_num)
  simp only [pow_zero, Nat.div_one, Nat.pow_one] at h0 h1
  have hbb : b = scaleBits L := by
    have e2 : (256 : Nat) ^ 2 = 65536 := by norm_num
    have e3 : (256 : Nat) ^ 3 = 16777216 := by norm_num
    rw [e2] at h2
    rw [e3] at h3
    omega
  have hsx : scX L = BitVec.ofNat 64 b := by
    unfold scX
    congr 1
    simp only [leNat, leByteOf, BitVec.toNat_ofNat, pow_zero, Nat.div_one]
    norm_num
    omega
  have hq := Option.map_eq_some_iff.mp hval
  obtain ⟨q, hq1, hq2⟩ := hq
  have hv : valFloat .f32 (.bits 32 (BitVec.ofNat 64 b)) = .ok (P.scale) := by
    have := valFloat_b32 (b := b) (q := q) (by omega) hq1
    rw [hq2] at this
    simpa [b32] using this
  have hc : Clean (.bits 32 (scX L)) := ⟨rfl, fun _ _ _ => by simp, fun w x hx => by
    simp only [Value.bits.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    rw [hsx, BitVec.toNat_ofNat]
    omega⟩
  rw [hsx] at hc ⊢
  exact rd_of_valFloat hc hv

open Wg0 Wg0.Data in
/-- The lane's data machine is, at every event up to `k`, in a startup state or in warpgroup 0's
with the invariants of the trace so far. -/
def FollowW (P : Params) (L : Launch) (X : Execution) (g k : Nat) (sc : ℝ) : Prop :=
  ∀ j ≤ k, ∃ s, Frame.stateAt (threadD P L) X g j = some (some s) ∧
    ((∃ b, s.1 = .inl b) ∨ ∃ d, s.1 = .inr ⟨.inl .wg0, d⟩) ∧
    (∀ b, s.1 = .inl b → ∀ f ∈ (X.tr g).take j, f.pc < 103) ∧
    (∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → InvW ((X.tr g).take j) d ∧ OkInv d ∧
      CarryW sc ((X.tr g).take j) d ∧ VoteInv ((X.tr g).take j) d ∧ InvE ((X.tr g).take j) d ∧
      InvSk ((X.tr g).take j) d) ∧
    (∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → Wg0.PrevPc P L X g j d) ∧
    ∀ d, s.1 = .inr ⟨.inl .wg0, d⟩ → Wg0.Data.PcBound ((X.tr g).take j) d ∧
      Wg0.Data.PcSeen ((X.tr g).take j) d

open Wg0 Wg0.Data in
/-- **The thread machine is alive before event `k`** (at a state of any role). -/
def ThreadLive (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ)

open Wg0 Wg0.Data in
/-- **The data thread machine follows the lane** up to its event `k` from any live state of the
thread machine there (no role asked), with the invariants. -/
theorem followW_st (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : ThreadLive P L X g k) {sc : ℝ}
    (hx : Rd (.bits 32 (scX L)) (sc : EReal)) (hv : W0Valid sc ((X.tr g).take k)) :
    FollowW P L X g k sc := by
  intro j hj
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := Wg0.followW0 hp hX hFw hw he hσ hx hv j hj
  exact ⟨s, hs, Wg0.w0_slot hFw hw (Frame.lt_of_get hX he) hs, h1, h2, h3, h4⟩

open Wg0 Wg0.Data in
/-- **The data thread machine follows the lane** up to its event `k`, with the invariants. -/
theorem followW (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) {sc : ℝ}
    (hx : Rd (.bits 32 (scX L)) (sc : EReal)) (hv : W0Valid sc ((X.tr g).take k)) :
    FollowW P L X g k sc :=
  by
    intro j hj
    obtain ⟨σ, h, -⟩ := ev_at hp hX hFw he hub
    obtain ⟨s, hs, h1, h2, h3, h4⟩ := Wg0.followW0 hp hX hFw hw he ⟨σ, h⟩ hx hv j hj
    exact ⟨s, hs, Wg0.w0_slot hFw hw (Frame.lt_of_get hX he) hs, h1, h2, h3, h4⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
