-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Sim
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FinalStores
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.SafeSt
import Lemmas.Flow.Arith32Interval
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Lib.RowBias
import Lemmas.Flow.StoreAt
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Lemmas.Flow.Arith32WordW
import Lemmas.Flow.UbFree
import Lemmas.Flow.WordBound
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The address of a log-sum-exp store

A global store of a correction lane is its row's word of the log-sum-exp array, in the tile of its
CTA, for a row of its stage that the request has (`corr_lse`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

namespace Correction

private theorem lse_pred : allSites.all (fun s => (nexts s).all fun s' =>
    match s' with
    | .lse 0 => s == .fdone 1 1
    | .lse 1 => s == .fdone 1 1 || s == .lse 0
    | _ => true) = true := by decide +kernel

private theorem pass_site (late : Bool) (d : D) (h : Fin 2) :
    (passStart p L g late d).site ≠ .lse h := by
  intro hs
  unfold passStart D.ite at hs
  cases late <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs <;> split at hs <;>
    simp at hs

/-- The state before a log-sum-exp store has the store's scheduler state, and its row is one of the
request's. -/
theorem lse_prev {d d' : D} {e : Event} {h : Fin 2} (hev : Ev p L g d e)
    (hn : succ p L g d e = some (some d')) (hs : d'.site = .lse h) :
    d'.v.sc = d.v.sc ∧ d'.k = 0 ∧ scmp .ge .s (rowW L g)
      (if h = 0 then sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
        else addi (sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)) (-128)) =
      false ∧ (d.site = .lse 0 ∨ d.site = .fdone 1 1 ∧ (h ≠ 0 → scmp .ge .s (rowW L g)
        (sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)) = true)) := by
  obtain ⟨site, v, kk⟩ := d
  have hsite : site = .fdone 1 1 ∨ site = .lse 0 ∧ h = 1 := by
    rcases succ_cases hn with ⟨rfl, _, _, _, _, hk⟩ | ⟨hf, -, rfl⟩ | hM
    · exfalso
      simp only at hs
      subst hs
      simp only [Ev] at hev
      rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
      · rw [hk] at h; cases h
      · rw [hk] at h; cases h
    · exfalso
      simp only at hs
      rw [hs] at hf
      cases hf
    · have h1 := List.all_eq_true.mp (List.all_eq_true.mp lse_pred site
        (mem_allSites _)) d'.site hM.1
      rw [hs] at h1
      fin_cases h
      · left; simpa using h1
      · simp at h1
        rcases h1 with h1 | h1
        · exact .inl h1
        · exact .inr ⟨h1, rfl⟩
  rcases hsite with rfl | ⟨rfl, rfl⟩
  · simp only [succ] at hn
    split at hn
    swap
    · cases hn
    simp only [Option.some.injEq] at hn
    subst hn
    unfold afterFinal D.ite at hs ⊢
    simp only at hs ⊢
    split at hs
    · rename_i h1
      rw [ite_eq_left h1] at *
      split at hs
      · exfalso
        exact pass_site _ _ _ hs
      · rename_i h2
        rw [ite_eq_right h2]
        simp only [Site.lse.injEq] at hs
        subst hs
        exact ⟨rfl, rfl, by simpa using h2, .inr ⟨trivial, fun _ => h1⟩⟩
    · rename_i h1
      rw [ite_eq_right h1]
      simp only [Site.lse.injEq] at hs
      subst hs
      exact ⟨rfl, rfl, by simpa using h1, .inr ⟨trivial, fun h => absurd rfl h⟩⟩
  · simp only [succ] at hn
    split at hn
    swap
    · cases hn
    simp only [Option.some.injEq] at hn
    subst hn
    unfold afterLse D.ite at hs ⊢
    simp only at hs ⊢
    split at hs
    · exfalso
      exact pass_site _ _ _ hs
    · rename_i h2
      rw [ite_eq_right h2]
      exact ⟨rfl, rfl, by simpa using h2, .inl trivial⟩

/-- A row below a limit. -/
private theorem ge_row {a b : Nat} (ha : a < 2 ^ 31)
    (hb : b < 2 ^ 31) : scmp .ge .s (W a) (W b) = false ↔ a < b := by
  simp only [scmp, PTX.compare]
  rw [r32_W (by omega), r32_W (by omega), toSigned_W ha, toSigned_W hb]
  simp

/-- A row below a limit less 128. -/
private theorem ge_row128 {a b : Nat} (ha : a < 2 ^ 31)
    (hb : b < 2 ^ 31) : scmp .ge .s (W a) (addi (W b) (-128)) = false ↔ a + 128 < b := by
  have hn : (addi (W b) (-128)).toNat = (b + 4294967168) % 4294967296 := by
    have hi : (i32 (-128)).toNat = 4294967168 := by decide
    show (r32 (r32 (W b) + i32 (-128))).toNat = _
    rw [toNat_r32, BitVec.toNat_add, hi, r32_W (by omega), toNat_W (by omega)]
    omega
  have hr : r32 (addi (W b) (-128)) = addi (W b) (-128) := r32_of_lt (by omega)
  simp only [scmp, PTX.compare]
  rw [r32_W (by omega), toSigned_W ha, hr]
  have hs : toSigned 32 (addi (W b) (-128)) = (b : Int) - 128 := by
    simp only [toSigned, hn]
    split <;> omega
  rw [hs]
  simp only [decide_eq_false_iff_not, not_le, ge_iff_le]
  omega

/-- The words of the rows of a lane. -/
private theorem row_W (hp : Pre p L m) : rowW L g = W (g % L.block % 128) := by
  have hb : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  rw [rowW, tidW_eq hp]
  exact andi_W_low (k := 7) (by omega) (by decide)

private theorem or_row {t ρ : Nat} (hρ : ρ < 128) (ht : 256 * t < 2 ^ 64) :
    (W (256 * t) ||| W ρ) = W (256 * t + ρ) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, toNat_W ht, toNat_W (by omega)]
  have h1 : (256 * t) ||| ρ = 256 * t + ρ := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 8) (show ρ < 2 ^ 8 by omega) t
    rw [show 2 ^ 8 * t = 256 * t by norm_num] at this
    exact this.symm
  rw [h1]
  by_cases h : 256 * t + ρ < 2 ^ 64
  · rw [toNat_W h]
  · omega

/-- The log-sum-exp address in numbers. -/
private theorem lse_num {v : V} {h c0 t ρ : Nat} (hc : v.sc.c0 = W c0) (hc' : c0 < 2 ^ 31)
    (hh : (coords p L g v.sc).head = W h) (hh' : h < 2 ^ 31)
    (hr : shl (rowOff p L g v.sc) 8 = W (256 * t)) (ht : 256 * t < 2 ^ 31) (hρ : ρ < 128)
    (hw : rowW L g = W ρ) (hfit : p.lseBase + 4 * (h * p.lseStride + (c0 + 256 * t + ρ)) < 2 ^ 64) :
    (lseAddr p L g v).toNat = p.lseBase + 4 * (h * p.lseStride + (c0 + 256 * t + ρ)) := by
  have s1 : headW p L g v.sc = W h := by
    show sext (coords p L g v.sc).head = _
    rw [hh]; exact sext_W hh'
  have s2 : truncBits 64 (cvtIntBits false IType.s 64 IType.s 32 (truncBits 32 (W c0))) = W c0 :=
    sext_W hc'
  have s3 : truncBits 64 (cvtIntBits false IType.s 64 IType.s 32 (truncBits 32 (W (256 * t)))) =
      W (256 * t) := sext_W ht
  have s4 : truncBits 32 (W ρ) = W ρ := r32_W (by omega)
  have t64 : ∀ x : BitVec 64, truncBits 64 x = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_mod]
    exact Nat.mod_eq_of_lt x.isLt
  unfold lseAddr
  rw [s1, hc, hr, hw]
  simp only [s2, s3, s4, t64, show ¬ (2 ≥ 64) by decide, ↓reduceIte, or_row hρ (show 256 * t <
    2 ^ 64 by omega)]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, W,
    Nat.shiftLeft_eq]
  have e1 : h % 2 ^ 64 = h := by omega
  have e2 : c0 % 2 ^ 64 = c0 := by omega
  have e3 : (256 * t + ρ) % 2 ^ 64 = 256 * t + ρ := by omega
  rw [e1, e2, e3]
  have e4 : (h * (p.lseStride % 2 ^ 64)) % 2 ^ 64 = h * p.lseStride % 2 ^ 64 := by
    rw [Nat.mul_mod_mod]
  rw [e4]
  generalize h * p.lseStride = z at hfit ⊢
  omega

/-- A weak global store through a 64-bit register writes at the register's word and the offset. -/
private theorem stGlobal_at {A : List Assumption} {t : TState} {a : MemAccess} {base : Nat}
    {x : BitVec 64}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base 64) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hr : t.regs base = some (.bits 64 x)) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) {acc : Acc} {bs : List Byte}
    (he : e.kind = .wr acc bs) :
    acc.loc = (⟨.global, 0, (truncBits 64 x + BitVec.ofInt 64 a.addr.off).toNat⟩ : Loc).at
      (a.elem.width / 8 * t.sub) ∧ acc.size = a.elem.width / 8 := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem] at hf
  exact storeTmpl_wr (effAddr_global_bits hr) hf he

set_option maxHeartbeats 4000000 in
/-- **The footprint of a log-sum-exp store.** -/
private theorem lse_loc {d : Control.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (Control.code p L g).AtD d t) (hk0 : d.k = 0)
    (hc : kernel.code[(Control.code p L g).pc d]? = some ins)
    (hf : Fires ((Control.code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {hh : Fin 2} (hs : d.site = .lse hh) {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    acc.loc = ⟨.global, 0, (lseAddr p L g d.v.scheduler + W (512 * hh.val)).toNat⟩ ∧
      acc.size = 4 := by
  have hreg : ∀ r ∈ Control.live d, t.regs r = some (Control.valueOf p L g d r) :=
    fun r hr => by obtain ⟨-, -, -, -, hh⟩ := h; exact holds_mem hh (mem_factsFrom hr)
  have hsub : t.sub = 0 := by rw [h.2.1]; simp [hk0]
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have t64 : truncBits 64 (lseAddr p L g d.v.scheduler) = lseAddr p L g d.v.scheduler := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (BitVec.isLt _)
  obtain ⟨site, v, k⟩ := d
  simp only at hs
  subst hs
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    obtain ⟨h1, h2⟩ := stGlobal_at (x := lseAddr p L g v.scheduler) rfl rfl rfl rfl rfl
      (hreg _ (by lit_mem)) hf hk
    refine ⟨?_, h2⟩
    rw [h1, hsub, t64]
    rfl

theorem lse_or_final {d : Control.D} {a : Acc} {pc : Nat} {bs : List Byte}
    (hev : Control.Ev p L g d ⟨pc, .wr a bs⟩) :
    (∃ hh, d.site = .lse hh) ∨ ∃ st j hh, d.site = .fst st j hh := by
  have hev1 := hev.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h)
  cases hs : d.site <;>
    simp only [Correction.Ev, show d.scheduler.site = d.site from rfl, hs] at hev1
  case lse hh => exact .inl ⟨hh,rfl⟩
  case fst st j hh => exact .inr ⟨st,j,hh,rfl⟩
  all_goals exfalso
  all_goals try simp only [Epilogue.Ev, Correction.Site.toE, Correction.rdOrUb] at hev1
  all_goals first
      | contradiction
      | (rcases hev1 with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with h | ⟨_, h⟩ <;> cases h; done)
      | (rcases hev1 with h | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h; done)
      | (obtain ⟨_, _, _, h⟩ := hev1; cases h; done)
      | (obtain ⟨_, _, h⟩ := hev1; cases h; done)
      | (obtain ⟨_, h⟩ := hev1; cases h; done)

end Correction

/-- **The tile of a lane past its rounds**: the words of the CTA's work item. -/
theorem lse_tile (hp : Pre p L m) (hg : g < L.threads) {d : Correction.Control.D} {ns nv : Nat}
    (hF : CorrWarp.CFits p L g d ns nv) (hep : CorrWarp.epi d.site = .ready 0) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧
      d.v.sc.c0 = W (p.qOffset b) ∧
      (Correction.coords p L g d.v.sc).head =
        W (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧
      shl (Correction.rowOff p L g d.v.sc) 8 =
        W (256 * (Epilogue.assignedCoordinates p b (g / L.block)).1) ∧
      sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (Correction.rowOff p L g d.v.sc) 8) =
        W (p.qLength b - 256 * (Epilogue.assignedCoordinates p b (g / L.block)).1) := by
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  simp only [Epilogue.Fits, CorrWarp.toE, show d.scheduler.site = d.site from rfl, hep] at hFE
  obtain ⟨R, bal, hC, hc0, hc1⟩ := hFE
  obtain ⟨b, hb, hlo, hhi, hch, hco⟩ := Epilogue.chosen_spec hp hg hC
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  set tt := (Epilogue.assignedCoordinates p b (g / L.block)).1 with htt
  set hd := (Epilogue.assignedCoordinates p b (g / L.block)).2 with hhd
  have hl := (hp.lengths b hb).1
  have hbb : b < 2 ^ 31 := by have := hp.shape.2.1; omega
  have hq1 := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
  obtain ⟨-, -, -, -, -, htq⟩ := hp.shape
  have hql : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
  have hc0' : d.v.sc.c0 = W (p.qOffset b) := by
    refine hc0.trans ?_
    rw [hch, Epilogue.qv_W hp (by omega)]
  have hc1' : d.v.sc.c1 = W (p.qOffset (b + 1)) := by
    refine hc1.trans ?_
    rw [hch, show (1 : Int) = ((1 : Nat) : Int) from rfl, addi_W (by decide) (by omega),
      Epilogue.qv_W hp (by omega)]
  have hce := CorrWarp.coords_eq (Correction.ctaR_eq hp hg) d.v.sc
  have hhead : (Correction.coords p L g d.v.sc).head = W hd := by
    rw [hce]
    exact congrArg Epilogue.Coords.head hco
  have hrow : shl (Correction.rowOff p L g d.v.sc) 8 = W (256 * tt) := by
    have h1 := congrArg Epilogue.Coords.row hco
    dsimp only at h1
    refine row_unbias (shl8_lt _) (by omega) ?_
    rw [← h1]
    show (Correction.coords p L g d.v.sc).row = _
    rw [hce]
    rfl
  have hρ : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hrw := Correction.row_W (L := L) (g := g) hp
  have hlim : sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (Correction.rowOff p L g d.v.sc) 8) =
      W (p.qLength b - 256 * tt) := by
    rw [hc0', hc1', hrow, sub32_W hl (by omega), ← hql, sub32_W (by omega) (by omega)]
  exact ⟨b, hb, hlo, hhi, hc0', hhead, hrow, hlim⟩

/-- **A stage's row guard**: the request has the lane's row of the stage. -/
theorem lse_guard (hp : Pre p L m) {b tt : Nat} (hb : b < p.batch) (hh : Fin 2) {lim : BitVec 64}
    (hlim : lim = W (p.qLength b - 256 * tt)) :
    scmp .ge .s (Correction.rowW L g) (if hh = 0 then lim else addi lim (-128)) = false ↔
      256 * tt + 128 * hh.val + g % L.block % 128 < p.qLength b := by
  have hl := (hp.lengths b hb).1
  have hρ : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hq1 := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
  obtain ⟨-, -, -, -, -, htq⟩ := hp.shape
  have hql : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
  have hlt : p.qLength b - 256 * tt < 2 ^ 30 := by omega
  rw [hlim, Correction.row_W (L := L) (g := g) hp]
  have h2 : hh.val < 2 := hh.isLt
  by_cases h0 : hh = 0
  · rw [ite_eq_left h0, Correction.ge_row (by omega) (by omega)]
    subst h0
    simp only [Fin.isValue, Fin.val_zero]
    omega
  · rw [ite_eq_right h0, Correction.ge_row128 (by omega) (by omega)]
    have : hh.val = 1 := by
      have : hh.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    omega

/-- **The address of the log-sum-exp store of a stage's site.** -/
theorem corr_lse_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    {d : Correction.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (h0 : n .ub = 0) (hF : CorrWarp.CFits p L g d (n .shfl) (n .vote)) {hh : Fin 2}
    (hs : d.site = .lse hh) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧
        256 * (Epilogue.assignedCoordinates p b (g / L.block)).1 + 128 * hh.val +
          g % L.block % 128 < p.qLength b ∧
        a.loc = p.lseLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b
          (g / L.block)).1 + 128 * hh.val + g % L.block % 128))
            (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧ a.size = 4 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  obtain ⟨i, d0, n0, e0, rfl, he0, hσ0, hub0, hn0, hev0, hube0⟩ := corr_prev hp hX hFw hw hw1 hσ h0
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1.le (by rw [hs]; simp)
  obtain ⟨a0,ev,hev,_,hn,ha,hv,hk,_⟩ := hn0
  obtain ⟨hsc0, hk0, hguard, -⟩ :=
    Correction.lse_prev (d := d0.scheduler) (d' := a0) hev hn (ha.trans hs)
  have hsc : d.v.sc = d0.v.sc := (congrArg Correction.Control.V.sc hv).symm.trans hsc0
  have hk0 : d.k = 0 := hk.symm.trans hk0
  change _ = false at hguard
  obtain ⟨hal, hsz⟩ := Correction.lse_loc (d := d) hat hk0 hc hf hs rfl
  obtain ⟨b, hb, hlo, hhi, hc0', hhead, hrow, hlim⟩ :=
    lse_tile hp hg hF (by rw [hs]; rfl)
  obtain ⟨hv1, hv2⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  set tt := (Epilogue.assignedCoordinates p b (g / L.block)).1 with htt
  set hd := (Epilogue.assignedCoordinates p b (g / L.block)).2 with hhd
  have hl := (hp.lengths b hb).1
  have hq1 := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
  obtain ⟨-, -, -, -, -, htq⟩ := hp.shape
  have hql : p.qLength b = p.qOffset (b + 1) - p.qOffset b := rfl
  have hρ : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
  have hrw := Correction.row_W (L := L) (g := g) hp
  simp only [Correction.Control.D.scheduler, Correction.Control.V.scheduler] at hguard
  rw [← hsc] at hguard
  have hvalid := (lse_guard hp hb hh hlim).mp hguard
  have hrange := hp.ranges p.lseRegion (by simp)
  have hin := lseByte_in (p := p) (q := p.qOffset b + (256 * tt + 128 * hh.val + g % L.block % 128))
    (h := hd) (k := 3) (by omega) hv2 (by decide)
  obtain ⟨-, -, -, hin2⟩ := id hin
  simp only [Params.lseLoc, globalLoc, Loc.at] at hin2
  have hN := Correction.lse_num (v := d.v.scheduler) (t := tt) hc0' (by omega) hhead
    (by have := Epilogue.heads_small hp; omega) hrow (by omega) hρ hrw (by
      generalize hd * p.lseStride = z at hin2 ⊢
      omega)
  refine ⟨b, hb, hlo, hhi, hvalid, ?_, hsz⟩
  rw [hal]
  simp only [Params.lseLoc, globalLoc, Loc.mk.injEq, true_and, BitVec.toNat_add, hN]
  rw [toNat_W (by have := hh.isLt; omega)]
  generalize hd * p.lseStride = z at hin2 ⊢
  have := hh.isLt
  omega

/-- **The address of a log-sum-exp store.** -/
theorem corr_lse (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hgl : a.loc.space = .global) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧ ∃ st : Fin 2,
        256 * (Epilogue.assignedCoordinates p b (g / L.block)).1 + 128 * st.val +
          g % L.block % 128 < p.qLength b ∧
        a.loc = p.lseLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b
          (g / L.block)).1 + 128 * st.val + g % L.block % 128))
            (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧ a.size = 4 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev1, hevR⟩
  · exact (start_mem hev hi.2 trivial).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hF : CorrWarp.CFits p L g d (n .shfl) (n .vote) := (hR h0).2
  obtain ⟨hh, hs⟩ : ∃ hh, d.site = .lse hh := by
    rcases Correction.lse_or_final hev1 with hs | ⟨st,j,hh,hs⟩
    · exact hs
    · obtain ⟨-, q, -, w, -, hloc⟩ := Correction.fst_at hp hat hc hf hs rfl
      rw [hloc] at hgl
      cases hgl
  obtain ⟨b, hb, hlo, hhi, h⟩ := corr_lse_at hp hX hFw hw hw1 he hσ h0 hF hs
  exact ⟨b, hb, hlo, hhi, hh, h⟩

/-- The event of a store site of a correction lane is a global write. -/
theorem lse_wr {e : Event}
    (hub : ∀ f, e.kind ≠ .ub f) {d : Correction.Control.D}
    (hev : Correction.Control.Ev p L g d e) {hh : Fin 2} (hs : d.site = .lse hh) :
    ∃ pc a bs, e = ⟨pc, .wr a bs⟩ := by
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  have hev1 : (∃ a bs, e.kind = .wr a bs) ∨ ∃ f, e.kind = .ub f := hev
  obtain ⟨pc, kind⟩ := e
  rcases hev1 with ⟨a, bs, rfl⟩ | ⟨f, rfl⟩
  · exact ⟨pc, a, bs, rfl⟩
  · exact (hub f rfl).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof
