-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrLocal
import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.PageWord
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every loader state has its address words (`addr_ok`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

theorem word32_inv {x : Value} {f : BitVec 64 → D} {d' : D}
    (h : word32 x f = some (some d')) : ∃ y, x = .bits 32 y ∧ d' = f y := by
  unfold word32 at h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨_, rfl, h.symm⟩
  · simp at h

theorem rebuild_lt {bs : List (Option Byte)} {x y : BitVec 64}
    (hl : bs.length = 4) (hb : ∀ i < 4, bs[i]? = some ((Value.bits 32 y).toBytes[0 + i]?))
    (hy : y.toNat < 2 ^ 32) (hx : rebuild 3 bs = .ok (.bits 32 x)) : x.toNat = y.toNat := by
  have := rebuild_part (.inl ⟨rfl, rfl, hy⟩) hl hb hx
  omega

theorem addr_init (hp : Pre p L m) (k : Nat) (b : Bool) :
    AddrOk p L X g k (Loader.F p L g b).init := by
  have h0 : 0 < p.pages := by have := hp.shape; omega
  have z1 : (0 : BitVec 64).toNat < 2 ^ 31 := by decide
  have z2 : (0 : BitVec 64).toNat < 16 := by decide
  refine ⟨⟨h0, z1⟩, ⟨h0, z1⟩, z2, fun h => by simp [Site.blk, bc] at h,
    fun _ _ _ h => by simp at h, fun h => by simp [isRow] at h⟩

/-- The location of a packet's address load. -/
theorem lw_loc (hp : Pre p L m) {per : Per} {v : Bool} {h : Fin 2} {vv : V} {kk : Fin 2}
    {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hev : Ev p L g w ⟨.lw per v h, vv, kk⟩ ⟨pc, .rd a bs⟩) :
    a.loc = ⟨.local, g, L.localBase + lwO per v h + 4 * kk.val⟩ ∧ a.size = 4 := by
  simp only [Ev] at hev
  obtain ⟨bs', hk'⟩ := hev
  simp only [Kind.rd.injEq] at hk'
  obtain ⟨rfl, -⟩ := hk'
  have hx' : rv p L g w ⟨.lw per v h, vv, kk⟩ (lwBase (pk per v)) =
      BitVec.ofNat 64 (L.localBase + (if per ≠ .prime ∧ v = false then 32 else 0)) := by
    cases per <;> cases v <;> rfl
  have hlb := hp.localMemory.2.1
  refine ⟨?_, rfl⟩
  rw [hx']
  cases per <;> cases v <;> fin_cases h <;> fin_cases kk <;>
    simp [lwO, lacc, Loc.at, lwOff, wrapAddr, truncBits, BitVec.toNat_add, BitVec.toNat_ofInt] <;>
    omega

theorem lwO_mem (per : Per) (v : Bool) (h : Fin 2) :
    (lwO per v h = 0 ∨ lwO per v h = 8 ∨ lwO per v h = 32 ∨ lwO per v h = 40) ∧
      lwO per v h ∈ lstOffs := by
  cases per <;> cases v <;> fin_cases h <;> simp [lwO, lstOffs]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

/-- **A packet's address load** reads a half of the row address the lane stored last. -/
theorem lw_half {k : Nat} {b : Bool} {n : Cls → Nat} {a : Acc} {bs : List (Option Byte)} {pc : Nat}
    {per : Per} {v : Bool} {h : Fin 2} {vv : V} {kk : Fin 2}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hσ : Frame.stateAt (thread p L) X g k =
      some (some (linj p L g b ⟨.lw per v h, vv, kk⟩ n)))
    (hJ : Loader.Ref p L g (wOf b) (⟨.lw per v h, vv, kk⟩, lcn n))
    (hev : Ev p L g (wOf b) ⟨.lw per v h, vv, kk⟩ ⟨pc, .rd a bs⟩)
    (IH : ∀ j ≤ k, ∀ b d n,
      Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) → n .ub = 0 →
      AddrOk p L X g j d) {x : BitVec 64} (hx : rebuild 3 bs = .ok (.bits 32 x)) :
    ∃ j a' y, RowA p y ∧ LastAt L X g k (lwO per v h) j a' (Value.bits 64 y).toBytes ∧
      x.toNat = y.toNat / 256 ^ (4 * kk.val) % 2 ^ 32 := by
  obtain ⟨hl, hz⟩ := lw_loc hp hev
  obtain ⟨ho, hm⟩ := lwO_mem per v h
  have hkk : 4 * kk.val = 0 ∨ 4 * kk.val = 4 := by omega
  obtain ⟨j, a', bs', hL, ⟨o, hlo, hS⟩, hlen, hb⟩ := load_at hp hX hg hw he hσ hJ IH hl hz
    (hkk.imp id fun h => ⟨h, ho⟩) hm (fun kk A => lst_lw per v h kk A)
  have hl' := hL.2.2.1
  rw [hl'] at hlo
  simp only [Loc.mk.injEq, true_and] at hlo
  rcases hS with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, y, hy, rfl⟩
  · omega
  · omega
  · exact ⟨j, a', y, hy, hL, rebuild_part (.inr ⟨rfl, hkk⟩) hlen hb hx⟩

set_option maxHeartbeats 4000000 in
/-- **Every loader state has its address words.** -/
theorem addr_ok : ∀ k, k ≤ (X.tr g).length → ∀ b d n,
    Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
    AddrOk p L X g k d := by
  refine pos_at (I := fun k d => AddrOk p L X g k d) (fun k b => addr_init hp k b)
    (fun k b d n e d' he hσ hub hJ hF hev hnu hn hm IH => ?_) hp hX hg hw
  have hA := IH k le_rfl b d n hσ hub
  have hsame : ∀ f, wr d.site f = false → f.same d.v d'.v := hm.keep
  obtain ⟨pc, kind⟩ := e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the page word
    by_cases hs : ∃ per it, d.site = .pgLd per it
    · obtain ⟨per, it, hs⟩ := hs
      have hpg := pg_page hp hX he hσ hF hs
      obtain ⟨s, v, kk⟩ := d
      simp only at hs
      subst hs
      simp only [succ] at hn
      cases kind <;> simp only [reduceCtorEq] at hn
      split at hn
      · rename_i a bs x hx
        obtain ⟨y, rfl, rfl⟩ := word32_inv hn
        exact hpg _ _ y rfl hx
      · simp at hn
    · push Not at hs
      rcases succ_pw hs hn with h | h
      · rw [h]; exact hA.pw
      · rw [h]
        have h0 : 0 < p.pages := by have := hp.shape; omega
        exact ⟨h0, by decide⟩
  · by_cases hs : ∃ per v it, d.site = .ptP per v it
    · obtain ⟨per, v, it, hs⟩ := hs
      obtain ⟨s, vv, kk⟩ := d
      simp only at hs
      subst hs
      obtain ⟨a, bs, hk, hl, hz⟩ := ptP_loc hp hev
      simp only at hk
      subst hk
      obtain ⟨j, a', bs', hL, ⟨o, ho, hS⟩, hlen, hb⟩ := load_at hp hX hg hw he hσ hJ IH
        (o := 96 + 4 * it.val) (q := 0) (by rw [hl]; rfl) hz (.inl rfl)
        (by fin_cases it <;> simp [lstOffs]) (fun kk A => lst_ptP per v it kk A)
      obtain ⟨-, -, hl', -⟩ := hL
      rw [hl'] at ho
      simp only [Loc.mk.injEq, true_and] at ho
      have hit := it.isLt
      rcases hS with ⟨-, -, x, hpg, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · simp only [succ] at hn
        split at hn
        · rename_i z hx
          obtain ⟨y, rfl, rfl⟩ := word32_inv hn
          have := rebuild_lt hlen hb (by have := hpg.2; omega) hx
          exact ⟨by rw [this]; exact hpg.1, by rw [this]; exact hpg.2⟩
        · simp at hn
      · omega
      · omega
    · have h : d'.v.lp = d.v.lp := hsame .lp (by
        revert hs; cases d.site <;> simp [wr])
      rw [h]; exact hA.lp
  · by_cases hs : ∃ per v it, d.site = .ptR per v it
    · obtain ⟨per, v, it, hs⟩ := hs
      obtain ⟨s, vv, kk⟩ := d
      simp only at hs
      subst hs
      obtain ⟨a, bs, hk, hl, hz⟩ := ptR_loc hp hev
      simp only at hk
      subst hk
      obtain ⟨j, a', bs', hL, ⟨o, ho, hS⟩, hlen, hb⟩ := load_at hp hX hg hw he hσ hJ IH
        (o := 64 + 4 * it.val) (q := 0) (by rw [hl]; rfl) hz (.inl rfl)
        (by fin_cases it <;> simp [lstOffs]) (fun kk A => lst_ptR per v it kk A)
      obtain ⟨-, -, hl', -⟩ := hL
      rw [hl'] at ho
      simp only [Loc.mk.injEq, true_and] at ho
      have hit := it.isLt
      rcases hS with ⟨h, -⟩ | ⟨-, -, x, hr, rfl⟩ | ⟨h, -⟩
      · omega
      · simp only [succ] at hn
        split at hn
        · rename_i z hx
          obtain ⟨y, rfl, rfl⟩ := word32_inv hn
          have := rebuild_lt hlen hb (by unfold RowV at hr; omega) hx
          show y.toNat < 16
          rw [this]; exact hr
        · simp at hn
      · omega
    · have h : d'.v.lr = d.v.lr := hsame .lr (by
        revert hs; cases d.site <;> simp [wr])
      rw [h]; exact hA.lr
  · -- the head bases
    intro hb'
    by_cases hs : d.site = .uk
    · obtain ⟨s, v, kk⟩ := d
      simp only at hs
      subst hs
      obtain ⟨-, hFE, hco⟩ : n (.load .commit) = 0 ∧ Epilogue.Fits p L g (toE ⟨.uk, v, kk⟩)
          (n .shfl) (n .vote) ∧ v.co = coords p L g v.sc := hF
      simp only [Epilogue.Fits, toE, Site.epi] at hFE
      obtain ⟨R, bal, hC, -⟩ := hFE
      obtain ⟨h, hh, hhd⟩ := head_chosen (d := ⟨.uk, v, kk⟩) hp hg hC
      simp only [succ] at hn
      cases kind <;> simp only [reduceCtorEq] at hn
      split at hn
      · rename_i a bs x hx
        obtain ⟨y, rfl, rfl⟩ := word32_inv hn
        refine head_setup hp (g := g) (v := { v with ukw := y }) hh (by rw [← hhd, ← hco]) ?_
        unfold pgEnter D.iteS
        dsimp only
        split <;> rfl
      · simp at hn
    · have hb : d.site.blk = true := by
        rcases hm.edge with h | h
        · exact h ▸ hb'
        · have := blk_edges.ok h
          simp only [blkChk, hb', hs, Bool.not_true, Bool.false_or, decide_false,
            Bool.or_false] at this
          exact this
      have hsu : d'.v.su = d.v.su := hsame .su (by
        revert hb hs; cases d.site <;> simp [wr, Site.blk, bc])
      obtain ⟨h, hh, h1, h2⟩ := hA.head hb
      exact ⟨h, hh, by rw [hsu]; exact h1, by rw [hsu]; exact h2⟩
  · -- between the two words
    intro per v hh hs' hk1
    obtain ⟨s, vv, kk⟩ := d
    have hlw : s = .lw per v hh := by
      rcases hm.edge with h | h
      · exact h.symm.trans hs'
      · have hc := lw_edges.ok h
        simp only [lwChk, hs'] at hc
        exfalso
        cases s <;> simp only [Bool.false_eq_true] at hc
        · rename_i it
          simp only [succ] at hn
          split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
          · simp at hk1
          · unfold pkStart at hk1; split at hk1
            · simp at hk1
            · split at hk1 <;> simp at hk1
        · simp only [succ] at hn
          repeat' split at hn
          all_goals simp only [Option.some.injEq] at hn
          all_goals subst hn
          all_goals simp at hk1
    subst hlw
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨bs, hk⟩ := hev0
    simp only [succ] at hn
    subst hk
    simp only at hn
    split at hn
    · rename_i z hx
      obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      have hk0 : kk = 0 := by
        by_contra hne
        have : kk.val ≠ 0 := fun h => hne (Fin.ext h)
        rw [ite_eq_right this] at hs'
        simp at hs'
      subst hk0
      simp only [Fin.val_zero, ↓reduceIte] at hs' ⊢
      obtain ⟨j, a', z, hz, hL, hxz⟩ := lw_half hp hX hg hw he hσ hJ hev IH hx
      refine ⟨j, a', z, hz, hL.mono ?_, ?_⟩
      · rintro a2 bs2 ⟨pc2, h2⟩
        rw [show X.get (g, k) = _ from he] at h2
        cases h2
      · simpa using hxz
    · simp at hn
  · -- in a packet's rows
    intro hr'
    by_cases hr : isRow d.site = true
    · obtain ⟨y, hy, h0, h1⟩ := hA.row hr
      have e0 : d'.v.l0 = d.v.l0 := hsame .l0 (by
        revert hr; cases d.site <;> simp [wr, isRow])
      have e1 : d'.v.l1 = d.v.l1 := hsame .l1 (by
        revert hr; cases d.site <;> simp [wr, isRow])
      exact ⟨y, hy, by rw [e0]; exact h0, by rw [e1]; exact h1⟩
    obtain ⟨s, vv, kk⟩ := d
    simp only [Bool.not_eq_true] at hr
    obtain ⟨per, v, hh, rfl⟩ : ∃ per v hh, s = .lw per v hh := by
      rcases hm.edge with h | h
      · rw [h, hr] at hr'; cases hr'
      · have hc := row_edges.ok h
        simp only [rowChk, hr', hr, Bool.not_true, Bool.false_or] at hc
        cases s <;> simp only [Bool.false_eq_true] at hc
        exact ⟨_, _, _, rfl⟩
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨bs, hk⟩ := hev0
    simp only [succ] at hn
    subst hk
    simp only at hn
    split at hn
    · rename_i z hx
      obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      have hk1 : kk = 1 := by
        by_contra hne
        have : kk.val = 0 := by
          have := kk.isLt
          have : kk.val ≠ 1 := fun h => hne (Fin.ext h)
          omega
        rw [ite_eq_left this] at hr'
        simp [isRow] at hr'
      subst hk1
      obtain ⟨j, a', z, hz, hL, hxz⟩ := lw_half hp hX hg hw he hσ hJ hev IH hx
      obtain ⟨j2, a2, z2, hz2, hL2, hl0⟩ := hA.mid per v hh rfl rfl
      obtain ⟨-, hbs⟩ := hL.unique hL2
      refine ⟨z2, hz2, hl0, ?_⟩
      show y.toNat = _
      rw [hxz]
      have : z = z2 := by
        have := congrArg List.head? hbs
        simpa [Value.toBytes, Value.bytes, Value.byteAt, List.range_succ_eq_map] using this
      subst this
      simp only [Fin.val_one]
      norm_num
      omega
    · simp at hn

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
