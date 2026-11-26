-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.TcOrd
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # The collective events and votes of a lane of warps 0–3, by state

Along the trace of a lane of warps 0–3 (`w0_tc`, by induction): at a startup state its
collectives are its paired Tensor Memory operations (`Startup.ev_tc`); at a warpgroup-0 state
they are `tcBase` (warp 0's allocation and relinquishment) plus `Wg0.tcOrd` with the arms of the
lane's blocks (`armH`, from the results of its votes, `voteRes`), its votes are `Wg0.vOrd`, past
a block's vote the vote word is that vote's result, and in an arm the arm runs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- The collectives of lane `y`'s prefix `i`. -/
def tcCnt (X : Execution) (y i : Nat) : Nat := ((X.tr y).take i).countP isTcColl

/-- The full-mask votes of lane `y`'s prefix `i`. -/
def vCnt (X : Execution) (y i : Nat) : Nat := ((X.tr y).take i).countP (voteWith (2 ^ 32 - 1))

/-- The result of lane `y`'s `n`-th full-mask vote (`false` if it has none). -/
def voteRes (X : Execution) (y n : Nat) : Bool :=
  ((((X.tr y).filter (voteWith (2 ^ 32 - 1)))[n]?).map Wg0.vres).getD false

/-- The arms of lane `y`'s blocks below `r`: the blocks but the first whose vote is true. -/
def armH (X : Execution) (y r : Nat) : Nat :=
  ((List.range r).filter fun r' => r' != 0 && voteRes X y r').length

/-- Warp 0's allocation and relinquishment. -/
def tcBase (L : Launch) (y : Nat) : Nat := if scmpi .ne .b (warpW L y) 0 then 0 else 2

theorem armH_succ (r : Nat) :
    armH X y (r + 1) = armH X y r + if r ≠ 0 ∧ voteRes X y r = true then 1 else 0 := by
  simp only [armH, List.range_succ, List.filter_append, List.length_append]
  by_cases h : r ≠ 0 ∧ voteRes X y r = true <;> simp_all

/-- The vote at position `i` with `n` earlier ones is the `n`-th. -/
theorem voteRes_of {i n : Nat} {e : Event} (he : (X.tr y)[i]? = some e)
    (hv : voteWith (2 ^ 32 - 1) e = true) (hc : vCnt X y i = n) :
    voteRes X y n = Wg0.vres e := by
  have hi : i < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
  have hsplit : X.tr y = (X.tr y).take i ++ e :: (X.tr y).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (X.tr y)]
    rw [List.drop_eq_getElem_cons hi, (List.getElem?_eq_some_iff.mp he).2]
  have hl : (((X.tr y).take i).filter (voteWith (2 ^ 32 - 1))).length = n := by
    rw [← List.countP_eq_length_filter]; exact hc
  unfold voteRes
  rw [hsplit, List.filter_append, List.filter_cons_of_pos hv, List.getElem?_append_right
    (by omega), hl, Nat.sub_self]
  rfl

/-- **The facts at a state** of a lane of warps 0–3 at prefix `i`. -/
def W0Tc (P : Params) (L : Launch) (X : Execution) (y i : Nat) : (thread P L y).D → Prop
  | (.inl _, _) => tcCnt X y i = ((X.tr y).take i).countP Tmem.Pair.isTmemOp ∧ vCnt X y i = 0
  | (.inr ⟨.inl .wg0, d⟩, _) =>
      tcCnt X y i = tcBase L y + Wg0.tcOrd (warpW L y) d (armH X y) ∧ vCnt X y i = Wg0.vOrd d ∧
        Wg0.VtOk d (voteRes X y) ∧ Wg0.ArmOk d
  | _ => True

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The facts hold at every state** of a lane of warps 0–3 whose events before `i` are no
undefined behaviour. -/
theorem w0_tc (hw : warp L y < 4) (hy : y < L.threads) :
    ∀ i, LaneUbFree X y i → ∀ σ, Frame.stateAt (thread P L) X y i = some (some σ) →
      W0Tc P L X y i σ := by
  intro i
  induction i with
  | zero =>
    intro hal σ hσ
    rcases w0_bst_pre hFw hal hw hy hσ with ⟨d, n, rfl, -⟩ | ⟨d, n, rfl, -⟩
    · simp [W0Tc, tcCnt, vCnt]
    · exfalso
      rw [Frame.stateAt_zero] at hσ
      simp [thread, Code.roleThread, Code.counted, Code.glue, Code.enter, Code.gatedExit,
        startupEnter, startupCode, Startup.code, Startup.exitOf] at hσ
  | succ i ih =>
    intro hal σ' hσ'
    rcases hk : (X.tr y)[i]? with _ | e
    · have hl : (X.tr y).length ≤ i := List.getElem?_eq_none_iff.mp hk
      have h1 : (X.tr y).take (i + 1) = (X.tr y).take i := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at hσ'
      have := ih (hal.mono (Nat.le_succ i)) σ' hσ'
      obtain ⟨s, n⟩ := σ'
      rcases s with d | ⟨i' | r, d⟩
      · simpa [W0Tc, tcCnt, vCnt, h1] using this
      · cases i' with
        | wg0 => simpa [W0Tc, tcCnt, vCnt, h1] using this
        | _ => trivial
      · trivial
    have hget : X.get (y, i) = some e := hk
    have hub := NoUbBefore.ne hal (Nat.lt_succ_self i) hget
    have hT : ∀ c : Event → Bool, ((X.tr y).take (i + 1)).countP c =
        ((X.tr y).take i).countP c + if c e then 1 else 0 := fun c => by
      rw [List.take_add_one, hk, Option.toList_some, List.countP_append]
      simp [List.countP_singleton]
    obtain ⟨σ, hσ, hn⟩ := prev_state hk hσ'
    obtain ⟨σ0, hσ0, -, -, hev, -⟩ := ev_at hp hX hFw hget hub
    rw [hσ] at hσ0
    cases hσ0
    have hal' := hal.mono (Nat.le_succ i)
    have IH := ih hal' σ hσ
    rcases w0_bst_pre hFw hal' hw hy hσ with ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -⟩
    · -- a startup state
      have hev' : Startup.Ev L y d e := hev
      have hx : ∀ r, d.site ≠ .enter r := fun r h => by simp [Startup.exitOf, h] at hxd
      obtain ⟨htc, hvt⟩ := Startup.ev_tc hx hev'
      obtain ⟨h1, h2⟩ := IH
      have hc1 : tcCnt X y (i + 1) = ((X.tr y).take (i + 1)).countP Tmem.Pair.isTmemOp := by
        simp only [tcCnt, hT, htc] at h1 ⊢; omega
      have hc2 : vCnt X y (i + 1) = 0 := by simp only [vCnt, hT, hvt] at h2 ⊢; simpa using h2
      rw [next_startup] at hn
      obtain ⟨d', -, hq⟩ := map_some hn
      subst hq
      unfold Code.enter
      split
      · next ent hent =>
        rcases w0_bst_pre hFw hal hw hy hσ' with ⟨d2, n2, h2', -⟩ | ⟨d2, n2, h2', -⟩
        · simp only [Code.enter, hent, Prod.mk.injEq, reduceCtorEq, false_and] at h2'
        · simp only [Code.enter, hent, Prod.mk.injEq] at h2'
          obtain ⟨h3, -⟩ := h2'
          simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h3
          obtain ⟨rfl, -⟩ := h3
          simp only [Code.enter, hent] at hσ'
          have hJ : fragJ P L y .wg0 _ _ := (follow_iff.mp hFw y hy (i + 1)).2 _ hσ'
          obtain ⟨-, ⟨-, hTm⟩, -, -⟩ := hJ
          have hu : Code.bump cls n e .ub = 0 := (state_count hσ' .ub).trans
            (w0_noUbTakeW_pre
              (fun f h => by obtain ⟨pc, kd⟩ := f; cases kd <;> simp [cls] at h ⊢) hal)
          have ht := hTm hu
          have hc := state_count hσ' .tmem
          simp only at hc
          rw [hc] at ht
          simp only [Wg0.TmemAt, cls] at ht
          refine ⟨?_, ?_, ?_, ?_⟩
          · show tcCnt X y (i + 1) = tcBase L y + Wg0.tcOrd (warpW L y) { site := .smr } _
            rw [hc1]
            simpa [tcBase, Wg0.tcOrd, Wg0.Site.reg] using ht
          · show vCnt X y (i + 1) = Wg0.vOrd { site := .smr }
            simpa [Wg0.vOrd, Wg0.Site.reg] using hc2
          · show Wg0.VtOk { site := .smr } _
            simp [Wg0.VtOk, Wg0.Site.reg]
          · show Wg0.ArmOk { site := .smr }
            simp [Wg0.ArmOk, Wg0.Site.isArm]
      · exact ⟨hc1, hc2⟩
    · -- a warpgroup-0 state
      obtain ⟨h1, h2, hV, hA⟩ := IH
      have hev' : Wg0.Ev P L y (warpW L y) d e := hev
      obtain ⟨-, hK⟩ := hev'
      have htc := Wg0.evK_tc hub hK
      have hvt := Wg0.evK_vote hub hK
      rw [next_frag] at hn
      obtain ⟨d', hs, rfl⟩ := map_some hn
      have hs' : Wg0.Control.succ P L y (warpW L y) d e = some (some d') := hs
      have hc1 : tcCnt X y (i + 1) = tcCnt X y i + if d.site.isTc then 1 else 0 := by
        simp only [tcCnt, hT, htc]
      have hc2 : vCnt X y (i + 1) = vCnt X y i + if d.site = .vote then 1 else 0 := by
        simp only [vCnt, hT, hvt]; split_ifs <;> simp_all
      show tcCnt X y (i + 1) = tcBase L y + Wg0.tcOrd (warpW L y) d' (armH X y) ∧
        vCnt X y (i + 1) = Wg0.vOrd d' ∧ Wg0.VtOk d' (voteRes X y) ∧ Wg0.ArmOk d'
      by_cases has : d.site = .arrS
      · have hC' := hC
        simp only [Wg0.RefCore, has, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hC'
        obtain ⟨r, ⟨-, hR, hrR, hbi, -⟩, -⟩ := hC'
        simp only [Wg0.Control.D.words] at hbi hR hrR
        have hr1 : d.bi.toNat = r + 1 := by rw [hbi]; exact toNat_W (by omega)
        have hvt' : d.vt = voteRes X y r := by
          have := hV (by rw [has]; rfl) (by rw [has]; decide)
          rwa [hr1, Nat.add_sub_cancel] at this
        have hav : Wg0.armV d = (r != 0 && voteRes X y r) := by
          simp only [Wg0.armV, hbi, scmpi_eq_b_W (n := 1) (show r + 1 < 2 ^ 32 by omega)
            (by omega) (by omega), hvt']
          cases voteRes X y r <;> by_cases h0 : r = 0 <;> simp [h0]
        have hH : armH X y (d.bi.toNat - 1 + 1) = armH X y (d.bi.toNat - 1) +
            if (r != 0 && voteRes X y r) then 1 else 0 := by
          rw [hr1, Nat.add_sub_cancel, armH_succ]
          cases voteRes X y r <;> by_cases h0 : r = 0 <;> simp [h0]
        obtain ⟨ht, hv, hVt, hA'⟩ := Wg0.arrS_tc has hC hs' hav hH
        simp only [has, Wg0.Site.isTc, reduceCtorEq, ite_false, Nat.add_zero] at hc1 hc2
        exact ⟨by rw [hc1, h1, ht], by rw [hc2, h2, hv], hVt _, hA'⟩
      · obtain ⟨ht, hv, hVt, hvote, hA'⟩ :=
          Wg0.succ_tc (batch_in hp y) has hs' hA (H := armH X y) rfl (voteRes X y)
        refine ⟨by rw [hc1, h1, ht]; omega, by rw [hc2, h2, hv], ?_, hA'⟩
        by_cases hvs : d.site = .vote
        · obtain ⟨h3, h4, h5⟩ := hvote hvs
          intro _ _
          rw [h3, h4]
          have hc : vCnt X y i = d.bi.toNat - 1 := by
            rw [h2]; simp [Wg0.vOrd, hvs, Wg0.Site.reg, Wg0.Site.ord]
          exact (voteRes_of hk (by rw [hvt]; simp [hvs]) hc).symm
        · exact hVt hvs hV

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
