-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarPlace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # Warpgroup 0's barrier events by barrier

A lane of warps 0–3 counts its role's barrier events in its ledger (`w0BarCnt`: barriers 9 to
12, none of the startup's); at a state the count is the state's ordinal (`Wg0.BarOk`). Its
`o`-th role barrier event is on barrier `Wg0.idAt R p o` (`Wg0.bar_kind`, `R` the CTA's blocks,
`p` the warp's parity), so the events of a prefix on barrier `id` (9 to 12) are the ordinals
below the count with that barrier (`w0_idCnt`, by induction along the trace).

`w0_bst`: a state of such a lane is the startup's or warpgroup 0's with the role's invariants at
the prefix's counts. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- The role's barrier events of lane `y`'s prefix `i` (its ledger's barriers 9 to 12). -/
def w0BarCnt (X : Execution) (y i : Nat) : Nat :=
  Wg0.barTot fun c => ((X.tr y).take i).countP (Wg0.cls c)

/-- The ordinals below `B` whose barrier is `id`. -/
def w0IdCnt (R p id B : Nat) : Nat :=
  ((List.range B).filter fun o => Wg0.idAt R p o = id).length

theorem w0IdCnt_succ (R p id B : Nat) :
    w0IdCnt R p id (B + 1) = w0IdCnt R p id B + if Wg0.idAt R p B = id then 1 else 0 := by
  simp only [w0IdCnt, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

theorem w0IdCnt_mono {R p id B B' : Nat} (h : B ≤ B') : w0IdCnt R p id B ≤ w0IdCnt R p id B' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [w0IdCnt_succ]; omega

/-- A prefix of a lane that has no `ub` event counts none of a class of `ub` events. -/
theorem w0_noUbTakeW_pre {c : Event → Bool} (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl)
    {i : Nat} (hal : LaneUbFree X y i) : ((X.tr y).take i).countP c = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => by
    obtain ⟨j, hji, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨fl, hk⟩ := hc f hcl
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    exact hal j hji pc fl hj

/-- **A state of a lane of warps 0–3** is the startup's, or warpgroup 0's with the role's
invariants at the prefix's counts. -/
theorem w0_bst_pre (hFw : Follow P L X) {i : Nat} (hal : LaneUbFree X y i)
    (hw : warp L y < 4) (hy : y < L.threads) {σ : (thread P L y).D}
    (hσ : Frame.stateAt (thread P L) X y i = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.exitOf d = none) ∨
      ∃ d n, σ = (.inr ⟨.inl .wg0, d⟩, n) ∧
        Wg0.RefCore L y d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) ∧
        Wg0.LaunchOk P L y d ∧ Wg0.BarOk d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) := by
  have hJ := (follow_iff.mp hFw y hy i).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · exact .inl ⟨d, n, rfl, by simpa [startupEnter] using glue_gate hσ⟩
  · cases e with
    | wg0 =>
      obtain ⟨-, ⟨hR, -⟩, -, -⟩ := hJ
      have hc : (fun c => n (.wg0 c)) = fun c => ((X.tr y).take i).countP (Wg0.cls c) :=
        funext fun c => state_count hσ (.wg0 c)
      have hu : n .ub = 0 := (state_count hσ .ub).trans
        (w0_noUbTakeW_pre (fun f h => by obtain ⟨pc, kd⟩ := f; cases kd <;> simp [cls] at h ⊢) hal)
      have hR' := hR hu
      rw [hc] at hR'
      obtain ⟨hC, hL, hB⟩ := hR' (w0_noUbTakeW_pre (fun f h => by
        obtain ⟨pc, kd⟩ := f
        cases kd with
        | ub fl => exact ⟨fl, rfl⟩
        | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf] at h
        | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf] at h
        | _ => simp [Wg0.cls, Wg0.kindOf] at h) hal)
      exact .inr ⟨d, n, rfl, hC, hL, hB⟩
    | dequant | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

theorem w0_bst (hFw : Follow P L X) (hnu : NoUbWg0 L X) (hw : warp L y < 4) (hy : y < L.threads)
    {i : Nat} {σ : (thread P L y).D} (hσ : Frame.stateAt (thread P L) X y i = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.exitOf d = none) ∨
      ∃ d n, σ = (.inr ⟨.inl .wg0, d⟩, n) ∧
        Wg0.RefCore L y d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) ∧
        Wg0.LaunchOk P L y d ∧ Wg0.BarOk d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) :=
  w0_bst_pre hFw (LaneUbFree.of_noUbWg0 hnu hw i) hw hy hσ

/-- **A role barrier event of a lane of warps 0–3** (barriers 9 to 12) is at a pc of warpgroup
0's code. -/
theorem w0_barPc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {j pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (y, j) = some ⟨pc, .bar id cnt md⟩) (h9 : 9 ≤ id) : 103 ≤ pc ∧ pc < 1842 := by
  rcases wg0_barRole hp hX hFw hw he rfl with h | h
  · obtain ⟨-, hk⟩ := barRow_startup hp hX hFw (Frame.lt_of_get hX he) he h rfl
    have hk' : Kind.bar id cnt md = .bar 0 none .sync := hk
    simp only [Kind.bar.injEq] at hk'
    omega
  · simp only [Wg0.inRole, decide_eq_true_eq] at h; omega

/-- **The role's barrier events by barrier**: a lane of warps 0–3 has, in prefix `i`, as many
events on barrier `id` (9 to 12) as ordinals below its role's barrier count have barrier `id`. -/
theorem w0_idCnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {id : Nat} (h9 : 9 ≤ id) (h12 : id ≤ 12) (i : Nat)
    (hal : LaneUbFree X y i) : ((X.tr y).take i).countP (Execution.isBarId id) =
      w0IdCnt (blocksOf P L (y / L.block)) (warp L y % 2) id (w0BarCnt X y i) := by
  induction i with
  | zero => simp [w0BarCnt, Wg0.barTot, w0IdCnt]
  | succ i ih =>
    have ih := ih (hal.mono (Nat.le_succ i))
    rcases hk : (X.tr y)[i]? with _ | e
    · have h1 : (X.tr y).take (i + 1) = (X.tr y).take i := by
        rw [List.take_add_one, hk]; simp
      simp only [w0BarCnt, h1] at ih ⊢
      exact ih
    have hget : X.get (y, i) = some e := hk
    have hT : ∀ c : Event → Bool, ((X.tr y).take (i + 1)).countP c =
        ((X.tr y).take i).countP c + if c e then 1 else 0 := fun c => by
      rw [List.take_add_one, hk, Option.toList_some, List.countP_append]
      simp [List.countP_singleton]
    by_cases hb : Execution.isBar e = true
    · have hub : ∀ fl, e.kind ≠ .ub fl := NoUbBefore.ne hal (Nat.lt_succ_self i) hget
      rcases wg0_barRole hp hX hFw hw hget hb with hlo | hr
      · have hc : ∀ c, Wg0.cls c e = false := fun c => by
          cases c <;> simp [Wg0.cls, Wg0.inRole] <;> omega
        obtain ⟨-, hk⟩ := barRow_startup hp hX hFw (Frame.lt_of_get hX hget) hget hlo hb
        have hk' : e.kind = .bar 0 none .sync := hk
        have hi : Execution.isBarId id e = false := by
          simp only [Execution.isBarId, hk', beq_eq_false_iff_ne]
          omega
        simp only [w0BarCnt, hT, hc, hi, Wg0.barTot] at ih ⊢
        simpa using ih
      · have hr' : 103 ≤ e.pc ∧ e.pc < 1842 := by
          simp only [Wg0.inRole, decide_eq_true_eq] at hr; omega
        obtain ⟨d, hRf, hE, -⟩ := wg0_at hp hX hFw hget hub hr'
        obtain ⟨hC, hL, -, ht⟩ := hRf (wg0_take_noUb hX hget)
        obtain ⟨-, hK⟩ := hE
        obtain ⟨c, hk⟩ := Wg0.bar_kind hub hK hb hC hL
        rw [Wg0.barW_warp hp, Nat.add_sub_cancel_left] at hk
        have h2 := Nat.mod_lt (warp L y) (show 0 < 2 by omega)
        have hid : 9 ≤ Wg0.idAt (blocksOf P L (y / L.block)) (warp L y % 2) (Wg0.barOrd d) ∧
            Wg0.idAt (blocksOf P L (y / L.block)) (warp L y % 2) (Wg0.barOrd d) ≤ 12 := by
          unfold Wg0.idAt; split_ifs <;> omega
        simp only [Wg0.barTot] at ht
        rw [w0BarCnt, Wg0.barTot] at ih
        generalize hI : Wg0.idAt (blocksOf P L (y / L.block)) (warp L y % 2) (Wg0.barOrd d) = I
          at hk hid
        have hcl : ∀ j, Wg0.cls (.bar j) e = decide (I = j) := fun j => by
          simp [Wg0.cls, Wg0.kindOf, hk, hr]
        have hi : Execution.isBarId id e = decide (I = id) := by
          by_cases h : I = id <;> simp [Execution.isBarId, hk, h]
        rw [w0BarCnt, Wg0.barTot]
        simp only [hT, hcl, hi, decide_eq_true_eq]
        rw [ht] at ih
        have hs : ∀ a b c' d' : Nat, a + b + c' + d' = Wg0.barOrd d →
            a + (if I = 9 then 1 else 0) + (b + if I = 10 then 1 else 0) +
              (c' + if I = 11 then 1 else 0) + (d' + if I = 12 then 1 else 0) =
              Wg0.barOrd d + 1 := fun a b c' d' h => by split_ifs <;> omega
        rw [hs _ _ _ _ ht, w0IdCnt_succ, hI, ← ih]
    · have hc : ∀ j, Wg0.cls (.bar j) e = false := fun j => by
        obtain ⟨pc, kd⟩ := e
        cases kd with
        | bar => simp [Execution.isBar] at hb
        | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf]
        | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf]
        | _ => simp [Wg0.cls, Wg0.kindOf]
      have hi : Execution.isBarId id e = false := by
        obtain ⟨pc, kd⟩ := e
        cases kd <;> simp_all [Execution.isBarId, Execution.isBar]
      simp only [w0BarCnt, hT, hc, hi, Wg0.barTot] at ih ⊢
      simpa using ih

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
