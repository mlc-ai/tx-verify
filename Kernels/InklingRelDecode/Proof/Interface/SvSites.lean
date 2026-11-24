-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvPair

@[expose] public section

/-!
# One step of the softmax region keeps the iteration invariant

`SvInv.step`: for the successor `Sm.next` returns at every site but the second shuffle of the
stage (`shfl6`, which `SvInv.pair` takes with the first), the invariant is kept, given the
premise on the event: `EvOk`. A bias load returns the `bf16` number of the key's bias
(`Spec.bias`); the S tile's load returns the exact scores (`Spec.score`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- **A bias load returns the `bf16` number of the key's bias.** -/
def BiasEv (Q : Params) (r s kvh T b j : Nat) (e : Event) : Prop :=
  ∀ acc bs x, e.kind = .rd acc bs → rebuild 3 bs = .ok x →
    x = Value.float .bf16 (biasB Q r s (tokOf T) (kvh * 6 + remOf T) b (Sm.half T) j)

/-- **The S tile's load returns the exact scores** of the keys of the thread's half. -/
def ScoreEv (Q : Params) (r s kvh T b : Nat) (e : Event) : Prop :=
  ∀ a vals sh, e.kind = .tc (.ld a vals sh) → ∀ j < 64,
    vals[j]? = some (Value.float .f32 (score Q r (tokOf T) (kvh * 6 + remOf T)
      (keyB Q s b (Sm.half T) j)))

/-- **The premise on the event of a state.** -/
def EvOk (Q : Params) (r s kvh T : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .pre j => BiasEv Q r s kvh T d.i j.val e
  | .nxt j => BiasEv Q r s kvh T (d.i + 1) j.val e
  | .ldS => ScoreEv Q r s kvh T d.i e
  | _ => True

/-- Loading word `j` with the bias of the key keeps the clause of the loaded words. -/
theorem setW_wb {d : D} {j : Nat} {x : Value} {P : Nat → ℝ}
    (hc : ∀ k < j, bfR (d.w k) = P k) (hx : bfR x = P j) :
    ∀ k < j + 1, bfR (setW d.w j x k) = P k := by
  intro k hk
  by_cases hkj : k = j
  · subst hkj
    simp [setW, hx]
  · simp only [setW, Function.update_of_ne hkj]
    exact hc k (by omega)

/-- A state with none of the invariant's site conditions needs only the clauses on the running
maximum and sum and on the bias words. -/
theorem corr_of_ml {d d' : D} {sl : ℝ} {bs : List (List (ℝ × ℝ))} (h : Corr sl bs d)
    (hm : d'.m = d.m) (hl : d'.l = d.l) : Corr sl bs d' := by
  unfold Corr at *
  rw [hm, hl]
  exact h

theorem SvInv.mk_vac {d : D} (n : Nat) (hE : EntFull Q r s kvh d.e) (hn : nDone d = n)
    (hc : Corr (slQ Q) ((List.range n).map B) d)
    (hwb : ∀ k < d.cw, d.i < d.e.r26 →
      bfR (d.w k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
        (Sm.half (g % L.block)) k)
    (hvb : ∀ k < d.cv, d.i + 1 < d.e.r26 →
      bfR (d.v k) = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) (d.i + 1)
        (Sm.half (g % L.block)) k)
    (h1 : d.site ≠ .waitLd) (h2 : d.site ≠ .shfl5) (h3 : ¬ StageSite d.site)
    (h4 : ¬ PfSite d.site) :
    SvInv Q L g r s kvh B d :=
  ⟨hE, by rw [hn]; exact hc, hwb, hvb, fun h => absurd h h1, fun h => absurd h h2,
    fun h => absurd h h3, fun h => absurd h h4⟩

/-- A step that changes the site and numbers of the stage that the invariant does not read. -/
theorem SvInv.upd {d : D} (h : SvInv Q L g r s kvh B d) (S : Site) (f : Stg → Stg)
    (hf : (f d.stg).fsv = d.stg.fsv ∧ (f d.stg).mn = d.stg.mn ∧ (f d.stg).kp = d.stg.kp ∧
      (f d.stg).al = d.stg.al ∧ (f d.stg).rs = d.stg.rs ∧ (f d.stg).alr = d.stg.alr)
    (hn : PostSite S ↔ PostSite d.site) (hsv : S = .waitLd → d.site = .waitLd)
    (hown : S = .shfl5 → d.site = .shfl5) (hst : StageSite S → StageSite d.site) :
    SvInv Q L g r s kvh B { d with site := S, stg := f d.stg } := by
  refine h.of_same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, hf.1, rfl⟩ ?_ hsv hown
    (fun hh => ⟨hst hh, ⟨hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩⟩)
  unfold nDone
  by_cases hp : PostSite S
  · simp [hp, hn.mp hp]
  · simp [hp, mt hn.mpr hp]

/-- The site conditions of a step from site `S0` to site `S`. -/
def SiteOk (S S0 : Site) : Prop :=
  (PostSite S ↔ PostSite S0) ∧ (S = .waitLd → S0 = .waitLd) ∧ (S = .shfl5 → S0 = .shfl5) ∧
    (StageSite S → StageSite S0)

theorem SvInv.site' {d : D} (h : SvInv Q L g r s kvh B d) {S : Site} (hS : SiteOk S d.site) :
    SvInv Q L g r s kvh B { d with site := S } :=
  h.site S hS.1 hS.2.1 hS.2.2.1 hS.2.2.2

theorem SvInv.upd' {d : D} (h : SvInv Q L g r s kvh B d) {S : Site} (f : Stg → Stg)
    (hf : (f d.stg).fsv = d.stg.fsv ∧ (f d.stg).mn = d.stg.mn ∧ (f d.stg).kp = d.stg.kp ∧
      (f d.stg).al = d.stg.al ∧ (f d.stg).rs = d.stg.rs ∧ (f d.stg).alr = d.stg.alr)
    (hS : SiteOk S d.site) :
    SvInv Q L g r s kvh B { d with site := S, stg := f d.stg } :=
  h.upd S f hf hS.1 hS.2.1 hS.2.2.1 hS.2.2.2

theorem SvInv.upd2 {d : D} (h : SvInv Q L g r s kvh B d) {S : Site} (st : Stg)
    (hf : st.fsv = d.stg.fsv ∧ st.mn = d.stg.mn ∧ st.kp = d.stg.kp ∧ st.al = d.stg.al ∧
      st.rs = d.stg.rs ∧ st.alr = d.stg.alr) (hS : SiteOk S d.site) :
    SvInv Q L g r s kvh B { d with site := S, stg := st } :=
  h.upd' (fun _ => st) hf hS

/-- **After the arrival on `p_ready`**: the next iteration's packs (`v` becomes `w`), the loop
variables and the loop test. -/
theorem SvInv.afterArrive {d d' : D} (hI : Inv L g d) (hv : rowValid d.e (g % L.block) = true)
    (h : SvInv Q L g r s kvh B d) (hs : PostSite d.site) (hl : LateSite d.site)
    (hn : Sm.afterArrive L g d = some (some d')) : SvInv Q L g r s kvh B d' := by
  unfold Sm.afterArrive at hn
  have hcv : d.cv = 64 := (hI.late hl).2.1
  have hnd : nDone d = d.i + 1 := by simp [nDone, hs]
  refine SvInv.afterSetup (x := { d with i := d.i + 1, w := d.v, cw := 64, cv := 0 })
    h.ent hI.ok hv ?_ ?_ ?_ hn
  · have := h.corr
    rwa [hnd] at this
  · intro k hk hi
    dsimp only at hk hi ⊢
    exact h.vb k (by omega) hi
  · intro k hk
    simp at hk

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
