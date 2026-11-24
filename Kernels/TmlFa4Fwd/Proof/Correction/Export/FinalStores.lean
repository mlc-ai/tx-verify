-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Correction.FstPos
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.Correction.FstIs1
import Kernels.TmlFa4Fwd.Proof.Lib.ProxyFence
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative

@[expose] public section

/-! # A correction lane's final stores before its ready arrival

`corr_fst_before`: a correction lane's arrival on the ready barrier of stage `st` follows, with a
proxy fence between, its store of every word of its row's line in each quarter of the stage's
staging buffer. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem done_pred : Correction.allSites.all (fun s => (Correction.nexts s).all fun s' =>
    match s' with
    | .fdone st 1 => s == .fdone st 0
    | .fdone st 0 => s == .fence st
    | _ => true) = true := by decide +kernel

private theorem done_off : Correction.allSites.all (fun s =>
    [(0 : Fin 2), 1].all fun st => Correction.arrOff s != 208 + 8 * st.val || s == .fdone st 1) =
      true := by decide +kernel

/-- The site before an arrival after the final stores. -/
private theorem done_prev {d d' : Correction.D} {e : Event} {st k : Fin 2}
    (hev : Correction.Ev p L g d e) (hn : Correction.succ p L g d e = some (some d'))
    (hs : d'.site = .fdone st k) : d.site = if k = 0 then .fence st else .fdone st 0 := by
  rcases Correction.succ_cases hn with ⟨rfl, _, _, _, _, hk⟩ | ⟨hf, -, rfl⟩ | hM
  · exfalso
    obtain ⟨site, v, kk⟩ := d'
    simp only at hs
    subst hs
    simp only [Correction.Ev] at hev
    rw [hk] at hev
    cases hev
  · exfalso
    simp only at hs
    rw [hs] at hf
    cases hf
  · have h1 := List.all_eq_true.mp (List.all_eq_true.mp done_pred d.site
      (Correction.mem_allSites _)) d'.site hM.1
    rw [hs] at h1
    fin_cases k <;> simpa using h1

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- The state before a correction state. -/
theorem corr_prev {i : Nat} {d' : Correction.Control.D} {n' : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g i = some (some (CorrWarp.cinj p L g d' n')))
    (hub : n' .ub = 0) (hil : i ≤ (X.tr g).length) (hs : d'.site ≠ .setmax) :
    ∃ k d n e, i = k + 1 ∧ X.get (g, k) = some e ∧
      Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) ∧ n .ub = 0 ∧
      Correction.Control.Represents p L g d d' e ∧ Correction.Control.Ev p L g d e ∧
      (∀ f, e.kind ≠ .ub f) := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hσ; cases hσ
  | succ k =>
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    have hst := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
    rw [hσ] at hst
    have hub' : ∀ f, e.kind ≠ .ub f := by
      intro f hk
      cases hs0 : Frame.stateAt (thread p L) X g k with
      | none => rw [hs0] at hst; simp at hst
      | some o =>
        cases o with
        | none =>
          rw [hs0] at hst
          exact absurd hst (by simp [Flow.Code.toMachine])
        | some σ0 =>
          rw [hs0] at hst
          have hn : (thread p L g).next σ0 e = some (some (CorrWarp.cinj p L g d' n')) := hst.symm
          obtain ⟨σ1, n0⟩ := σ0
          obtain ⟨-, hn2⟩ := Code.counted_next_some hn
          simp only at hn2
          rw [hn2] at hub
          simp [Code.bump, cls, hk] at hub
    rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub' with ⟨s, n0, hσ', -, -, hi, hev'⟩ |
      ⟨d0, n0, hσ', h0', hR', hinv, hev', -⟩
    · exfalso
      rw [hσ'] at hst
      have hn : (thread p L g).next (.inl s, n0) e = some (some (CorrWarp.cinj p L g d' n')) :=
        hst.symm
      obtain ⟨h1, -⟩ := Code.counted_next_some hn
      simp only [glued, Code.glue, Startup.code] at h1
      cases hsu : Startup.succ L g s e with
      | none => rw [hsu] at h1; simp at h1
      | some o =>
        cases o with
        | none => rw [hsu] at h1; simp at h1
        | some s' =>
          rw [hsu] at h1
          simp only [Option.map_some, Option.some.injEq, Code.enter] at h1
          split at h1
          · rename_i r _
            cases r <;> cases h1
            exact hs rfl
          · cases h1
    · rw [hσ'] at hst
      have hn : (thread p L g).next (CorrWarp.cinj p L g d0 n0) e =
          some (some (CorrWarp.cinj p L g d' n')) := hst.symm
      rw [CorrWarp.next_cinj] at hn
      cases hr : Correction.Control.succ p L g d0 e with
      | none => rw [hr] at hn; simp at hn
      | some o =>
        cases o with
        | none => rw [hr] at hn; simp at hn
        | some d1 =>
          rw [hr] at hn
          simp only [Option.map_some, Option.some.injEq] at hn
          cases hn
          exact ⟨k, d0, n0, e, rfl, he, hσ', h0',
            Correction.Control.represents (hR' h0').1.counts hev' hub' hr, hev', hub'⟩

/-- The stores before a state of the store block. -/
theorem corr_fst_at {st : Fin 2} : ∀ (i : Nat) {d : Correction.Control.D} {n : Cls → Nat}
    {N M : Nat},
    Frame.stateAt (thread p L) X g i = some (some (CorrWarp.cinj p L g d n)) → n .ub = 0 →
    i ≤ (X.tr g).length → Correction.fstPos st d = some N → M < N →
    ∃ k d0 n0 e, k < i ∧ X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧
      Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d0 n0)) ∧
      Correction.Control.Ev p L g d0 e ∧ Correction.isFstS st d0.site = true ∧
      Correction.fstPos st d0 = some M := by
  intro i
  induction i with
  | zero =>
    intro d n N M hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ i ih =>
    intro d n N M hσ hub hil hN hM
    have hs : d.site ≠ .setmax := by
      rintro h
      simp [Correction.fstPos, Correction.Control.D.scheduler, h] at hN
    obtain ⟨k, d0, n0, e, hk, he, hσ0, hub0, hn, hev, hube⟩ :=
      corr_prev hp hX hFw hw hw1 hσ hub hil hs
    obtain rfl : i = k := by omega
    obtain ⟨a,ev,_,_,hstep,hsite,_,hsub,_⟩ := hn
    have hpos : Correction.fstPos st a = Correction.fstPos st d.scheduler := by
      unfold Correction.fstPos
      rw [hsite,hsub]
      rfl
    rcases Correction.fstPos_succ hstep (hpos.trans hN) with rfl | ⟨M0, hM0, hNM⟩
    · omega
    · by_cases hlt : M < M0
      · obtain ⟨k', d1, n1, e1, h1, h2⟩ := ih hσ0 hub0 (by omega) hM0 hlt
        exact ⟨k', d1, n1, e1, by omega, h2⟩
      · by_cases hf : Correction.isFstS st d0.scheduler.site = true
        · have : M = M0 := by simp only [hf, ↓reduceIte] at hNM; omega
          subst this
          exact ⟨i, d0, n0, e, by omega, he, hube, hσ0, hev, hf, hM0⟩
        · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hNM
          omega

/-- **A correction lane's ready arrival follows its final stores and a proxy fence.** -/
theorem corr_fst_before {st : Fin 2} {i pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, i) = some ⟨pc, .arrive (obj L g (208 + 8 * st.val)) tx c rel sc⟩) {q t : Nat}
    (hq : q < 4) (ht : t < 32) :
    ∃ f j pcf pcj a bs, j < f ∧ f < i ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j) = some ⟨pcj, .wr a bs⟩ ∧ a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 3072 + 65536 * st.val + 16384 * q +
        128 * Correction.rowN L g + 4 * t⟩ := by
  have hub : ∀ f, (⟨pc, .arrive (obj L g (208 + 8 * st.val)) tx c rel sc⟩ : Event).kind ≠ .ub f :=
    fun f h => by cases h
  have hil : i < (X.tr g).length := by have := len_of_get he; simpa using this
  have hst2 := st.isLt
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n0, -, -, -, hi, hev'⟩ |
    ⟨d, n, hσ, h0, hR, hinv, hev, -⟩
  · obtain ⟨c, hc⟩ := start_mbar hev' hi.2 (l := obj L g (208 + 8 * st.val)) rfl
    cases hc
  -- the site
  have hsite : d.site = .fdone st 1 := by
    rcases corr_mbar2 (hev.data_or_vote.resolve_right (by rintro ⟨_,_,hh⟩; cases hh))
      (l := obj L g (208 + 8 * st.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
    swap
    · cases hk
    have ho : 208 + 8 * st.val = Correction.arrOff d.site := obj_inj hl
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp done_off d.site
      (Correction.mem_allSites _)) st (by fin_cases st <;> simp)
    simpa [← ho] using h1
  obtain ⟨k1, d1, n1, e1, rfl, he1, hσ1, h01, hn1, hev1, hub1⟩ :=
    corr_prev hp hX hFw hw hw1 hσ h0 hil.le (by rw [hsite]; simp)
  have hs1 : d1.site = .fdone st 0 := by
    obtain ⟨a,ev,hEv,_,hn,ha,_⟩ := hn1
    simpa [Correction.Control.D.scheduler] using done_prev hEv hn (ha.trans hsite)
  obtain ⟨k2, d2, n2, e2, rfl, he2, hσ2, h02, hn2, hev2, hub2⟩ :=
    corr_prev hp hX hFw hw hw1 hσ1 h01 (by omega) (by rw [hs1]; simp)
  have hs2 : d2.site = .fence st := by
    obtain ⟨a,ev,hEv,_,hn,ha,_⟩ := hn2
    simpa [Correction.Control.D.scheduler] using done_prev hEv hn (ha.trans hs1)
  -- the fence
  obtain ⟨pcf, kdf⟩ := e2
  have hkf : ∃ k sc, kdf = .fenceProxy k sc := by
    obtain ⟨site, v, kk⟩ := d2
    simp only at hs2
    subst hs2
    exact hev2
  obtain ⟨kf, scf, rfl⟩ := hkf
  obtain ⟨rfl, rfl⟩ := proxy_fence hX he2
  -- the store
  obtain ⟨kc, hkc, hcol⟩ : ∃ kc < 8, (g % L.block % 8) ^^^ kc = t / 4 := by
    have key : ∀ a < 8, ∀ b < 8, ∃ kc < 8, a ^^^ kc = b := by decide
    exact key _ (Nat.mod_lt _ (by decide)) _ (by omega)
  have hN : Correction.fstPos st d2 = some 128 := by
    simp only [Correction.fstPos, Correction.Control.D.scheduler, hs2, ↓reduceIte]
  obtain ⟨j, d0, n0, e0, hj, he0, hub0, hσ0, hev0, hf0, hM⟩ :=
    corr_fst_at hp hX hFw hw hw1 (st := st) (M := 8 * (4 * q + kc / 2) + 4 * (kc % 2) + t % 4) k2
      hσ2 h02 (by omega) hN (by omega)
  obtain ⟨jj, hh, hsf⟩ : ∃ jj hh, d0.site = .fst st jj hh := by
    revert hf0
    cases d0.site <;> simp [Correction.isFstS]
  have hMe : 8 * jj.val + 4 * hh.val + d0.k.val =
      8 * (4 * q + kc / 2) + 4 * (kc % 2) + t % 4 := by
    simp only [Correction.fstPos, Correction.Control.D.scheduler, hsf, ↓reduceIte,
      Option.some.injEq] at hM
    exact hM
  have hk4 := d0.k.isLt
  have hh2 := hh.isLt
  obtain ⟨pcj, kdj⟩ := e0
  obtain ⟨a, bs, rfl⟩ : ∃ a bs, kdj = .wr a bs := by
    obtain ⟨site, v, kk⟩ := d0
    simp only at hsf
    subst hsf
    rcases hev0 with ⟨a, bs, h⟩ | ⟨f, h⟩
    · exact ⟨a, bs, h⟩
    · exact absurd h (hub0 f)
  obtain ⟨ts, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he0 hσ0 (fun _ => nofun)
  have hfe := Correction.fst_exact hp (d := d0) hat hc hf hsf rfl
  obtain ⟨hz, hl⟩ := hfe
  refine ⟨k2, j, pcf, pcj, a, bs, hj, by omega, he2, he0, hz, ?_⟩
  rw [hl]
  have hcw := Correction.colW_col (L := L) (g := g) hp st ⟨2 * (jj.val % 4) + hh.val, by omega⟩
  have hkk : 2 * (jj.val % 4) + hh.val = kc := by omega
  have hq' : jj.val / 4 = q := by omega
  have hs4 : d0.k.val = t % 4 := by omega
  change (Correction.colW L g st _).toNat = _ + 16 * ((g % L.block % 8) ^^^ _) at hcw
  simp only [hkk] at hcw
  rw [hcol] at hcw
  simp only [hkk, hq', hs4, Loc.mk.injEq, true_and]
  rw [hcw]
  unfold Correction.lineAt
  omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
