-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvSites

@[expose] public section

/-!
# One step of the softmax region keeps the iteration invariant

`SvInv.step`: for the successor `Sm.next` returns at every site but the second shuffle of the
stage (`shfl6`, which `SvInv.pair` takes with the first), given the premise on the event, `EvOk`.
The thread layer's invariant `Sm.Inv` of the state before the event is a hypothesis: the
counters of the loads (`cw`, `cv`), the loop's bounds and the first state's values.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- The probabilities' clause is vacuous at a site that is neither a stage nor a post site. -/
local macro "pfv" : tactic => `(tactic| simp [PfSite, StageSite, PostSite])
local macro "pfv_at" h:ident : tactic => `(tactic| simp [PfSite, StageSite, PostSite] at $h:ident)

/-- **One step of the softmax region keeps the invariant** (not at the second shuffle of the
stage). -/
theorem SvInv.step {d d' : D} {e : Event} (hI : Inv L g d)
    (hv : rowValid d.e (g % L.block) = true) (h : SvInv Q L g r s kvh B d)
    (hs6 : d.site ≠ .shfl6) (hev : EvOk Q r s kvh (g % L.block) d e)
    (hn : Sm.next L g d e = some (some d')) : SvInv Q L g r s kvh B d' := by
  have hh2 : Sm.half (g % L.block) < 2 := by unfold Sm.half; omega
  have hcd : ∀ S : Site, ¬ PostSite S → d.site = S → nDone d = d.i := by
    intro S hS hsS
    simp [nDone, hsS, hS]
  cases hs : d.site
  · -- setMaxReg
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- bar0
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · rename_i hact
      obtain ⟨hi0, -, -, hcw0, hcv0⟩ := hI.loop.2 hs
      refine SvInv.afterSetup (x := { d with cw := 64, w := fun _ => z16 }) h.ent hI.ok hv
        ?_ ?_ ?_ hn
      · have := h.corr
        rwa [hcd .bar0 (by simp [PostSite]) hs] at this
      · intro k hk hi
        dsimp only at hk hi ⊢
        rw [bfR_z16]
        refine (biasB_zero h.ent hh2 hk ?_).symm
        have hr25 : 0 < d.e.r25 ∧ d.e.r25 < 2 ^ 31 := by
          have := hI.ok.r26_of_lt hi
          omega
        intro hnb
        apply hact
        have hnb' : d.e.nbias ≤ d.e.split := by
          unfold blkOf at hnb
          rw [hi0] at hnb
          simpa using hnb
        unfold act0
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hr25, hv⟩, hnb'⟩
      · intro k hk
        dsimp only at hk
        omega
  · -- pre j
    rename_i j
    simp only [EvOk, hs] at hev
    simp only [Sm.next, hs] at hn
    split at hn
    · rename_i acc bs he
      split at hn
      · rename_i x hx
        split at hn
        · rename_i hbf
          obtain ⟨hcw, -⟩ := hI.cwPre j hs
          obtain ⟨hi0, hcv0, -⟩ := hI.loop.1 j hs
          have hxv := hev acc bs x he hx
          have hxb : bfR x = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
              d.i (Sm.half (g % L.block)) j.val := by
            rw [hxv]; rfl
          have hcnd := hcd (.pre j) (by simp [PostSite]) hs
          have hwb' : ∀ k < j.val + 1, d.i < d.e.r26 →
              bfR (setW d.w j.val x k) = biasB Q r s (tokOf (g % L.block))
                (kvh * 6 + remOf (g % L.block)) d.i (Sm.half (g % L.block)) k := by
            intro k hk hi
            exact setW_wb (d := d) (P := fun k => biasB Q r s (tokOf (g % L.block))
              (kvh * 6 + remOf (g % L.block)) d.i (Sm.half (g % L.block)) k)
              (fun k hk => h.wb k (by omega) hi) hxb k hk
          split at hn
          · rename_i hj
            simp only [Option.some.injEq] at hn
            subst hn
            have hc : Corr (slQ Q) ((List.range d.i).map B) d := by
              have := h.corr
              rwa [hcnd] at this
            refine SvInv.mk_vac d.i h.ent (by simp [nDone, PostSite]) (corr_of_ml hc rfl rfl) ?_
              h.vb (by simp) (by simp) (by simp [StageSite]) (by pfv)
            · intro k hk hi
              exact hwb' k (by simpa using hk) hi
          · rename_i hj
            refine SvInv.afterSetup (x := { d with cw := 64, w := setW d.w j.val x }) h.ent
              hI.ok hv ?_ ?_ ?_ hn
            · have := h.corr
              rwa [hcnd] at this
            · intro k hk hi
              have hj63 : j.val = 63 := by have := j.isLt; omega
              dsimp only at hk hi ⊢
              exact hwb' k (by omega) hi
            · exact h.vb
        · cases hn
      · cases hn
    · cases hn
  · -- nxt j
    rename_i j
    simp only [EvOk, hs] at hev
    simp only [Sm.next, hs] at hn
    split at hn
    · rename_i acc bs he
      split at hn
      · rename_i x hx
        split at hn
        · rename_i hbf
          obtain ⟨hcw, hcv, -, -⟩ := hI.cwNxt j hs
          have hxv := hev acc bs x he hx
          have hxb : bfR x = biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
              (d.i + 1) (Sm.half (g % L.block)) j.val := by
            rw [hxv]; rfl
          have hcnd := hcd (.nxt j) (by simp [PostSite]) hs
          have hvb' : ∀ k < j.val + 1, d.i + 1 < d.e.r26 →
              bfR (setW d.v j.val x k) = biasB Q r s (tokOf (g % L.block))
                (kvh * 6 + remOf (g % L.block)) (d.i + 1) (Sm.half (g % L.block)) k := by
            intro k hk hi
            exact setW_wb (d := { d with w := d.v }) (P := fun k => biasB Q r s
              (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) (d.i + 1)
              (Sm.half (g % L.block)) k)
              (fun k hk => h.vb k (by omega) hi) hxb k hk
          have hc : Corr (slQ Q) ((List.range d.i).map B) d := by
            have := h.corr
            rwa [hcnd] at this
          split at hn
          · rename_i hj
            simp only [Option.some.injEq] at hn
            subst hn
            refine SvInv.mk_vac d.i h.ent (by simp [nDone, PostSite]) (corr_of_ml hc rfl rfl)
              h.wb ?_ (by simp) (by simp) (by simp [StageSite]) (by pfv)
            · intro k hk hi
              exact hvb' k (by simpa using hk) hi
          · rename_i hj
            simp only [Option.some.injEq] at hn
            subst hn
            have hj63 : j.val = 63 := by have := j.isLt; omega
            refine SvInv.mk_vac d.i h.ent (by simp [nDone, PostSite]) (corr_of_ml hc rfl rfl)
              h.wb ?_ (by simp) (by simp) (by simp [StageSite]) (by pfv)
            · intro k hk hi
              dsimp only at hk hi ⊢
              exact hvb' k (by omega) hi
        · cases hn
      · cases hn
    · cases hn
  · -- waitS
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      split at hn
      · subst hn
        exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
      · subst hn; exact h
    · cases hn
  · -- shfl4
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · rename_i b _
        simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd' (fun st => { st with bw := b }) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- ldS
    simp only [EvOk, hs] at hev
    simp only [Sm.next, hs] at hn
    split at hn
    · rename_i a vals sh he
      split at hn
      · rename_i hv64
        simp only [Option.some.injEq] at hn
        subst hn
        refine h.of_same0 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [nDone, PostSite, hs]) ?_ (by intro hh; simp at hh)
          (fun hh => by simp [StageSite] at hh) (fun hh => by pfv_at hh)
        intro _ k hk
        have hk' : k < vals.length := by omega
        have := hev a vals sh he k hk
        rw [List.getElem?_eq_getElem hk'] at this
        simp only [Option.some.injEq] at this
        simp only [svOf, hk', ↓reduceDIte]
        exact this
      · cases hn
    · cases hn
  · -- waitLd
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      rw [finT_eq fun k hk => ⟨_, h.sv hs k hk⟩]
      obtain ⟨hcw, -, hilt⟩ := hI.late (by rw [hs]; trivial)
      refine h.of_same0 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [nDone, PostSite, hs]) (by intro hh; simp at hh) ?_
        (fun hh => by simp [StageSite] at hh) (fun hh => by pfv_at hh)
      intro _ k hk
      exact fin_sv (d := d) h.ent (h.sv hs) (fun k hk => h.wb k (by omega) hilt) hcw k hk
    · cases hn
  · -- shfl5
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.of_same0 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [nDone, PostSite, hs, D.afterMax]) (by intro hh; simp [D.afterMax] at hh)
          (by intro hh; simp [D.afterMax] at hh)
          (fun hh => by simp [StageSite, D.afterMax] at hh)
          (fun hh => by simp [PfSite, StageSite, PostSite, D.afterMax] at hh)
      · split at hn
        · simp only [Option.some.injEq] at hn
          subst hn
          exact h.of_same0 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            (by simp [nDone, PostSite, hs, D.afterMaxT]) (by intro hh; simp [D.afterMaxT] at hh)
            (by intro hh; simp [D.afterMaxT] at hh)
            (fun hh => by simp [StageSite, D.afterMaxT] at hh)
            (fun hh => by simp [PfSite, StageSite, PostSite, D.afterMaxT] at hh)
        · cases hn
    · cases hn
  · -- shfl6
    exact absurd hs hs6
  · -- bar22
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- shfl7
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- shfl8
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- shfl9
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- shfl10
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- store10
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- bar23
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- ldL
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- shfl11
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- shfl12
    simp only [Sm.next, hs] at hn
    split at hn
    · split at hn
      · split at hn
        · exact SvInv.toBar20 h (by simp [StageSite, hs]) hn
        · simp only [Option.some.injEq] at hn
          subst hn
          exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
      · cases hn
    · cases hn
  · -- waitO
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      split at hn
      · subst hn
        exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
      · subst hn; exact h
    · cases hn
  · -- ldO
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.upd2 _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [SiteOk, PostSite, StageSite, hs])
    · cases hn
  · -- waitLdO
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · cases hn
  · -- bar24
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- stO
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · cases hn
  · -- waitStO
    simp only [Sm.next, hs] at hn
    exact SvInv.toBar20 h (by simp [StageSite, hs]) hn
  · -- bar20
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · cases hn
  · -- tmemSt
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · cases hn
  · -- tmemWait
    simp only [Sm.next, hs, Option.some.injEq] at hn
    subst hn
    exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
  · -- bar21
    simp only [Sm.next, hs] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h.site' (by simp [SiteOk, PostSite, StageSite, hs])
    · exact SvInv.afterArrive hI hv h (by simp [PostSite, hs]) (by simp [LateSite, hs]) hn
  · -- arrive
    simp only [Sm.next, hs] at hn
    split at hn
    · exact SvInv.afterArrive hI hv h (by simp [PostSite, hs]) (by simp [LateSite, hs]) hn
    · cases hn

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
