-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvCount

@[expose] public section

/-! # Which warp runs which role

The dispatch enters a role at its first iteration only (`role_count`), from the byte of the
prologue's role word `0x01000202` for the warp (`role_read1`): byte `w - 4` is 2, 2, 0, 1 for the
warps 4 to 7, so warp 6 is the loader and warp 7 the MMA warp; the second iteration reads the
epilogue's `0x03030303` (`role_readN`), whose bytes send every warp to the exit path.
`role_warp`: every loader state is of warp 6 and every MMA state of warp 7. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The warps of the loader's and the MMA warp's states. -/
def RW (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), .loader _ _⟩, _) => g % L.block / 32 = 6
  | (.inr ⟨.inl (.worker _), .mma _ _⟩, _) => g % L.block / 32 = 7
  | (.inr ⟨.inl (.worker _), .idle _⟩, _) => g % L.block / 32 < 6
  | _ => True

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedSimpArgs false in
/-- **The loader runs on warp 6, the MMA warp on warp 7, the idle role on warps 4 and 5.** -/
theorem role_warp (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      RW Q L g σ := by
  have hb : L.block = 256 := hp.block
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · simp only [Code.withStubs, frag, Worker.code]; trivial
          · trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlt _ hk0).2
          have hw8 : g % L.block / 32 < 8 := by
            have := Nat.mod_lt g (show 0 < L.block by omega)
            omega
          have hsr := hp.sharedRange
          unfold sharedBytes at hsr
          cases d with
          | worker wd =>
            -- only the dispatch's step enters a role
            by_cases hs : wd.site = .ldRole
            · obtain ⟨site, P⟩ := wd
              simp only at hs
              subst hs
              obtain ⟨a, bs, hk', d', hdisp, hst⟩ := dispatch_succ hσw
              obtain ⟨pc, kd⟩ := e
              simp only at hk'
              subst hk'
              have hget : X.get (g, k) = some ⟨pc, .rd a bs⟩ := he
              have hc0 : _ % 3 = _ := w1_inv hp hX hg k hlt _ hk0
              have hR : RIt (.worker ⟨.ldRole, P⟩) _ := ri_inv hp hX hg k hlt _ hk0
              simp only [wph] at hc0
              have hc4 := hR.2.2.1 rfl
              rcases (by omega : ((X.tr g).take k).countP (Execution.isBarId 1) = 1 ∨
                  4 ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) with h1 | h4
              · obtain ⟨v, hv, hl, hbs⟩ := role_read1 hp hX hget hk0 h1
                rw [storeValue_b32'] at hv
                obtain rfl := (Except.ok.inj hv).symm
                rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
                subst hbs
                rw [dispatch_byte P _ _ (by omega)] at hdisp
                obtain rfl := Option.some.inj (Option.some.inj hdisp)
                rcases (by omega : g % L.block / 32 = 4 ∨ g % L.block / 32 = 5 ∨
                    g % L.block / 32 = 6 ∨ g % L.block / 32 = 7) with h | h | h | h
                all_goals
                  rw [h] at hst
                  norm_num [Proof.Worker.roleSite, Proof.WComp.roleStart] at hst
                all_goals (repeat' split at hst)
                all_goals first
                  | (cases hst; done)
                  | (simp only [Option.some.injEq, reduceCtorEq] at hst; done)
                  | (subst hst; first | trivial | exact h | (show _ < 6; omega))
                  | (simp only [Option.some.injEq] at hst; subst hst;
                     first | trivial | exact h | (show _ < 6; omega))
              · obtain ⟨v, hv, hl, hbs⟩ := role_readN hp hX hget hk0 h4
                rw [storeValue_b32'] at hv
                obtain rfl := (Except.ok.inj hv).symm
                rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
                subst hbs
                rw [dispatch_byte P _ _ (by omega)] at hdisp
                obtain rfl := Option.some.inj (Option.some.inj hdisp)
                have hi : 50529027 / 256 ^ (g % L.block / 32 - 4) % 256 = 3 := by
                  rcases (by omega : g % L.block / 32 - 4 = 0 ∨ g % L.block / 32 - 4 = 1 ∨
                    g % L.block / 32 - 4 = 2 ∨ g % L.block / 32 - 4 = 3) with h | h | h | h <;>
                    rw [h] <;> norm_num
                simp only [hi, Proof.Worker.roleSite, Option.getD_some,
                  Proof.WComp.roleStart, Option.some.injEq] at hst
                subst hst
                trivial
            · rw [Proof.EvW.next_worker_map hs] at hσw
              obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some hσw
              subst ha
              trivial
          | loader dl P =>
            rcases role_succ (σ := .loader dl P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : dl.site ≠ .setMaxInc := by intro h; simp [wph, ldPh, h] at hph
              rw [Proof.EvW.next_loader_map P hs] at hσw
              obtain ⟨d', -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              exact hR0
            · trivial
          | mma dm P =>
            rcases role_succ (σ := .mma dm P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : dm.site ≠ .setMaxRegInc := by intro h; simp [wph, mmPh, h] at hph
              rw [Proof.EvW.next_mma_map P hs] at hσw
              obtain ⟨d', -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              exact hR0
            · trivial
          | idle di =>
            rcases role_succ (σ := .idle di) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : di.site ≠ .inc := by intro h; simp [wph, idPh, h] at hph
              rw [Proof.EvW.next_idle_map hs] at hσw
              obtain ⟨a, -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              exact hR0
            · trivial
          | exit x =>
            obtain ⟨x', rfl⟩ := exit_succ hσw
            trivial
      · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
