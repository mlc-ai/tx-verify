-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.PairRead

@[expose] public section

/-! # The loader's counter bounds as an invariant

The loader's machine follows every word its `(num_pre, num_iters)` load returns, so its counter
bounds (`Loader.Rng`: the counters below `2 ^ 31`, the counter below `num_iters` in the loop) are
not facts of the machine. On the role table they hold at every loader state (`ld_rng`): the
loader is entered at its first site (no counter), the two loads return the CTA's `num_pre`
(at most 3) and `num_iters` (below `2 ^ 31`) (`pair_read`), and every other step keeps the bounds
(`Loader.Rng.next`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem numPre_le3 (Q : Params) (r s : Nat) : Proof.ProA.numPre Q r s ≤ 3 := by
  unfold Proof.ProA.numPre
  exact Nat.min_le_right _ _

/-- `num_iters` is below `2 ^ 31`: the iterations are at most the request's blocks plus one, and
the sequence is below `2 ^ 31` (`Pre.seqRange`). -/
theorem numIters_lt31 (hpre : Pre Q L m) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s < 2 ^ 31 := by
  have h1 := Proof.SmEntry.iters_lt Q r s hpre.splitsPos
  have h2 := hpre.seqRange _ hr
  unfold Params.blocks at h1
  omega

/-- A worker step into a loader state is the dispatch's entry (the loader's first site) or a step
of the loader machine. -/
theorem w_next_loader {s : Proof.WComp.WSt} {e : Event} {d' : Proof.Loader.D}
    {P' : Proof.Loader.Pro} (h : Proof.WComp.next L g s e = some (some (.loader d' P'))) :
    d'.site = .setMaxDec ∨ ∃ d, s = .loader d P' ∧ d.site ≠ .setMaxInc ∧
      Proof.Loader.next L g d e = some (some d') := by
  cases s with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨site, P⟩ := w
      simp only at hs
      subst hs
      left
      change Proof.WComp.dispatch L g P e = _ at h
      unfold Proof.WComp.dispatch at h
      split at h
      · rename_i d0 hd
        rcases (Proof.EvW.ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
          simp only [Proof.WComp.roleStart] at h
        all_goals (repeat' split at h)
        all_goals first
          | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
          | (simp only [Option.some.injEq, Proof.WComp.WSt.loader.injEq] at h
             obtain ⟨rfl, -⟩ := h
             rfl)
      · cases h
      · cases h
    · rw [Proof.EvW.next_worker_map hs] at h
      obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
      cases ha
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_idle_map hs] at h
      obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
      cases ha
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_loader_map P hs] at h
      obtain ⟨a, ha, he⟩ := Proof.EvW.map_map_some h
      simp only [Proof.WComp.WSt.loader.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inr ⟨d, rfl, hs, ha⟩
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      cases h
    · rw [Proof.EvW.next_mma_map P hs] at h
      obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
      cases ha
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s <;> cases h

/-- The loader states' counter bounds. -/
def LR (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _) => Proof.Loader.Rng d
  | _ => True

/-- **The loader's counter bounds along a thread.** -/
theorem ld_rng (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      LR Q L g σ := by
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
      · -- the startup enters the worker at the loop's head
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · trivial
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
          cases σw' with
          | loader d' P' =>
            show Proof.Loader.Rng d'
            rcases w_next_loader hσw with hst | ⟨dl, rfl, hne, hld⟩
            · have h1 : d'.site.iBounded = false := by
                simp [hst, Proof.Loader.Site.iBounded, Proof.Loader.Site.bounded,
                  Proof.Loader.Site.inLoop]
              have h2 : d'.site.bounded = false := by
                simp [hst, Proof.Loader.Site.bounded, Proof.Loader.Site.inLoop]
              have h3 : d'.site.inLoop = false := by simp [hst, Proof.Loader.Site.inLoop]
              exact ⟨fun h => by simp [h1] at h, fun h => by simp [h2] at h,
                fun h => by simp [h3] at h, fun h => by simp [h1] at h, fun h => by simp [h2] at h⟩
            · have hrd : Proof.Loader.Rng dl := hR0
              have hget : X.get (g, k) = some e := he
              obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
                Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
              cases o with
              | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
              | some u =>
                have hsh : Proof.EvW.LdShapeW Q L g dl e := frag_ev hp hg hJ hat hi hc hf
                have hw : 128 ≤ g % L.block := by
                  have := (tm_inv hp hX hg k hlt _ hk0).2
                  have : 4 ≤ g % L.block / 32 := this
                  omega
                by_cases h0 : dl.site = .ld0
                · unfold Proof.EvW.LdShapeW at hsh
                  rw [h0] at hsh
                  obtain ⟨ac, bs, rfl, hloc, hsz, -⟩ := hsh
                  have hbs := pair_read hp hX hget hw 0 (by rw [hloc]; simp) hsz
                  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := dl
                  simp only at h0
                  subst h0
                  simp only [Proof.Loader.next, hbs, pairVal, rebuild_b32,
                    Option.some.injEq] at hld
                  subst hld
                  have := numPre_le3 Q (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)
                  exact Proof.Loader.Rng.of_readI _ (Proof.Raw.word32Of_b32 _) (by omega)
                by_cases h1 : dl.site = .ld1
                · unfold Proof.EvW.LdShapeW at hsh
                  rw [h1] at hsh
                  obtain ⟨ac, bs, rfl, hloc, hsz, -⟩ := hsh
                  have hbs := pair_read hp hX hget hw 1 (by rw [hloc]; simp) hsz
                  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := dl
                  simp only at h1
                  subst h1
                  simp only [Proof.Loader.next, hbs, pairVal, rebuild_b32,
                    Option.some.injEq] at hld
                  subst hld
                  obtain ⟨-, -, hz⟩ := Proof.ProA.cta_lt hp hg
                  have := numIters_lt31 hp hz (Proof.ProA.cta L g .x)
                  exact Proof.Loader.Rng.of_readN hrd rfl (Proof.Raw.word32Of_b32 _) (by omega)
                exact hrd.next h0 h1 hld
          | _ => trivial
      · trivial


/-- **A loader event has the loader's shape with its counter bounds** (`EvW.LdShape`: the ring
slot `i % 3` and its phase), from the table's shape and `ld_rng`. -/
theorem ld_shape (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hne : ¬ Ends e) {tm : Value}
    {d : Proof.Loader.D} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n))) :
    Proof.EvW.LdShape Q L g d e := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hJ := (good_all' hp hX hg k).2 _ hσ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  cases o with
  | none => exact absurd (fires_none_ends hf) hne
  | some u =>
    have hW : Proof.EvW.LdShapeW Q L g d e := frag_ev hp hg hJ hat hi hc hf
    have hR : Proof.Loader.Rng d := ld_rng hp hX hg k hlen _ hσ
    exact hW.shape (Proof.EvW.sbOk_of_pre hp) hR.bndI
end
end PTX.Kernels.InklingRelDecode.Proof2
