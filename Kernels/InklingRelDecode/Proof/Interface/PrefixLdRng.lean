-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPremises
public import Kernels.InklingRelDecode.Proof.Interface.Lk2NumPre
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof2.Safety.LdRng
public import Kernels.InklingRelDecode.Proof.Interface.FootTrack
public import Kernels.InklingRelDecode.Proof.Interface.InputRead
public import Kernels.InklingRelDecode.Proof.Thread.LoaderRng

@[expose] public section

/-!
# The loader's counter bounds, and `Premises`

The loader's machine follows every word its `(num_pre, num_iters)` load returns
(`Loader.next`), so its counter bounds (`Loader.Rng`: the counters below `2 ^ 31`, the counter
below `num_iters` in the loop) are not facts of the machine. In an execution where the two reads
return the launch's words (`NumPreRead`, `NumWordRead`) they hold at every loader state
(`ldRng_of_reads`): the first state has no counter, the two loads give words below `2 ^ 31`
(`num_pre ≤ 3`, `num_iters < 2 ^ 31`), and every other step keeps the bounds (`Loader.Rng.next`).

The two read facts are proved (`numPreRead_of_p2`, `numWordRead_of_p2`) on the second tree's
role table (`Proof2.pair_read`), with no use of the counter bounds: the copies of a loader at any
counter land below the end of the rings or wrap to the top of the 32-bit space
(`Proof2.async_write_loc`), never on the two words. So `premises_of_prefix` builds `Premises`,
with its field `ldRng`, from the tracking and
`TmplOk`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `num_iters` is below `2 ^ 31`: the iterations are at most the request's blocks plus one, and
the sequence is below `2 ^ 31` (`Pre.seqRange`). -/
theorem numIters_lt31 (hpre : Pre Q L mem0) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s < 2 ^ 31 :=
  Proof2.numIters_lt31 hpre hr s

/-- **The loader's counter bounds**, from the two reads of `(num_pre, num_iters)`. -/
theorem ldRng_of_reads (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hP : NumPreRead Q L X)
    (hN : NumWordRead Q L X) : LdRng Q L X := by
  intro g k0 d0 P0 hg0 hσ0
  have key := stateAt_induction (Q := Q) (L := L) (X := X) (g := g)
    (fun s => ∀ d P, s = .w (.loader d P) → Loader.Rng d) ?_ ?_ k0 _ hσ0 d0 P0 rfl
  · exact key
  · intro d P h
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = _ at h
    split at h <;> cases h
  · intro k e s s' he' hσ hI hn d' P' hs'
    subst hs'
    have he : X.get (g, k) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    cases s with
    | d s0 =>
      rw [next_d] at hn
      obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
      cases h
    | w s0 =>
      rw [next_w] at hn
      obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
      cases h
      rcases Proof2.w_next_loader ha with hst | ⟨d, rfl, hne, hld⟩
      · have h1 : d'.site.iBounded = false := by
          simp [hst, Loader.Site.iBounded, Loader.Site.bounded, Loader.Site.inLoop]
        have h2 : d'.site.bounded = false := by
          simp [hst, Loader.Site.bounded, Loader.Site.inLoop]
        have h3 : d'.site.inLoop = false := by simp [hst, Loader.Site.inLoop]
        exact ⟨fun h => by simp [h1] at h, fun h => by simp [h2] at h,
          fun h => by simp [h3] at h, fun h => by simp [h1] at h, fun h => by simp [h2] at h⟩
      · have hrd := hI d P' rfl
        -- the event of the step, for the two loads
        obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
        obtain ⟨t, hgd, hfire⟩ := hF
        have hr := treach_stateAt hpre hg hσ
        have hsh := EvW.loader_shapeW hpre hr.2 (d := d) (P := P') (u := u)
          ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
        by_cases h0 : d.site = .ld0
        · unfold EvW.LdShapeW at hsh
          rw [h0] at hsh
          obtain ⟨ac, bs, rfl, hloc, hsz, -⟩ := hsh
          have hbs := hP he hσ h0 hloc hsz
          obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
          simp only at h0
          subst h0
          simp only [Loader.next, hbs, rebuild_b32, Option.some.injEq] at hld
          subst hld
          have := Proof2.numPre_le3 Q (ProA.cta L g .z) (ProA.cta L g .x)
          exact Loader.Rng.of_readI _ (Raw.word32Of_b32 _) (by omega)
        by_cases h1 : d.site = .ld1
        · unfold EvW.LdShapeW at hsh
          rw [h1] at hsh
          obtain ⟨ac, bs, rfl, hloc, hsz, -⟩ := hsh
          have hbs := hN he hσ h1 (by rw [hloc]) hsz
          obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
          simp only at h1
          subst h1
          simp only [Loader.next, hbs, rebuild_b32, Option.some.injEq] at hld
          subst hld
          obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
          have := numIters_lt31 hpre hz (ProA.cta L g .x)
          exact Loader.Rng.of_readN hrd rfl (Raw.word32Of_b32 _) (by omega)
        exact hrd.next h0 h1 hld

/-- `GoodP` at every present event of an execution whose machines follow every thread. -/
theorem goodP_of_tracked (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L Q) X) : ∀ e, Present X e → GoodP Q L mem0 X e := by
  rintro ⟨g, k⟩ ⟨ev, hev⟩ j -
  exact ⟨ht g (j + 1) (Frame.lt_of_get hX hev), launchRead_of_wf hpre hX _⟩

/-- **`Premises` from the tracking** and `TmplOk`: the loader's counter bounds from the two reads
and the roles by warp from the role bytes. -/
theorem premises_of_prefix (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (ht : Frame.Tracked (code L Q) X) :
    Premises Q L X := by
  have hS := sound_all hpre smOb
  exact premises_of_tracked ht hT (ldRng_of_reads hpre hX hS hT
    (numPreRead_of_p2 hpre hX) (numWordRead_of_p2 hpre hX))
    (roleWarp_of_reads hpre hX hS (roleReads_of_p2 hpre hX))

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
