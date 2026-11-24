-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeInput
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof.Result.MmaOperand
public import Kernels.InklingRelDecode.Proof2.Lib.LoaderPage

@[expose] public section

/-!
# The loader's block-table words are the pages

The loader reads the two block-table words of an iteration (`ldb0`, `ldb1`) and keeps them in
`Loader.D.p0`, `p1`. `ldb_word` says what the bytes of such a read are: those of `Q.page` of the
slab, because the address (`EvW.ldBtAddr_spec`) is the table entry of a block below `num_iters`
and an input read returns the launch content (`input_word`). `loader_page` is the invariant along
the run: from the load on, `p0` (`p1`) is the page of the slab of the current iteration. It is the
`hpage` premise of `Result.Mma.loader_copy_spec`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The bytes of a block-table read.** At a loader state at `ldb0` or `ldb1` of an iteration
below `num_iters`, the read returns the bytes of the 32-bit word `Q.page` of the slab. -/
theorem ldb_word (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) {slab : Nat}
    (hs : (slab = 0 ∧ d.site = .ldb0) ∨ (slab = 1 ∧ d.site = .ldb1))
    (hi : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ pc ac bs, e = ⟨pc, .rd ac bs⟩ ∧
      bs = (b32 (slabPage Q L g d.i slab)).toBytes.map some := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨t, hgd, hfire⟩ := hF
  have hr := hf.reach hg hσ
  obtain ⟨t', ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  have hinv' : Loader.Inv L g d ∧ Loader.ProEq L g P d ∧ Worker.Rest L g P ∧
      4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := hinv.2
  have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
    ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hm : EvW.Words Q P := hr.1
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hblk := Result.Mma.blk_lt hpre.splitsPos hi
  have hsb := hpre.seqRange _ hz
  have hbl : Q.blocks (ProA.cta L g .z) < 2 ^ 24 := by
    unfold Params.blocks; omega
  have hsl : slab ≤ 1 := by omega
  have hsite : d.site = .ldb0 ∨ d.site = .ldb1 := by
    rcases hs with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hi31 : d.i < 2 ^ 31 :=
    (hf.ldRng hg hσ).bndI (by rcases hsite with h | h <;> rw [h] <;> rfl)
  have hidx : ProA.cta L g .z * Q.strideBt + (2 * (ProA.cta L g .x + d.i * Q.splits) + slab) <
      2 ^ 31 := hpre.btIndexRange _ hz _ (by omega)
  have haddr := EvW.ldBtAddr_spec hpre hg hm hinv'.2.1 slab hsl (by omega) (by omega)
  have hsr : 2 * (ProA.cta L g .x + d.i * Q.splits) + slab < 2 * Q.blocks (ProA.cta L g .z) := by
    omega
  have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
      (2 * (ProA.cta L g .x + d.i * Q.splits) + slab)) + j) :=
    fun j hj => .inr (.inr (.inr (.inr (.inr ⟨_, hz, _, hsr, j, hj, rfl⟩))))
  have hnw : (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
      (2 * (ProA.cta L g .x + d.i * Q.splits) + slab))) < 2 ^ 64 := by
    have := hpre.readsRange _ (hrd 0 (by omega))
    omega
  unfold EvW.LdShape at hsh
  rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [h] at hsh
    obtain ⟨ac, bs, he2, hloc, hsz⟩ := hsh
    refine ⟨_, ac, bs, he2, ?_⟩
    have hA : ac.loc = ⟨.global, 0, Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
        (2 * (ProA.cta L g .x + d.i * Q.splits) + 0))⟩ := by
      rw [hloc, haddr]
      congr 1
      omega
    exact input_word hpre hX hf (by rw [← he2]; exact he) hA hsz _ fun j hj =>
      ⟨hrd j hj, hpre.btInput _ hz _ hsr j hj⟩
  · rw [h] at hsh
    obtain ⟨ac, bs, he2, hloc, hsz⟩ := hsh
    refine ⟨_, ac, bs, he2, ?_⟩
    have hA : ac.loc = ⟨.global, 0, Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
        (2 * (ProA.cta L g .x + d.i * Q.splits) + 1))⟩ := by
      rw [hloc, haddr]
      congr 1
      omega
    exact input_word hpre hX hf (by rw [← he2]; exact he) hA hsz _ fun j hj =>
      ⟨hrd j hj, hpre.btInput _ hz _ hsr j hj⟩

/-! ### The invariant -/

/-! ### Along the run -/

/-- What the thread's state keeps: the loader's `LoaderPage`. -/
def PagePr (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .w (.loader d _) => LoaderPage Q L g d
  | _ => True

/-- **The dispatch enters the loader at its first site.** -/
theorem dispatch_loader {g : Nat} {e : Event} {P : Loader.Pro} {a : WComp.WSt}
    (h : WComp.dispatch L g P e = some (some a)) {d : Loader.D} {P' : Loader.Pro}
    (ha : a = .loader d P') : d.site = .setMaxDec := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    rcases (EvW.ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
      simp only [WComp.roleStart] at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [WComp.WSt.loader.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      rfl
    · split at h
      · split_ifs at h
        · simp only [Option.some.injEq] at h
          subst h
          cases ha
        · cases h
      · cases h
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
  · cases h
  · cases h

/-- **A composed worker step keeps `PagePr`.** -/
theorem page_wstep (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k : Nat} {e : Event}
    {s0 a : WComp.WSt} (he : X.get (g, k) = some e) (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.w s0))) (hi : PagePr Q L g (.w s0))
    (h : WComp.next L g s0 e = some (some a)) : PagePr Q L g (.w a) := by
  cases s0 with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨s, P⟩ := w
      simp only at hs
      subst hs
      cases a with
      | loader d' P' =>
        exact loaderPage_start (dispatch_loader (by simpa [WComp.next] using h) rfl)
      | _ => trivial
    · rw [EvW.next_worker_map hs] at h
      obtain ⟨w', hw, rfl⟩ := EvW.map_map_some h
      trivial
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_idle_map hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      trivial
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_loader_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      show LoaderPage Q L g d'
      change LoaderPage Q L g d at hi
      obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
      obtain ⟨t, hgd, hfire⟩ := hF
      have hr := hf.reach hg hσ
      obtain ⟨t', ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
      have hinv' : Loader.Inv L g d ∧ Loader.ProEq L g P d ∧ Worker.Rest L g P ∧
          4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := hinv.2
      have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
        ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
      by_cases h1 : d.site = .ld1
      · unfold EvW.LdShape at hsh
        rw [h1] at hsh
        obtain ⟨ac, bs, he2, hloc, hsz, -⟩ := hsh
        have hbs := hn (pc := Loader.Site.pc .ld1) (a := ac) (bs := bs)
          (by rw [← he2]; exact he) hσ h1 (by rw [hloc]) hsz
        exact lp_step_ld1 hi h1 he2 (numIters_lt hpre hg) hbs hd
      by_cases h2 : d.site = .ldb0
      · have hnN := hi.1 (by rw [h2]; rfl)
        have hlp : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
          rw [← hnN]; exact (hf.ldRng hg hσ).loop (by rw [h2]; rfl)
        obtain ⟨pc, ac, bs, he2, hbs⟩ := ldb_word hpre hX hf hg he hσ (slab := 0)
          (.inl ⟨rfl, h2⟩) hlp
        have hpg := slabPage_lt hpre hg hlp (slab := 0) (by norm_num)
        exact lp_step_ldb hi (.inl ⟨rfl, h2⟩) he2 (by omega) hbs hd
      by_cases h3 : d.site = .ldb1
      · have hnN := hi.1 (by rw [h3]; rfl)
        have hlp : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
          rw [← hnN]; exact (hf.ldRng hg hσ).loop (by rw [h3]; rfl)
        obtain ⟨pc, ac, bs, he2, hbs⟩ := ldb_word hpre hX hf hg he hσ (slab := 1)
          (.inr ⟨rfl, h3⟩) hlp
        have hpg := slabPage_lt hpre hg hlp (slab := 1) (by norm_num)
        exact lp_step_ldb hi (.inr ⟨rfl, h3⟩) he2 (by omega) hbs hd
      exact lp_step_other hi h1 h2 h3 hd
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_mma_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      trivial
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · have h' : some (some (WComp.WSt.exit ⟨.ret, P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · cases h

/-- **Every state keeps `PagePr`.** -/
theorem page_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g : Nat} :
    ∀ (k : Nat) (s : TSt), St Q L X g k = some (some s) → PagePr Q L g s := by
  refine stateAt_induction (PagePr Q L g) ?_ ?_
  · show PagePr Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> trivial
  · intro k e s s' he' hσ hi hnx
    have he : X.get (g, k) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    cases s with
    | d s0 =>
      rw [next_d] at hnx
      obtain ⟨a, -, h⟩ := map_map_eq_some_some hnx
      subst h
      trivial
    | w s0 =>
      rw [next_w] at hnx
      obtain ⟨a, ha, h⟩ := map_map_eq_some_some hnx
      subst h
      exact page_wstep hpre hX hf hn he hg hσ hi ha

/-- **The block-table word of a loader copy is the page of its slab** (the premise `hpage` of
`Result.Mma.loader_copy_spec`): at a loader state at one of the eight copy sites, with box
`(isV, slab, hh)`, the word `p0` (slab 0) or `p1` (slab 1) is the `Q.page` of the slab
`2 (split + i · num_splits) + slab`. -/
theorem loader_copy_page (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.loader d P)))) {b : Bool × Nat × Nat}
    (hb : EvW.ldBox d.site = some b) :
    (if b.2.1 = 0 then d.p0 else d.p1) =
      Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + d.i * Q.splits) + b.2.1) := by
  have hp : LoaderPage Q L g d := page_inv hpre hX hf hn k _ hσ
  obtain ⟨-, hp0, hp1⟩ := hp
  cases hs : d.site <;> rw [hs] at hb <;> simp only [EvW.ldBox, Option.some.injEq,
    reduceCtorEq] at hb
  all_goals
    subst hb
    first
      | exact hp0 (by rw [hs]; rfl)
      | exact hp1 (by rw [hs]; rfl)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
