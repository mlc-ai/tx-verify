-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Placed
public import Kernels.InklingRelDecode.Proof2.Lib.LoaderPage
public import Kernels.InklingRelDecode.Proof2.Ref.Input

@[expose] public section

/-! # The loader's block-table words are the pages

* `ww_inv`: every worker state carries the launch's parameter words in its inherited registers
  (`EvW.Words`): the startup hands the worker `workerPro`, whose words are the parameters modulo
  `2 ^ 32`, and every worker step keeps them (`EvW.next_keep`).
* `ldb_bytes`: a loader block-table load of an iteration below `num_iters` returns the 32-bit page
  of its slab (the address is the table entry, `EvW.ldBtAddr_spec`; an input read returns the
  launch's bytes, the read-only input assumption through `input_word'`).
* `ld_page`: every loader state has `Interface.LoaderPage` (from the read of `num_iters` on the
  bound is the CTA's `num_iters`, by `pair_read`; from each block-table load on its word is the
  page), and `ld_copy_page`: the word of a copy's slab is its page. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Interface (LoaderPage slabPage)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The parameter words of the workers -/

/-- The worker states' parameter words. -/
def WW (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), σ⟩, _) => Proof.EvW.Words Q (Proof.EvW.stPro σ)
  | _ => True

theorem words_keep {P P' : Proof.Loader.Pro} (h : Proof.EvW.Keep P P') (hw : Proof.EvW.Words Q P) :
    Proof.EvW.Words Q P' := by
  obtain ⟨h67, h68, h69, h70, h71, hbt, -⟩ := h
  obtain ⟨w67, w68, w69, w70, w71, wbt⟩ := hw
  exact ⟨h67.trans w67, h68.trans w68, h69.trans w69, h70.trans w70, h71.trans w71,
    hbt.trans wbt⟩

/-- **Every worker state carries the parameter words.** -/
theorem ww_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      WW Q L g σ := by
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
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'; cases hσ'
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hR0 := ih hlt.le σ hk0
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
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
          exact words_keep (Proof.EvW.next_keep hσw) hR0
      · exact ((good_all' hp hX hg k).2 _ hk0).elim

/-! ### The block-table loads -/

/-- **An input word read** by an access of any element index: the launch's bytes. -/
theorem input_word' (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc A x : Nat}
    {a : Acc} {bs : List (Option Byte)} (he : X.get i = some ⟨pc, .rd a bs⟩)
    (hs : Assumptions.inputReadSites.contains pc = true)
    (hloc : a.loc = ⟨.global, 0, A⟩) (hsz : a.size = 4)
    (hm : ∀ j < 4, m ⟨.global, 0, A + j⟩ = some (some ((b32 x).byteAt j))) :
    bs = (b32 x).toBytes.map some := by
  have hrd : X.MemReads (.thread i) a bs := Or.inl ⟨pc, he⟩
  have hlen : bs.length = 4 := by rw [← hsz]; exact (hX.rf _ _ _ hrd).1
  refine Frame.bytes_of_pointwise (by rw [hlen]; rfl) fun j hj => ?_
  have hj4 : j < 4 := by simpa [b32, Value.bytes] using hj
  exact (hX.asm _ inputReadOnly_mem) i pc a bs he hs j (by omega)
    _ (by simpa [Loc.at, hloc] using hm j hj4)

/-- The positions of the loader's two block-table loads are input read sites. -/
theorem ldb_sites : Assumptions.inputReadSites.contains Proof.Loader.Site.ldb0.pc = true ∧
    Assumptions.inputReadSites.contains Proof.Loader.Site.ldb1.pc = true := by decide

/-- **A block-table load of an iteration below `num_iters` returns the page of its slab.** -/
theorem ldb_bytes (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hne : ¬ Ends e) {tm : Value}
    {d : Proof.Loader.D} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)))
    {slab : Nat} (hs : (slab = 0 ∧ d.site = .ldb0) ∨ (slab = 1 ∧ d.site = .ldb1))
    (hi : d.i < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)) :
    ∃ pc ac bs, e = ⟨pc, .rd ac bs⟩ ∧
      bs = (b32 (slabPage Q L g d.i slab)).toBytes.map some := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have hpro : Proof.Loader.ProEq L g P d := (hinv : Proof.WComp.Inv L g (.loader d P)).2.1
  have hm : Proof.EvW.Words Q P := ww_inv hp hX hg k hlen.le _ hσ
  have hsh := ld_shape hp hX he hne hσ
  have hrg : Proof.Loader.Rng d := ld_rng hp hX hg k hlen _ hσ
  obtain ⟨hx, hy, hz⟩ := Proof.ProA.cta_lt hp hg
  have hblk := Proof.Result.Mma.blk_lt hp.splitsPos hi
  have hsb := hp.seqRange _ hz
  have hbl : Q.blocks (Proof.ProA.cta L g .z) < 2 ^ 24 := by
    unfold Params.blocks; omega
  have hsl : slab ≤ 1 := by omega
  have hsite : d.site = .ldb0 ∨ d.site = .ldb1 := by
    rcases hs with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hidx : Proof.ProA.cta L g .z * Q.strideBt +
      (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab) < 2 ^ 31 :=
    hp.btIndexRange _ hz _ (by omega)
  have haddr := Proof.EvW.ldBtAddr_spec hp hg hm hpro slab hsl (by omega) (by omega)
  have hsr : 2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab <
      2 * Q.blocks (Proof.ProA.cta L g .z) := by omega
  have hrd : ∀ j < 4, Q.reads (Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
      (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab)) + j) :=
    fun j hj => .inr (.inr (.inr (.inr (.inr ⟨_, hz, _, hsr, j, hj, rfl⟩))))
  have hnw : (Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
      (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + slab))) < 2 ^ 64 := by
    have := hp.readsRange _ (hrd 0 (by omega))
    omega
  unfold Proof.EvW.LdShape at hsh
  rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [h] at hsh
    obtain ⟨ac, bs, he2, hloc, hsz⟩ := hsh
    refine ⟨_, ac, bs, he2, ?_⟩
    have hA : ac.loc = ⟨.global, 0, Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
        (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + 0))⟩ := by
      rw [hloc, haddr]
      congr 1
      omega
    rw [he2] at he
    exact input_word' hX he ldb_sites.1 hA hsz fun j hj =>
      hp.btInput _ hz _ hsr j hj
  · rw [h] at hsh
    obtain ⟨ac, bs, he2, hloc, hsz⟩ := hsh
    refine ⟨_, ac, bs, he2, ?_⟩
    have hA : ac.loc = ⟨.global, 0, Q.btBase + 4 * (Proof.ProA.cta L g .z * Q.strideBt +
        (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + 1))⟩ := by
      rw [hloc, haddr]
      congr 1
      omega
    rw [he2] at he
    exact input_word' hX he ldb_sites.2 hA hsz fun j hj =>
      hp.btInput _ hz _ hsr j hj


/-! ### The page invariant -/

/-- The loader states' page invariant. -/
def LP (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.worker _), .loader d _⟩, _) => LoaderPage Q L g d
  | _ => True

/-- **Every loader state has its page invariant.** -/
theorem ld_page (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      LP Q L g σ := by
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
            show LoaderPage Q L g d'
            rcases w_next_loader hσw with hst | ⟨dl, rfl, hne, hld⟩
            · exact Proof.Interface.loaderPage_start hst
            · have hi : LoaderPage Q L g dl := hR0
              have hget : X.get (g, k) = some e := he
              have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
              have hrg : Proof.Loader.Rng dl := ld_rng hp hX hg k hlt _ hk0
              by_cases h1 : dl.site = .ld1
              · have hsh := ld_shape hp hX hget hnE hk0
                unfold Proof.EvW.LdShape at hsh
                rw [h1] at hsh
                obtain ⟨ac, bs, he2, hloc, hsz, -⟩ := hsh
                have hw : 128 ≤ g % L.block := by
                  have : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlt _ hk0).2
                  omega
                have hbs := pair_read hp hX (he2 ▸ hget) hw 1 (by rw [hloc]; simp) hsz
                exact Proof.Interface.lp_step_ld1 hi h1 he2 (by
                  have := numIters_lt31 hp (Proof.ProA.cta_lt hp hg).2.2 (Proof.ProA.cta L g .x)
                  omega) hbs hld
              by_cases h2 : dl.site = .ldb0
              · have hnN := hi.1 (by rw [h2]; rfl)
                have hlp : dl.i < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) := by
                  rw [← hnN]; exact hrg.loop (by rw [h2]; rfl)
                obtain ⟨pc, ac, bs, he2, hbs⟩ := ldb_bytes hp hX hget hnE hk0 (slab := 0)
                  (.inl ⟨rfl, h2⟩) hlp
                have hpg := Proof.Interface.slabPage_lt hp hg hlp (slab := 0) (by norm_num)
                exact Proof.Interface.lp_step_ldb hi (.inl ⟨rfl, h2⟩) he2 (by omega) hbs hld
              by_cases h3 : dl.site = .ldb1
              · have hnN := hi.1 (by rw [h3]; rfl)
                have hlp : dl.i < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) := by
                  rw [← hnN]; exact hrg.loop (by rw [h3]; rfl)
                obtain ⟨pc, ac, bs, he2, hbs⟩ := ldb_bytes hp hX hget hnE hk0 (slab := 1)
                  (.inr ⟨rfl, h3⟩) hlp
                have hpg := Proof.Interface.slabPage_lt hp hg hlp (slab := 1) (by norm_num)
                exact Proof.Interface.lp_step_ldb hi (.inr ⟨rfl, h3⟩) he2 (by omega) hbs hld
              exact Proof.Interface.lp_step_other hi h1 h2 h3 hld
          | _ => trivial
      · exact hJ.elim

/-- **The block-table word of a loader copy is the page of its slab.** -/
theorem ld_copy_page (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} (hk : k < (X.tr g).length) (hg : g < L.threads) {tm : Value} {d : Proof.Loader.D}
    {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)))
    {b : Bool × Nat × Nat} (hb : Proof.EvW.ldBox d.site = some b) :
    (if b.2.1 = 0 then d.p0 else d.p1) =
      Q.page (Proof.ProA.cta L g .z) (2 * (Proof.ProA.cta L g .x + d.i * Q.splits) + b.2.1) := by
  have hpg : LoaderPage Q L g d := ld_page hp hX hg k hk _ hσ
  obtain ⟨-, hp0, hp1⟩ := hpg
  cases hs : d.site <;> rw [hs] at hb <;> simp only [Proof.EvW.ldBox, Option.some.injEq,
    reduceCtorEq] at hb
  all_goals
    subst hb
    first
      | exact hp0 (by rw [hs]; rfl)
      | exact hp1 (by rw [hs]; rfl)
end
end PTX.Kernels.InklingRelDecode.Proof2
