-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTileDefs

@[expose] public section

/-! # The tile of each consumer task

A consumer's tasks are numbered by its successful response polls (`epoch`): its first task is
its CTA's own tile, and task `E > 0` is the tile of the CTA claimed by the response it read right
after its poll numbered `E - 1` (`TileAt`, `ReadClaim`). Along its run the consumer holds that tile
in `(m, n)`; from its queries on, the claimed CTA in `x`; from its group barrier on, the next tile
in `(m', n')` (`TileRel`, a conjunct of the consumer's run invariant). The task's commit then moves
to the next tile, the claimed one, or leaves when nothing is claimed. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The tiles along a consumer's run.** -/
def TileRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (d.site = .setMaxReg → okPolls (clcResp L g) es = 0) ∧
  (d.site ≠ .setMaxReg → TileAt L g es (epoch L g d es) d.m d.n) ∧
  (1 ≤ d.clcStage → okPolls (clcResp L g) (es.take (es.length - d.clcStage)) + 1 =
    okPolls (clcResp L g) es) ∧
  (d.afterQuery = true → ReadClaim L g es (okPolls (clcResp L g) es - 1) d.x) ∧
  (d.afterBar = true → d.m' = (nextTile d).1 ∧ d.n' = (nextTile d).2) ∧
  (∀ k, d.site = .fence k ∨ d.site = .tma k → first L g = true)

/-- The response the latest successful poll's read holds, as the queries see it. -/
theorem query_claim {es : List Event} {n : Nat} {rr : ClcResponse}
    (hq : QueryRel L g n (.clc rr) es) (hn : 2 ≤ n)
    (hc : okPolls (clcResp L g) (es.take (es.length - n)) + 1 = okPolls (clcResp L g) es) :
    ReadClaim L g es (okPolls (clcResp L g) es - 1)
      ((rr.firstCta.map fun c => c.1.toNat).getD Loader.none32) := by
  obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr', hjn, hj, hj1, -, -, hrr, hv⟩ := hq.2 hn
  cases hv
  refine ⟨j, pc, p, acq, sc, pcr, a, bs, rr, hj, ?_, hj1, hrr, rfl⟩
  rw [show es.length - n = j by omega] at hc
  omega

/-- A consumer's event other than at its response poll is no successful response poll. -/
theorem not_okPoll (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hs : d.site ≠ .clcWait) :
    okPoll (clcResp L g) e = false := by
  cases hp : okPoll (clcResp L g) e
  · rfl
  · obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form hp
    exact absurd ((clc_sites hpre hg hi h hc hf).1 p true acq sc hk).1 hs

/-- A step that keeps the tile, the claimed CTA and the next tile, away from the response
poll. -/
theorem TileRel.frame {d d' : D} {pre : List Event} {e : Event} (hq : TileRel L g d pre)
    (hp : okPoll (clcResp L g) e = false) (hs : d.site ≠ .setMaxReg) (hs' : d'.site ≠ .setMaxReg)
    (hw : d.site ≠ .clcWait) (hw' : d'.site ≠ .clcWait) (hm : d'.m = d.m) (hn : d'.n = d.n)
    (hx : d'.x = d.x) (hm' : d'.m' = d.m') (hn' : d'.n' = d.n')
    (hq1 : d'.afterQuery = true → d.afterQuery = true)
    (hb1 : d'.afterBar = true → d.afterBar = true) (hst : d'.clcStage = 0)
    (h6 : ∀ k, d'.site = .fence k ∨ d'.site = .tma k → first L g = true) :
    TileRel L g d' (pre ++ [e]) := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := hq
  have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
    rw [okPolls_snoc, hp]; simp
  have hep : epoch L g d' (pre ++ [e]) = epoch L g d pre := by
    simp only [epoch, hw, hw', ↓reduceIte, hpo]
  refine ⟨fun h => absurd h hs', fun _ => ?_, fun h => by rw [hst] at h; omega, fun h => ?_,
    fun h => ?_, ?_⟩
  · rw [hep, hm, hn]; exact (h2 hs).snoc e
  · rw [hpo, hx]; exact (h4 (hq1 h)).snoc e
  · have := h5 (hb1 h)
    simp only [nextTile, hm, hn, hx, hm', hn'] at this ⊢
    exact this
  · exact h6

set_option maxHeartbeats 8000000 in
/-- **One step of a consumer's run keeps its tiles.** -/
theorem tileRel_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event} (hi : Inv d)
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : TileRel L g d pre) (hqr : QueryRel L g d.clcStage d.resp pre) :
    TileRel L g d' (pre ++ [e]) := by
  have h : Holds t.regs (facts L g d) := hat.2.2.2.2
  have hqs := fun {q : ClcQuery} {r : ClcResponse} (hk : e.kind = .clcQuery q r) =>
    query_site hat hc hf hk
  have hp : d.site ≠ .clcWait → okPoll (clcResp L g) e = false :=
    not_okPoll hpre hg hi h hc hf
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case setMaxReg =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hpo : okPolls (clcResp L g) (pre ++ [e]) = 0 := by
      rw [okPolls_snoc, hp (by simp), hq.1 rfl]; simp
    refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
      fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
        simp at hk⟩
    simp only [epoch, ↓reduceIte, hpo]
    exact .inl ⟨rfl, rfl, rfl⟩
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl h hc hf
    simp only [next] at hn
    have hloc : (⟨.shared, g / L.block, L.sharedBase + 104⟩ : Loc) = clcResp L g := rfl
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;> subst hn
    · have hpo : okPolls (clcResp L g) (pre ++ [⟨Site.clcWait.pc, .wait ⟨.shared, g / L.block,
          L.sharedBase + 104⟩ p false acq sc⟩]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, okPoll_wait rfl]; simp
      obtain ⟨h1, h2, -, -, -, -⟩ := hq
      refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
        fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
          simp at hk⟩
      simp only [epoch, ↓reduceIte, hpo]
      exact (h2 (by simp)).snoc _
    · have hpo : okPolls (clcResp L g) (pre ++ [⟨Site.clcWait.pc, .wait ⟨.shared, g / L.block,
          L.sharedBase + 104⟩ p true acq sc⟩]) = okPolls (clcResp L g) pre + 1 := by
        rw [okPolls_snoc, okPoll_wait rfl, hloc]; simp
      obtain ⟨h1, h2, -, -, -, -⟩ := hq
      refine ⟨fun h => by simp at h, fun _ => ?_, fun _ => ?_,
        fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
          simp at hk⟩
      · simp only [epoch, hpo]
        have := (h2 (by simp)).snoc
          ⟨Site.clcWait.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p true acq sc⟩
        simp only [epoch, ↓reduceIte, Nat.sub_zero] at this
        simpa [D.clcStage] using this
      · simp only [D.clcStage, List.length_append, List.length_singleton, Nat.add_sub_cancel,
          List.take_left', hpo]
  case clcLoad =>
    simp only [next] at hn
    split at hn
    · simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, -, rfl⟩ := hn
      have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, hp (by simp)]; simp
      obtain ⟨h1, h2, h3, -, -, -⟩ := hq
      refine ⟨fun h => by simp at h, fun _ => ?_, fun _ => ?_,
        fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
          simp at hk⟩
      · simpa [epoch, hpo] using (h2 (by simp)).snoc e
      · have h3' := h3 (by simp [D.clcStage])
        simp only [D.clcStage] at h3' ⊢
        rw [hpo, ← h3', List.length_append, List.length_singleton,
          List.take_append_of_le_length (by omega), show pre.length + 1 - 2 = pre.length - 1 by
            omega]
    · cases hn
  case clcStatus =>
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, hp (by simp)]; simp
      obtain ⟨h1, h2, h3, -, -, -⟩ := hq
      have he2 : TileAt L g (pre ++ [e]) (epoch L g ⟨.clcStatus, mm, n, m', n', cp, ap, resp, x,
        acc, base⟩ pre) mm n :=
        (h2 (by simp)).snoc e
      split_ifs with hfc
      · refine ⟨fun h => by simp at h, fun _ => ?_, fun _ => ?_,
          fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
            simp at hk⟩
        · simpa [epoch, hpo] using he2
        · have h3' := h3 (by simp [D.clcStage])
          simp only [D.clcStage] at h3' ⊢
          rw [hpo, ← h3', List.length_append, List.length_singleton,
            List.take_append_of_le_length (by omega),
            show pre.length + 1 - 3 = pre.length - 2 by omega]
      · refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
          fun _ => ?_, fun h => by simp [D.afterBar] at h, fun k hk => by simp at hk⟩
        · simpa [epoch, hpo] using he2
        · obtain ⟨-, hr⟩ := hqs hk
          obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, -, -, -, -, -, -, hv⟩ := hqr.2 (le_refl 2)
          simp only at hv
          subst hv
          have hrr := hr rr rfl
          subst hrr
          have hnone : r.firstCta = none := by
            cases hh : r.firstCta
            · rfl
            · simp [hh] at hfc
          have hcl := query_claim (n := 2) hqr (le_refl 2) (h3 (by simp [D.clcStage]))
          rw [hnone] at hcl
          rw [hpo]
          exact hcl.snoc e
    · cases hn
  case clcFirst =>
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, hp (by simp)]; simp
      obtain ⟨h1, h2, h3, -, -, -⟩ := hq
      refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
        fun _ => ?_, fun h => by simp [D.afterBar] at h, fun k hk => by simp at hk⟩
      · simpa [epoch, hpo] using (h2 (by simp)).snoc e
      · obtain ⟨-, hr⟩ := hqs hk
        obtain ⟨j, pc, p, acq, sc, pcr, a, bs, rr, -, -, -, -, -, -, hv⟩ :=
          hqr.2 (by simp [D.clcStage])
        simp only at hv
        subst hv
        have hrr := hr rr rfl
        subst hrr
        rw [hpo]
        exact (query_claim (n := 3) hqr (by omega) (h3 (by simp [D.clcStage]))).snoc e
    · cases hn
  case clcBar =>
    simp only [next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
    · exact TileRel.frame hq (hp (by simp)) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl rfl
        rfl (by simp [D.afterQuery]) (by simp [D.afterBar]) (by simp [D.clcStage])
        (fun k hk => by simp at hk)
    · have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, hp (by simp)]; simp
      obtain ⟨-, h2, -, h4, -, -⟩ := hq
      refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
        fun _ => ?_, fun _ => ⟨rfl, rfl⟩, fun k hk => by simp at hk⟩
      · simpa [epoch, hpo] using (h2 (by simp)).snoc e
      · rw [hpo]; exact (h4 rfl).snoc e
  case ack =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
      rw [okPolls_snoc, hp (by simp)]; simp
    obtain ⟨-, h2, -, h4, -, -⟩ := hq
    refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
      fun _ => ?_, fun _ => ⟨rfl, rfl⟩, fun k hk => by simp at hk⟩
    · simpa [epoch, hpo] using (h2 (by simp)).snoc e
    · rw [hpo]; exact (h4 rfl).snoc e
  case commit k =>
    simp only [next] at hn
    split_ifs at hn with hk hx <;> simp only [Option.some.injEq] at hn <;> subst hn
    · exact TileRel.frame hq (hp (by simp)) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl rfl
        rfl (by simp [D.afterQuery]) (by simp [D.afterBar]) (by simp [D.clcStage])
        (fun k hk => by simp at hk)
    · exact TileRel.frame hq (hp (by simp)) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl rfl
        rfl (by simp [D.afterQuery]) (by simp [D.afterBar]) (by simp [D.clcStage])
        (fun k hk => by simp at hk)
    · have hpo : okPolls (clcResp L g) (pre ++ [e]) = okPolls (clcResp L g) pre := by
        rw [okPolls_snoc, hp (by simp)]; simp
      obtain ⟨-, -, -, h4, h5, -⟩ := hq
      have hr := h4 rfl
      obtain ⟨hm', hn'⟩ := h5 rfl
      simp only [nextTile, hx, ↓reduceIte] at hm' hn'
      refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp [D.clcStage] at h,
        fun h => by simp [D.afterQuery] at h, fun h => by simp [D.afterBar] at h, fun k hk => by
          simp at hk⟩
      simp only [epoch, ↓reduceIte, Nat.sub_zero, hpo]
      exact .inr ⟨x, by have := hr.lt; omega, hr.snoc e, hx, hm', hn'⟩
  all_goals simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals first
    | (simp only [Option.some.injEq] at hn
       subst hn
       exact TileRel.frame hq (hp (by simp)) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl
        rfl rfl (by simp [D.afterQuery]) (by simp [D.afterBar]) (by simp [D.clcStage])
        (by first
          | (intro k _; assumption)
          | (intro k _; exact hq.2.2.2.2.2 _ (.inl rfl))
          | (intro k hk; simp at hk)))
    | cases hn


end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
