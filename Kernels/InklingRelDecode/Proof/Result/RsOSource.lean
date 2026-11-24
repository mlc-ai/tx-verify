-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RsEpiLoad
public import Kernels.InklingRelDecode.Proof.Interface.RsMmaBack
public import Kernels.InklingRelDecode.Proof.Interface.RsElect
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Kernels.InklingRelDecode.Proof.Result.OutLoad

@[expose] public section

/-!
# The epilogue's `O` load reads the last PV MMA (`Out.Inputs.oSource`)

The statement `OSource` is `Out.Inputs.oSource` for the epilogue's own load event, the event that
the state at the load's site (`Epi.Site.ld`) fires (`RsEpiLoad`): in `Inputs.oSource` as it stands
the event index `k0` is free, so the statement also names the softmax region's rescale loads, whose
read source is an earlier PV MMA (`Out.ld_event'` and the file header of `RsEpiLoad.lean`).

The proof follows the epilogue's poll of `o_final` to the commit it observes (`SO.fObj`), the
MMA warp's state at that commit (`Interface.mma_event_state`, the site `finCommit`), the end of the
loop (`Interface.fin_iter`: iteration `num_iters + 1`) and back to PV step 7 of the last iteration
(`Interface.exists_pv7`). That MMA is `DoneBefore` the epilogue's load (`SO.f_doneBefore`), writes
each cell of the load (`Out.taddr_cell`, `Mma.pv_writeCell`), and every other writer of the cell is
before it: the other PV MMAs of the lane by program order (none follows it: the states between it
and the commit are past the PV half of the last iteration, `exists_pv7`'s chain, and every MMA
precedes the commit), the rescale stores by `Sr.pv_ost_B` (iteration `i < num_iters`), the QK
MMAs and the `P` stores in other columns.

Premises: `Sr.SrPkg`, `Pr.MmaStates`, `Tmem1.Tmem1Facts`, `SO.TmemLife`, the reads-from facts
`BaseWordRead` and `NumWordRead` (the words the MMA warp reads: `Interface.mma_tm`,
`mma_iters`), and `OSrcPrem` (the MMA lane's role-table facts, the epilogue's base word and the
iteration bound of the rescale stores): rows in the development notes.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InO InP TmOk)

noncomputable section

variable {Q : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution}

/-- **The premises of `OSource`** beyond the handshake's (`SrPkg`, `MmaStates`):
* `commit_once`, `mma_before`: the MMA lane commits to `o_final` once, after every MMA of its CTA
  (the role table gives the MMA warp one run: `SO.f_doneBefore`'s `hcommit`, `hbefore`);
* `epiTm`: the epilogue's Tensor Memory base is the allocation's, 0 (the default partition's copy
  of the base word `BaseWordRead` speaks of: the thread layer tracks it for the workers
  (`Interface.words_inv`) but not for the default partition);
* `ostBound`: the iteration of a rescale store is below the thread's `num_iters` (the softmax
  region's loop counter, `Sm.Inv.late`). -/
structure OSrcPrem (Q : Params) (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0)
    (X : Execution) (G : SrPkg L K A mem0 X) : Prop where
  commit_once : ∀ c, c < L.grid → ∀ {i pc : Nat} {sp : TcCommit.Spec},
    X.get (G.cm c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c →
      ((X.tr (G.cm c)).take i).countP (commitsTo (EvW.oFinal L c)) = 0
  mma_before : ∀ c, c < L.grid → ∀ {x : EvId}, IsMma X x → x.1 / L.block = c →
    ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (G.cm c, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c → x.2 < i
  epiTm : ∀ {g k : Nat} {d : Epi.D}, g < L.threads →
    St Q L X g k = some (some (.d (.epi d))) → d.pr.tm = 0
  ostBound : ∀ c, c < L.grid → ∀ {t sk i a : Nat} {vals : List Value} {sh : TcShape},
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk i a vals sh →
      i < Q.numIters (reqOf L t) (splitOf L t)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **A commit to `o_final` is at the site `finCommit`.** -/
theorem site_of_commit {g : Nat} {d : Mma.D} {pc : Nat} {sp : TcCommit.Spec}
    (hsh : EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = EvW.oFinal L (g / L.block)) : d.site = .finCommit := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [EvW.MmShape] at hsh
  case finCommit => rfl
  case qkCommit =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.sReady_ne_oFinal (by omega))
  case pvCommit1 =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm (SO.kvEmpty_ne_oFinal (by omega))
  case pvCommit2 =>
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
    obtain ⟨-, rfl⟩ := hsh
    exact absurd hm SO.oDone_ne_oFinal
  all_goals first
    | (simp only [Event.mk.injEq] at hsh; simp at hsh; done)
    | (obtain ⟨_, _, hh, -⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | (obtain ⟨_, _, _, _, _, _, hh⟩ := hsh; simp only [Event.mk.injEq] at hh; simp at hh; done)
    | skip

/-- The number of blocks of a split is at most `2147483646`, the bound the MMA warp's loop test
needs. -/
theorem numIters_le (hpre : Pre Q L mem0) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s ≤ 2147483646 := by
  have h1 := hpre.seqRange r hr
  have hsp := hpre.splitsPos
  unfold Params.numIters Params.blocks
  have := ceil_div_le ((Q.seqK r + 127) / 128 - s) Q.splits hsp
  omega

/-- An MMA-warp state past the PV half of the last iteration issues no QK or PV MMA. -/
theorem past_not_mma {N : Nat} {d : Mma.D} (hI : Mma.Inv d) (hp : Interface.Past N d)
    (hn : d.n = N) (hs : (∃ j, d.site = .qk j) ∨ ∃ j, d.site = .pv j) : False := by
  unfold Interface.Past at hp
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · have := (hI.qk (by rw [hj]; trivial)).1
    rcases hp with hp | ⟨hp, -⟩ <;> omega
  · have := (hI.pv (by rw [hj]; trivial)).2.1
    rcases hp with hp | ⟨-, hp⟩
    · omega
    · rcases hp with hp | hp <;> rw [hj] at hp <;> cases hp

/-- **The last PV MMA of a CTA.** The facts of the MMA lane at the `o_final` commit an epilogue
thread's poll observed: the lane's state at the last PV MMA (step 7 of iteration `num_iters`) and
that every MMA of the CTA is that MMA or before it. -/
structure LastPv (Q : Params) (L : Launch) (X : Execution) (cm c n : Nat) : Prop where
  cm_ok : cm < L.threads ∧ cm / L.block = c
  pv7 : ∃ (k' : Nat) (d' : Mma.D) (P : Loader.Pro) (pc dst : Nat) (sp : OperandSpec)
      (acc : Bool) (mask : List Nat),
    St Q L X cm k' = some (some (.w (.mma d' P))) ∧ d'.site = .pv 7 ∧ d'.i = n ∧
      X.get (cm, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ ∧
      ∀ x : EvId, IsMma X x → x.1 / L.block = c → x.1 = cm ∧ x.2 ≤ k'

/-- **The poll observes the commit that follows the last PV MMA.** For an epilogue thread `h` of
CTA `c` at a successful poll of `o_final` and `num_iters ≥ 1`. -/
theorem last_pv (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X) (G : SrPkg L kernel Assumptions.all mem0 X)
    (R : OSrcPrem Q L kernel Assumptions.all mem0 X G) {c : Nat} (hcl : c < L.grid)
    {h j pc : Nat} {sc : MbarScope} (hhg : h < L.threads) (hhc : h / L.block = c)
    (he : X.get (h, j) = some ⟨pc, .wait (EvW.oFinal L c) 0 true true sc⟩)
    (hN : 1 ≤ Q.numIters (reqOf L h) (splitOf L h)) :
    LastPv Q L X (G.cm c) c (Q.numIters (reqOf L h) (splitOf L h)) := by
  have l := G.lane c hcl
  have F := (G.ctx c hcl).facts
  have hq : okPolls (EvW.oFinal L c) ((X.tr h).take j) + 0 =
      okPolls (EvW.oFinal L c) ((X.tr h).take j) := rfl
  obtain ⟨i, pcx, sp, rank, hget, hmbar, -⟩ :=
    (SO.fObj hX F).observes hX (SO.fReach hX F h (R.commit_once c hcl)) he hq
  have hcm := l.cm_ok.1
  obtain ⟨dc, Pc, hσc, hsh⟩ := Interface.mma_event_state hpre hX hf.sound hf.tracked hcm hget
    (Or.inr ⟨sp, rfl⟩)
  have hsite : dc.site = .finCommit :=
    site_of_commit hsh (by rw [l.cm_ok.2]; exact hmbar)
  have hik : i < (X.tr (G.cm c)).length := len_of_get hget
  have hreq := cta_eq (L := L) (g := G.cm c) (g' := h) (by rw [l.cm_ok.2, hhc])
  have hN' : dc.n = Q.numIters (reqOf L h) (splitOf L h) := by
    rw [hreq.1, hreq.2.1]
    exact Interface.mma_iters hpre hX hf hb hn (m := (G.cm c, i)) ⟨Pc, hσc⟩
      (by rw [hsite]; nofun) (by rw [hsite]; nofun)
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hhg
  have hle : Q.numIters (reqOf L h) (splitOf L h) ≤ 2147483646 :=
    numIters_le hpre hz (splitOf L h)
  have hlead : ElectLead L (G.cm c) (X.tr (G.cm c)) :=
    Interface.lead_of_finCommit hX hik hσc hsite
  have hbc : Mma.BcastRun (X.tr (G.cm c)) := Interface.bcast_of_mma hf.roleWarp hB hcm hik.le hσc
  have hdi : dc.i = dc.n + 1 :=
    Interface.fin_iter hX hlead i hik hσc (Or.inr (Or.inr (Or.inl hsite)))
      (by omega) (by omega)
  obtain ⟨k', d', hlt, hσ', hs7, hi7, htm, hn7, hev, hch⟩ :=
    Interface.exists_pv7 hpre hX hf hlead hbc (i0 := dc.n) (by omega) i hik hσc
      (Or.inl (by omega))
  refine ⟨⟨hcm, l.cm_ok.2⟩, k', d', Pc, ?_⟩
  obtain ⟨pcm, dst, sp7, acc, mask, hevm⟩ := hev
  refine ⟨pcm, dst, sp7, acc, mask, hσ', hs7, by rw [hi7, hN'], hevm, ?_⟩
  intro x hx hxc
  have hxt : x.1 = G.cm c := l.mma_thread hx hxc
  refine ⟨hxt, ?_⟩
  by_contra hgt
  have hgt' : k' < x.2 := by omega
  have hxi := R.mma_before c hcl hx hxc hget hmbar
  obtain ⟨pcx', dx, sx, ax, mx, hxget⟩ := hx.get
  have hxg : X.get (G.cm c, x.2) = some ⟨pcx', .tc (.mma dx sx ax mx)⟩ := by
    rw [← hxt]; exact hxget
  obtain ⟨dj, hdj, hpj, hnj⟩ := hch x.2 hgt' (by omega)
  rcases Result.Mma.mma_event_cases hpre hX hf hcm hxg with
    ⟨d'', P'', j'', hσ'', hI'', hs'', -⟩ | ⟨d'', P'', j'', hσ'', hI'', hs'', -⟩
  all_goals
    have hdd : d'' = dj := by
      have := Option.some.inj (Option.some.inj (hσ''.symm.trans hdj))
      simp only [Interface.TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
  · exact past_not_mma hI'' hpj (by rw [hnj]) (.inl ⟨j'', hs''⟩)
  · exact past_not_mma hI'' hpj (by rw [hnj]) (.inr ⟨j'', hs''⟩)

/-- **`Out.Inputs.oSource`, for the epilogue's own load.** For the load of a valid row's epilogue
(the event at the state at the load's site, with the registers of the state that holds its words),
the last PV MMA of the CTA (the state of step 7 of iteration `num_iters`) is the read source of
each of the 64 cells it reads, and the epilogue's Tensor Memory base is the MMA warp's. -/
def OSource (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k k0 pc : Nat} {d d0 : Epi.D}, g < L.threads →
    St Q L X g k = some (some (.d (.epi d))) → d.pr.rv = true → d.sk = false →
    St Q L X g k0 = some (some (.d (.epi d0))) → d0.site = .ld → d0.pr = d.pr →
    X.get (g, k0) = some ⟨pc, .tc (.ld d.pr.taddr d.o (.s16x32bx2 64))⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧
      dm.i = Q.numIters (reqOf L g) (splitOf L g) ∧ d.pr.tm = dm.tm ∧
      ∀ j < 64, ReadSource L X .ld m (g, k0) (tcDataCell L g (.s16x32bx2 64) d.pr.taddr j)

/-- **`OSource` for every row**: the same statement without `d.pr.rv` (the epilogue of every row
loads its 64 words, and their source does not depend on the row being valid), for the load event
with any words. -/
def OSourceAll (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k k0 pc : Nat} {d d0 : Epi.D} {vals : List Value}, g < L.threads →
    St Q L X g k = some (some (.d (.epi d))) → d.sk = false →
    St Q L X g k0 = some (some (.d (.epi d0))) → d0.site = .ld → d0.pr = d.pr →
    X.get (g, k0) = some ⟨pc, .tc (.ld d.pr.taddr vals (.s16x32bx2 64))⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧
      dm.i = Q.numIters (reqOf L g) (splitOf L g) ∧ d.pr.tm = dm.tm ∧
      ∀ j < 64, ReadSource L X .ld m (g, k0) (tcDataCell L g (.s16x32bx2 64) d.pr.taddr j)

/-- **`oSource` for every row.** The last PV MMA is the read source of the epilogue's `O`
load. -/
theorem oSourceAll_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L kernel Assumptions.all mem0 X)
    (st : Pr.MmaStates Q L G) (R : OSrcPrem Q L kernel Assumptions.all mem0 X G)
    (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X) : OSourceAll Q L X := by
  intro g k k0 pc d d0 vals hg hσ hsk hσ0 hs0 hpr0 hld
  have hk0 : k0 < (X.tr g).length := len_of_get hld
  have hcl : g / L.block < L.grid := cta_lt hX ⟨_, hld⟩
  have l := G.lane (g / L.block) hcl
  have H := G.ctx (g / L.block) hcl
  obtain ⟨pcp, sc, hk2, hpoll⟩ := ld_poll hpre hX hf hg hk0 hσ0 hs0
  have hN : 1 ≤ Q.numIters (reqOf L g) (splitOf L g) := by
    have := (skip_of hpre hf hg hσ).not.mp (by rw [hsk]; simp)
    omega
  have hLP := last_pv hpre hX hf hB hb hn G R hcl hg rfl hpoll hN
  obtain ⟨hcm, hcmc⟩ := hLP.cm_ok
  obtain ⟨k', dm, P, pcm, dst, spm, acc, mask, hσm, hs7, hi7, hevm, hall⟩ := hLP.pv7
  have hmEvt : IsMma X (G.cm (g / L.block), k') := ⟨dst, spm, acc, mask, pcm, hevm⟩
  have hdm0 : dm.tm = 0 :=
    Interface.mma_tm hpre hX hf hb hn (m := (G.cm (g / L.block), k')) ⟨P, hσm⟩
  have hpr0' : d.pr.tm = 0 := R.epiTm hg hσ
  refine ⟨(G.cm (g / L.block), k'), pcm, dst, spm, acc, mask, dm, P, hcm, hcmc, hevm, hσm, hs7,
    hi7, by rw [hpr0', hdm0], ?_⟩
  intro j hj
  have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
  have ht128 : g % L.block < 128 := (hf.reach hg hσ).1
  have hcell := taddr_cell L g (pr := d.pr) (by omega) hm.c0 j
  rw [hcell, hpr0']
  set cell : Cell := oCell (g / L.block) 0 (Epi.rowM (g % L.block))
    (64 * Epi.halfM (g % L.block) + j) with hcelldef
  have hrow : Epi.rowM (g % L.block) < 64 := by unfold Epi.rowM; omega
  have hcol : 64 * Epi.halfM (g % L.block) + j < 128 := by unfold Epi.halfM; omega
  -- the last PV MMA writes the cell
  obtain ⟨hqo, hdst, -, hmask, -⟩ := pv_event hpre hX hf hcm hevm hσm hs7
  have hwc : writeCell spm dst mask (Epi.rowM (g % L.block))
      (64 * Epi.halfM (g % L.block) + j) = some cell := by
    rw [hdst, hmask, hdm0, zero_add]
    have := pv_writeCell (sp := spm) hqo.desc (cta := g / L.block) (tm := 0)
      (hqo.low.trans hcmc) (by omega) hrow hcol
    simpa using this
  have hmc : X.MmaCell (G.cm (g / L.block), k') cell :=
    ⟨_, _, _, _, _, _, ⟨pcm, hevm⟩, hwc⟩
  have hlen' : k' < (X.tr (G.cm (g / L.block))).length := len_of_get hevm
  have hpv := (st.pv hcm hlen' hσm hs7).2
  rw [hcmc] at hpv
  obtain ⟨jy, pcy, ey, hjy, hgy, hqy⟩ := hpv.issue
  obtain ⟨hIO, hcta⟩ := SO.pv_cells l.tmOk hqy hgy hmc
  have ix : WInfo L X (g / L.block) (G.cm (g / L.block)) (G.p0 (g / L.block))
      (G.tm (g / L.block)) (G.Soft (g / L.block)) (G.cm (g / L.block), k') cell :=
    .pv hpv hIO hcta
  have hdone := SO.f_doneBefore hX (G.ctx (g / L.block) hcl).facts
    (fun hx hc => l.mma_thread hx hc) (R.commit_once (g / L.block) hcl)
    (R.mma_before (g / L.block) hcl) ⟨hcm, hg, by rw [hcmc]⟩ hpoll hmEvt hcmc
    (by omega) hk0
  refine ⟨?_, .inl hmc, .inl (.inl hdone), ?_, ?_⟩
  · -- the source is not the load
    intro hh
    have hh1 : G.cm (g / L.block) = g := congrArg Prod.fst hh
    have hh2 : k' = k0 := congrArg Prod.snd hh
    subst hh2
    rw [hh1] at hσm
    rw [hσ0] at hσm
    cases Option.some.inj (Option.some.inj hσm)
  · -- every other writer of the cell is before the last PV MMA
    intro other hw'
    have hol := cta_lt hX (write_event hnc hns hw')
    have iy := winfo hnc hns (G.lane _ hol) hw' rfl
    have hxy : other.1 / L.block = g / L.block := iy.cta.symm.trans ix.cta
    rw [hxy] at iy
    cases iy with
    | @qk _ _ i' hq' h1' _ =>
      exact absurd hIO (SO.inS_inO_disjoint (Nat.mod_lt _ (by omega)) h1')
    | @pv _ _ m' hv' h1' _ =>
      obtain ⟨hth, hle⟩ := hall other hv'.isMma hxy
      rcases Nat.lt_or_ge other.2 k' with hlt | hge
      · exact .inr (.inl (.inl (pv_before l.cm_ok.1 hv' hpv hlt)))
      · exact .inl (Prod.ext hth (by show other.2 = k'; omega))
    | @pst t sk i' w j' a' vals sh cell' hst hp hj ha hc' hin _ =>
      exact absurd hIO (SO.inP_inO_disjoint (Nat.mod_lt _ (by omega)) hin)
    | @ost t sk i' w j' a' vals sh cell' hst ho hj ha hc' hin _ =>
      have hb := R.ostBound (g / L.block) hcl ho
      have htc := soft_info H ho.gate.soft
      have hce := cta_eq (L := L) (g := g) (g' := t) htc.2.1
      rw [hce.1, hce.2.1] at hb
      have h1le := ho.one_le
      exact .inr (.inl (.inr (.inl (pv_ost_B H l hpv ho hst (by omega)))))
  · -- the source is live
    intro cta r hr hcov dd hrel
    obtain ⟨⟨pc1, grp, a1, n1, hd⟩, hdc⟩ := Tmem1.release_info hX ht.toTmem1Ops hr hrel
    have hown := Tmem1.covers_owner hcov
    obtain ⟨hlc, -⟩ := Tmem1.record_info hX ht.toTmem1Ops hr
    have hcc : dd.1 / L.block = (g, k0).1 / L.block := by
      rw [hdc, ← hlc, ← hown]
      exact hcta
    refine .inl ⟨fun ⟨a', vals', sh', h'⟩ => (hl.ldst_before_dealloc hd hcc).1 h',
      fun ⟨a', vals', sh', h'⟩ => ?_, fun hta => ?_⟩
    · exfalso
      obtain ⟨pc2, h2⟩ := h'
      rw [hld] at h2
      simp at h2
    · exfalso
      rcases hta with ⟨dd', s', ac', mk', pc2, h2⟩ | ⟨cp, hcp⟩ | ⟨s', hs'⟩
      · rw [hld] at h2
        simp at h2
      · exact hnc _ _ hcp
      · exact hns _ _ hs'

/-- **`oSource`.** The last PV MMA is the read source of the epilogue's `O` load
(`oSourceAll_of`, for a valid row). -/
theorem oSource_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hB : Mma.MmaBcast L X) (hb : Interface.BaseWordRead L X)
    (hn : Interface.NumWordRead Q L X) (hnc : ∀ e cp, ¬ X.CpIssue e cp)
    (hns : ∀ e s, ¬ X.ShiftIssue e s) (G : SrPkg L kernel Assumptions.all mem0 X)
    (st : Pr.MmaStates Q L G) (R : OSrcPrem Q L kernel Assumptions.all mem0 X G)
    (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X) : OSource Q L X :=
  fun hg hσ _ hsk hσ0 hs0 hpr0 hld =>
    oSourceAll_of hpre hX hf hB hb hn hnc hns G st R ht hl hg hσ hsk hσ0 hs0 hpr0 hld

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
