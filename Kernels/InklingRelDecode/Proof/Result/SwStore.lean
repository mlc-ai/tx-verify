-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Interface.SwStO
public import Kernels.InklingRelDecode.Proof.Interface.SwTcSt
public import Kernels.InklingRelDecode.Proof.Result.RsOAcc
public import Kernels.InklingRelDecode.Proof.Result.SvVals

@[expose] public section

/-!
# The word of the rescale store (`Rs.OAccPrem.store`)

`OAccPrem.store`: the word the rescale store of iteration `b` writes to a cell of `O` of a valid
row is `alpha` times the value the PV MMA at step 7 of iteration `b` left in the cell.

The store is the softmax thread's `stO` event (`Interface.tcst_event_state`: the program has two
`tcgen05.st`, and a 64-word one is the rescale's). Its words are `alr · Sm.bfR (ow k)`
(`Sm.shape_stO`), `alr` is `Out.alphaRow` (`Sv.alr_eq`), and `ow k` is the word the rescale load
returned (`Sv.stO_pred`: the state at `stO` is three events after the state at `ldO`). The load
returns the value its read source wrote (`LoadReadOk.f32`): that the read source is the PV MMA at
step 7 of the iteration is `OLoadSrc`, the premise this file leaves, with the base word of the
default partition (`SmBaseZero`: the softmax region's Tensor Memory base is 0) and the iteration of
a store's coordinates (`OStIter`: the `OSt` iteration `b` of the store is the machine's `d.i`).

`stO_cell`: register `j` of the store (and of the load) is the cell `oCell` of the thread's row and
column `64 · half + j`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rs
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)
open PTX.Kernels.InklingRelDecode.Proof.Sv (ValidRow SvPrem)

noncomputable section

variable {Q : Params} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution}

/-- **The cell register `j` of the rescale's load and store reads or writes**: row `row T`, column
`tm + 256 + 64 · half + j` of the `O` accumulator of the thread's CTA. -/
theorem stO_cell (L : Launch) (g : Nat) {tm : Nat} (htm : tm + 384 ≤ 512) (j : Nat) :
    tcDataCell L g (.s16x32bx2 64) (tm + 256 + g % L.block / 32 * 2 ^ 21) j =
      oCell (g / L.block) tm (Sm.row (g % L.block)) (64 * Sm.half (g % L.block) + j) := by
  unfold tcDataCell TcShape.base TcShape.laneIn TcShape.columnIn TcShape.lanes laneBase
    chunkOffset oCell Sm.row Sm.half laneOf
  split_ifs with h1 <;> congr 1 <;> omega

/-- **The premise on the rescale load**: at the softmax thread's rescale load of iteration `i` (a
valid row), the PV MMA at step 7 of iteration `i` (block `i - 1`) is the read source
(`ReadSource .ld`) of each of the 64 cells the load reads, and it is the only such state of the
lane. The analogue of `Rs.oSource_of` for the rescale load: `SO.o_doneBefore_iter` (the poll of
`o_done` observes the commit after the PV MMA of block `i - 1`), the other writers of the cells
(the PV MMAs before it by program order, the rescale stores by `Sr.pv_ost_B`, the later PV MMA by
the `wait::ld` before `bar24`, `bar20`, `bar21` and thread 0's arrival on `p_ready`). -/
structure OLoadSrc (Q : Params) (L : Launch) (X : Execution) : Prop where
  src : ∀ {g k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}, g < L.threads →
    ValidRow Q L g → St Q L X g k = some (some (.d (.sm d))) → d.site = .ldO →
    X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    ∃ (m : EvId) (pcm dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat)
      (dm : Mma.D) (P : Loader.Pro),
      m.1 < L.threads ∧ m.1 / L.block = g / L.block ∧
      X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩ ∧
      St Q L X m.1 m.2 = some (some (.w (.mma dm P))) ∧ dm.site = .pv 7 ∧ dm.i = d.i ∧
      (∀ j < 64, ReadSource L X .ld m (g, k) (tcDataCell L g (.s16x32bx2 64) a j)) ∧
      ∀ (k'' : Nat) (d'' : Mma.D) (P'' : Loader.Pro),
        St Q L X m.1 k'' = some (some (.w (.mma d'' P''))) → d''.site = .pv 7 → d''.i = dm.i →
        k'' = m.2

/-- **The base word of the softmax region** is 0: the Tensor Memory base every softmax state holds
(`Sm.Ent.tm`) is the allocation's, column 0 (row S5, `Interface.BaseWordRead` for the default
partition). -/
def SmBaseZero (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → St Q L X g k = some (some (.d (.sm d))) →
    d.e.tm = 0

/-- **The iteration of a rescale store**: the coordinates `b` of the store (`OSt`) are the
iteration `d.i` of the softmax state at the store (the poll of `o_done` of the thread's iteration
`i` is its `(i - 1)`-th: `SO.sm_owait_count`, on a run). -/
def OStIter (Q : Params) (L : Launch) (X : Execution) {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (G : SrPkg L K A mem0 X) : Prop :=
  ∀ c, c < L.grid → ∀ {t sk b a : Nat} {vals : List Value} {sh : TcShape} {d : Sm.D},
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk b a vals sh →
    St Q L X t sk = some (some (.d (.sm d))) → d.i = b

/-- **The state before a rescale-store event is a softmax state at `stO`.** -/
theorem stO_state (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {t sk pc a : Nat} {vals : List Value}
    (hget : X.get (t, sk) = some ⟨pc, .tc (.st a vals (.s16x32bx2 64))⟩) :
    ∃ d : Sm.D, St Q L X t sk = some (some (.d (.sm d))) ∧ d.site = .stO := by
  have hne : ∀ pc' f, (⟨pc, .tc (.st a vals (.s16x32bx2 64))⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
    intro pc' f h
    simp only [Event.mk.injEq] at h
    cases h.2
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked hget hne
  obtain ⟨d, rfl, hs⟩ := Interface.tcst_event_state hf.sound hX hget hσ
  refine ⟨d, hσ, ?_⟩
  rcases hs with hs | hs
  · exfalso
    obtain ⟨u, hF⟩ := Interface.fired_cont hX hf (event_thread_lt hX hget) hget hσ
      (by simp [Interface.ExitState])
    obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_tmemSt (Interface.fired_sm hF) hs
    simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
    obtain ⟨-, -, -, hsh⟩ := hev
    simp at hsh
  · exact hs

/-- **The address of the rescale store's event** (no row condition). -/
theorem ostore_addr (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} (hg : g < L.threads) {k pc a : Nat} {d : Sm.D}
    {vals : List Value} {sh : TcShape} (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .stO) (he : X.get (g, k) = some ⟨pc, .tc (.st a vals sh)⟩) :
    a = Sm.oAddr L g d := by
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_stO (Interface.fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
  exact hev.2.1

/-- **The words of the rescale store.** The thread's `tcgen05.st` at the state `stO` of iteration
`d.i` (a valid row) stores 64 words at `Sm.oAddr`; where the word `ow w` the preceding load
returned is the `f32` number `y`, word `w` is the float of `alphaRow · y`. -/
theorem ostore_event (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) {g : Nat} (hg : g < L.threads)
    (hvr : ValidRow Q L g) {k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .stO) (he : X.get (g, k) = some ⟨pc, .tc (.st a vals sh)⟩) :
    a = Sm.oAddr L g d ∧ sh = .s16x32bx2 64 ∧ vals.length = 64 ∧
      ∀ w < 64, ∀ y : ℝ, d.stg.ow w = .float .f32 y →
        vals[w]? = some (.float .f32 (alphaRow Q L g d.i (Sm.row (g % L.block)) * y)) := by
  have hIv : Sm.Inv L g d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_stO (Interface.fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
  obtain ⟨-, ha, hv, hsh⟩ := hev
  subst ha hv hsh
  refine ⟨rfl, rfl, hl, ?_⟩
  intro w hw' y hy
  rw [hw w hw', hy, Sm.prodO_float hIv.four.al,
    Sv.alr_eq hpre hX hf P hg hvr hk hσ (by rw [hs]; trivial)]

theorem oCell_inj {c tm r r' n n' : Nat} (hr : r < 64) (hr' : r' < 64)
    (h : oCell c tm r n = oCell c tm r' n') : r = r' ∧ n = n' := by
  unfold oCell at h
  simp only [Cell.mk.injEq] at h
  omega

theorem row_lt_64 (T : Nat) : Sm.row T < 64 := by
  unfold Sm.row
  omega

/-- **`OAccPrem.store`**, for the rescale factors `Out.alphaRow`: the word of the rescale store of
iteration `b` at a cell of `O` of a valid row is `alphaRow` times the value the PV MMA at step 7 of
iteration `b` left in the cell. From the event shapes (`ostore_event`, `Sm.shape_ldO`), the
iteration invariant (`Sv.alr_eq`) and the three premises `OLoadSrc`, `SmBaseZero`, `OStIter`. -/
theorem store_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (G : SrPkg L kernel Assumptions.all mem0 X)
    (O : OLoadSrc Q L X) (hT : SmBaseZero Q L X) (hI : OStIter Q L X G) :
    ∀ c, c < L.grid → ∀ {g b r n t sk a j k' : Nat} {vals : List Value} {sh : TcShape}
      {d' : Mma.D} {P' : Loader.Pro}, g / L.block = c → 1 ≤ b → QRowValid Q L g r → n < 128 →
    X.TSt (t, sk) a vals sh → OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk b a vals sh →
    j < 64 → oCell c (G.tm c) r n = tcDataCell L t (.s16x32bx2 64) a j →
    St Q L X (G.cm c) k' = some (some (.w (.mma d' P'))) → d'.site = .pv 7 → d'.i = b →
    ∀ v : ℝ, Result L Assumptions.all X (G.cm c, k') (oCell c (G.tm c) r n) (.float .f32 v) →
      StoreValue L X (t, sk) (oCell c (G.tm c) r n) (.float .f32 (alphaRow Q L g b r * v)) := by
  intro c hcl g b r n t sk a j k' vals sh d' P' hgc hb1 hr hn hst hO hj hcell0 hσ' hs' hi' v hv
  have H := G.ctx c hcl
  have l := G.lane c hcl
  obtain ⟨ht, htc, hT128⟩ := soft_info H hO.gate.soft
  obtain ⟨hsh, hlen, w, ha⟩ := hO.shape
  subst hsh
  obtain ⟨pcs, hget⟩ := hst
  obtain ⟨d, hσt, hds⟩ := stO_state hX hf hget
  have hk : sk ≤ (X.tr t).length := (len_of_get hget).le
  have hiter : d.i = b := hI c hcl hO hσt
  have hTm := hT ht hσt
  have htmOk := l.tmOk
  unfold SO.TmOk at htmOk
  have hreq := cta_eq (L := L) (g := g) (g' := t) (by rw [htc, hgc])
  -- the address: the base is 0 and the lane field is the thread's warp
  have hae : a = Sm.oAddr L t d := ostore_addr hX hf ht hσt hds hget
  have hz : G.tm c = 0 ∧ w = t % L.block / 32 := by
    have h1 := hae
    have hbw := Interface.sm_bw' hpre hX hf ht hσt (by rw [hds]; trivial)
    unfold Sm.oAddr at h1
    rw [hTm, hbw] at h1
    omega
  obtain ⟨hz, hw⟩ := hz
  -- the cell fixes the row and the column
  have hcell := hcell0
  rw [ha, hz, hw, stO_cell L t (tm := 0) (by omega) j, htc] at hcell
  obtain ⟨hrt, hnn⟩ := oCell_inj (by have := hr.1; omega) (row_lt_64 _) hcell
  have hvt : ValidRow Q L t := by
    obtain ⟨h1, h2⟩ := hr
    unfold Sv.ValidRow
    refine ⟨by rw [← hrt]; exact h1, ?_⟩
    have e1 : Sm.tokOf (t % L.block) = r / 6 := by rw [← Sv.row_div6, hrt]
    have e2 : ProA.cta L t .z = reqOf L g := hreq.1
    rw [e1, e2]
    exact h2
  obtain ⟨-, -, -, hwd⟩ := ostore_event hpre hX hf P ht hvt hk hσt hds hget
  -- the rescale load three events before
  obtain ⟨k0, d0, a0, vals0, sh0, hk0, hσ0, hs0, ⟨pc0, hget0⟩, hd⟩ :=
    Sv.stO_pred hk hσt hds
  obtain ⟨u0, hF0⟩ := Interface.fired_cont hX hf ht hget0 hσ0 (by simp [Interface.ExitState])
  obtain ⟨vals1, hl1, hev0⟩ := Sm.shape_ldO (Interface.fired_sm hF0) hs0
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev0
  obtain ⟨-, ha0, hv0, hsh0⟩ := hev0
  subst hv0 hsh0
  have haa : a = a0 := by
    have : Sm.oAddr L t d = Sm.oAddr L t d0 := by rw [hd]; rfl
    rw [hae, this, ha0]
  obtain ⟨m, pcm, dst, spm, acc, mask, dm, Pm, hmg, hmc, hmget, hmσ, hms, hmi, hrsrc, huniq⟩ :=
    O.src ht hvt hσ0 hs0 hget0
  have hmE : IsMma X m := ⟨dst, spm, acc, mask, pcm, hmget⟩
  have hm1 : m.1 = G.cm c := l.mma_thread hmE (hmc.trans htc)
  have hiter0 : d0.i = b := by rw [hd] at hiter; exact hiter
  have hk'eq : k' = m.2 :=
    huniq k' d' P' (by rw [hm1]; exact hσ') hs' (by rw [hi', hmi, hiter0])
  have hmeq : m = (G.cm c, k') := Prod.ext hm1 hk'eq.symm
  have hrs := hrsrc j hj
  rw [hmeq] at hrs
  have hld : X.TLd (t, k0) a0 vals0 (.s16x32bx2 64) := ⟨pc0, hget0⟩
  have hjl : j < vals0.length := by omega
  have hlc : LoadCell L X (t, k0) j (oCell c (G.tm c) r n) :=
    ⟨a0, vals0, _, hld, hjl, by rw [hcell0, haa]⟩
  have hrs' : ReadSource L X .ld (G.cm c, k') (t, k0) (oCell c (G.tm c) r n) := by
    rw [hcell0, haa]
    exact hrs
  have hl : vals0[j]? = some (.float .f32 v) :=
    LoadReadOk.f32 hX.tcRead.1 hld hlc hrs' (.inl hv)
  refine ⟨a, vals, .s16x32bx2 64, j, ⟨pcs, hget⟩, ?_, hcell0⟩
  have h3 : d.stg.ow j = .float .f32 v := by
    rw [hd]
    show vals0.getD j (b32 0) = _
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  have hal : alphaRow Q L t d0.i (Sm.row (t % L.block)) = alphaRow Q L g b r := by
    rw [hiter0, ← hrt]
    unfold alphaRow
    rw [hreq.1, hreq.2.1, hreq.2.2]
  have hw2 := hwd j hj v h3
  have hdi : d.i = d0.i := by rw [hd]
  rw [hw2, hdi, hal]

end
end PTX.Kernels.InklingRelDecode.Proof.Rs
