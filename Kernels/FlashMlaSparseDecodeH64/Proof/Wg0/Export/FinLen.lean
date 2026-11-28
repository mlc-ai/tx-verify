-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Kernel.FullVote
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.CarryBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteOrd
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103

@[expose] public section

/-! # The blocks closed by a warpgroup-0 lane are its arrivals on `so_ready`

An event at pc 1122 is an arrival on one of the two slots of `soReady` and no other event of the
lane arrives there (`mbarRow_wg0`), so the closed blocks of a prefix (`w0Closed`) are the
prefix's arrivals on `soReady` (`w0Closed_arrs`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem arr_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g i : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, i) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (e.pc = w0ArrSPc ↔ (arrivesOn (loc L g (.soReady 0)) e = true ∨
      arrivesOn (loc L g (.soReady 1)) e = true)) ∧
    ¬ (arrivesOn (loc L g (.soReady 0)) e = true ∧ arrivesOn (loc L g (.soReady 1)) e = true) := by
  have hg := Frame.lt_of_get hX he
  have hrow : MbarRow.Wg0 P L X := mbarRow_wg0 hp hX hFw
  obtain ⟨pc, kd⟩ := e
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun ⟨h0, h1⟩ => ?_⟩
  · simp only at h
    obtain ⟨d, -, ⟨hpc, hk⟩, -⟩ := wg0_at hp hX hFw he hub
      (by show 103 ≤ pc ∧ pc < 1842; unfold w0ArrSPc at h; omega)
    have hs : d.site = .arrS := Wg0.Data.site_pc_1122 (by rw [← hpc]; exact h)
    simp only [Wg0.EvK, hs, Wg0.ArrEv] at hk
    rcases hk with hk | ⟨f, hk⟩
    · subst hk
      have hu := hrow (l := smLoc L g (Wg0.soW L d) 0) hg he
        ⟨hw, by show 103 ≤ pc ∧ pc < 1842; unfold w0ArrSPc at h; omega⟩
        (by simp only [Frame.MbarOf])
      cases hu with
      | soReady hpc' hl hk' =>
        rw [hl]
        generalize slot2 (arrs2 L g .soReady ((X.tr g).take i)) = s
        fin_cases s <;> simp [arrivesOn, sourceArrive]
      | _ => rename_i hpc' _ _; unfold w0ArrSPc at h; simp only at hpc'; omega
    · exact absurd hk (hub f)
  · have key : ∃ l tx c r sc, kd = .arrive l tx c r sc ∧
        (l = loc L g (.soReady 0) ∨ l = loc L g (.soReady 1)) := by
      cases kd <;> simp [arrivesOn, sourceArrive] at h ⊢
      exact h
    obtain ⟨l, tx, c, r, sc, rfl, hl⟩ := key
    have hin := wg0_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩)))
    have hr : 103 ≤ pc ∧ pc < 1842 := by
      simp only [Wg0.inRole, decide_eq_true_eq] at hin
      omega
    have hu := hrow (l := l) hg he ⟨hw, hr⟩ (by simp only [Frame.MbarOf])
    cases hu with
    | soReady hpc' hl' hk' => exact hpc'
    | lastStore hpc' hl' hk' =>
      rcases hl with hl | hl <;>
        exact absurd (Wg0.loc_inj.mp (hl'.symm.trans hl)) (by simp)
    | coordReady hpc' hl' hk' =>
      rcases hl with hl | hl <;>
        exact absurd (Wg0.loc_inj.mp (hl'.symm.trans hl)) (by simp)
    | qkDone hpc' hl' hk' =>
      rcases hl with hl | hl <;>
        exact absurd (Wg0.loc_inj.mp (hl'.symm.trans hl)) (by simp)
    | coordFree hpc' hl' hk' =>
      rcases hl with hl | hl <;>
        exact absurd (Wg0.loc_inj.mp (hl'.symm.trans hl)) (by simp)
    | svDone hpc' hl' hk' =>
      rcases hl with hl | hl <;>
        exact absurd (Wg0.loc_inj.mp (hl'.symm.trans hl)) (by simp)
  · cases kd <;> simp [arrivesOn, sourceArrive] at h0 h1
    rename_i l tx c r sc
    rw [h0] at h1
    exact absurd (Wg0.loc_inj.mp h1.symm) (by simp)

private theorem countP_two {l : List Event} {Q a b : Event → Bool}
    (h : ∀ f ∈ l, (Q f = true ↔ (a f = true ∨ b f = true)) ∧ ¬ (a f = true ∧ b f = true)) :
    l.countP Q = l.countP a + l.countP b := by
  induction l with
  | nil => simp
  | cons f l ih =>
    have ih := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2⟩ := h f List.mem_cons_self
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    cases hQ : Q f <;> cases ha : a f <;> cases hb : b f <;> simp_all <;> omega

/-- **The closed blocks of a prefix are its arrivals on `soReady`** (either slot), when the
lane has no undefined behaviour before `k`. -/
theorem w0Closed_arrs (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g : Nat} (hw : warp L g < 4) {k : Nat} (hal : LaneUbFree X g k) :
    w0Closed ((X.tr g).take k) = arrs2 L g .soReady ((X.tr g).take k) := by
  unfold w0Closed arrs2 arrivals
  refine countP_two fun f hf => ?_
  obtain ⟨i, hik, hi⟩ : ∃ i < k, X.get (g, i) = some f := by
    obtain ⟨i, hi, hf'⟩ := List.getElem_of_mem hf
    rw [List.getElem_take] at hf'
    rw [List.length_take] at hi
    exact ⟨i, by omega, by rw [← hf']; exact List.getElem?_eq_getElem _⟩
  obtain ⟨h1, h2⟩ := arr_pc hp hX hFw hw hi (NoUbBefore.ne hal hik hi)
  exact ⟨by simpa using h1, h2⟩

private theorem arrs_counts (hp : Pre P L m) {g : Nat} {es : List Event} {n : Wg0.Cnt → Nat}
    {a : Bool} {r i : Nat} {sv : Option Nat}
    (hn : Wg0.Counts (Wg0.objs L g) n a r i sv) (hA : ∀ l, arrivals l es = n (.arrive l)) :
    arrs2 L g .soReady es = r := by
  unfold arrs2
  rw [hA, hA, hn.2, hn.2, Wg0.arr_so hp _ _ _ 0, Wg0.arr_so hp _ _ _ 1]
  simp [ringUses]
  omega

/-- **At an arrival on `last_store_done` (pc 200) no block is closed.** -/
theorem w0Closed_arrL (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event}
    (hw : warp L g < 4) (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u)
    (hpc : e.pc = w0ArrLPc) : w0Closed ((X.tr g).take k) = 0 := by
  rw [w0Closed_arrs hp hX hFw hw (noUbBefore_of_get hX he)]
  obtain ⟨d, hR, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub
    (by unfold w0ArrLPc at hpc; omega)
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  have hs : d.site = .arrL := Wg0.Data.site_pc_200 (by rw [← hpc']; exact hpc)
  have hc' : Wg0.Counts (Wg0.objs L g) (fun c => ((X.tr g).take k).countP (Wg0.cls c)) false 0 0
      none := by
    have := hc
    simp only [Wg0.RefCore, Wg0.RefAt, hs, Wg0.Site.reg] at this
    exact this
  exact arrs_counts hp hc' (fun l => wg0_arrivals hp hX hFw hw k l)

/-- **No block closes before the arrival at pc 200** in a prefix of a lane of warpgroup 0. -/
theorem w0_noEarly_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g : Nat} (hw : warp L g < 4) {k : Nat} (hal : LaneUbFree X g k) :
    W0NoEarlyClose ((X.tr g).take k) := by
  intro i hi hpc200
  have hi' : i < k := by
    have := hi
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, i) = some (((X.tr g).take k)[i]'hi) := by
    have : (X.tr g)[i]? = some (((X.tr g).take k)[i]'hi) := by
      rw [List.getElem_take]; exact List.getElem?_eq_getElem _
    exact this
  have h0 := w0Closed_arrL hp hX hFw hw hget (hal.ne hi' hget) hpc200
  rw [List.take_take, Nat.min_eq_left hi'.le]
  exact h0

/-- **No block closes before the arrival at pc 200** (a lane with no undefined behaviour). -/
theorem w0_noEarly (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g : Nat} (hw : warp L g < 4) (k : Nat) :
    W0NoEarlyClose ((X.tr g).take k) :=
  w0_noEarly_pre hp hX hFw hw (noUbBefore_of_noUb hnu)

private theorem w0Fin_cnt_gen (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u)
    (hpc : e.pc = 572 ∨ e.pc = 1157 ∨ e.pc = 566 ∨ e.pc = 1155) :
    ((e.pc = 572 ∨ e.pc = 1157) → ((X.tr g).take k).countP (Execution.isBarId 9) =
      2 * (w0Fin ((X.tr g).take k)).1.length + 2) ∧
    ((e.pc = 566 ∨ e.pc = 1155) → ((X.tr g).take k).countP (Execution.isBarId 9) =
      2 * (w0Fin ((X.tr g).take k)).1.length + 1) ∧
    ((e.pc = 1155 ∨ e.pc = 1157) →
      (w0Fin ((X.tr g).take k)).1.length = blocksOf P L (g / L.block)) ∧
    ((e.pc = 566 ∨ e.pc = 572) →
      (w0Fin ((X.tr g).take k)).1.length < blocksOf P L (g / L.block)) := by
  have hal := noUbBefore_of_get hX he
  have hno := w0_noEarly_pre hp hX hFw hw hal
  rw [w0Fin_length hno, w0Closed_arrs hp hX hFw hw hal]
  obtain ⟨d, hR, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  obtain ⟨hC, hL, -, ht⟩ := hR (wg0_take_noUb hX he)
  have hB : w0BarCnt X g k = Wg0.barOrd d := ht
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) k hal, hB]
  have hA := fun l => wg0_arrivals hp hX hFw hw k l
  have hsite : d.site = .mld ∨ d.site = .eld ∨ d.site = .mst ∨ d.site = .est := by
    have h2 : d.site.pc = 572 ∨ d.site.pc = 1157 ∨ d.site.pc = 566 ∨ d.site.pc = 1155 := by
      rw [← hpc']; exact hpc
    revert h2
    generalize d.site = s
    cases s
    all_goals repeat' (rename_i x; fin_cases x)
    all_goals decide
  have hl2 : 2 ≤ d.site.lens := by
    rcases hsite with h | h | h | h <;> rw [h] <;> simp [Wg0.Site.lens]
  have hepi : ∀ b, (d.site = .eld ∧ b = 2 ∨ d.site = .est ∧ b = 1) →
      w0IdCnt (blocksOf P L (g / L.block)) (warp L g % 2) 9 (Wg0.barOrd d) =
        2 * blocksOf P L (g / L.block) + b ∧
      arrs2 L g .soReady ((X.tr g).take k) = blocksOf P L (g / L.block) := by
    intro b hb
    have hk' : d.site.reg = Wg0.Reg.epi := by rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have hR' := Wg0.rounds_blocks hL hl2
    have ho : Wg0.barOrd d = 3 * blocksOf P L (g / L.block) + d.site.bidx := by
      simp only [Wg0.barOrd, hk', hR']
    have hc := hC
    simp only [Wg0.RefCore, Wg0.RefAt, hk'] at hc
    refine ⟨?_, ?_⟩
    · rcases hb with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp only [h, Wg0.Site.bidx] at ho <;>
        rw [ho, w0Cnt9_epi _ _ _ (by omega)] <;> omega
    · rw [arrs_counts hp hc.2 hA]
      simp only [Wg0.Control.D.words]
      rw [hR']
  rcases hsite with h | h | h | h
  · obtain ⟨r', hrR, ho, hn⟩ := barOrd_loop hC hL (by rw [h]; rfl) hl2
    simp only [h, Wg0.Site.bidx] at ho
    rw [ho, (w0Cnt9_site _ _ hrR).2]
    rw [arrs_counts hp hn hA]
    have hpe : e.pc = 572 := by rw [hpc', h]; rfl
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩ <;> omega
  · obtain ⟨h1, h2⟩ := hepi 2 (.inl ⟨h, rfl⟩)
    rw [h1, h2]
    have hpe : e.pc = 1157 := by rw [hpc', h]; rfl
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩ <;> omega
  · obtain ⟨r', hrR, ho, hn⟩ := barOrd_loop hC hL (by rw [h]; rfl) hl2
    simp only [h, Wg0.Site.bidx] at ho
    rw [ho, (w0Cnt9_site _ _ hrR).1]
    rw [arrs_counts hp hn hA]
    have hpe : e.pc = 566 := by rw [hpc', h]; rfl
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩ <;> omega
  · obtain ⟨h1, h2⟩ := hepi 1 (.inr ⟨h, rfl⟩)
    rw [h1, h2]
    have hpe : e.pc = 1155 := by rw [hpc', h]; rfl
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩ <;> omega

/-- **The barrier count of the exchange load**: a load of the peer's word (pc 572, or 1157 in the
epilogue) is after `2 r + 2` barrier-9 events, `r` the number of closed blocks. -/
theorem w0_cnt_exch (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 572 ∨ e.pc = 1157) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * (w0Fin ((X.tr g).take k)).1.length + 2 :=
  by
    obtain ⟨h1, -, -, -⟩ := w0Fin_cnt_gen hp hX hFw hw he hub (by omega)
    exact h1 hpc

/-- **The barrier count of the exchange store**: a store of the lane's word (pc 566, or 1155) is
after `2 r + 1` barrier-9 events, `r` the number of closed blocks. -/
theorem w0_cnt_st (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 566 ∨ e.pc = 1155) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * (w0Fin ((X.tr g).take k)).1.length + 1 :=
  by
    obtain ⟨-, h2, -, -⟩ := w0Fin_cnt_gen hp hX hFw hw he hub (by omega)
    exact h2 hpc

/-- **The epilogue's exchange events are after all `R` blocks**: the store at pc 1155 and the
load at pc 1157 have `R` closed blocks, `R` the CTA's block count. -/
theorem w0_len_epi (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 1155 ∨ e.pc = 1157) :
    (w0Fin ((X.tr g).take k)).1.length = blocksOf P L (g / L.block) :=
  by
    obtain ⟨-, -, h3, -⟩ := w0Fin_cnt_gen hp hX hFw hw he hub (by omega)
    exact h3 hpc

/-- **The loop's exchange events are before the last block**: the store at pc 566 and the load at
pc 572 have fewer than `R` closed blocks. -/
theorem w0_len_lt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 566 ∨ e.pc = 572) :
    (w0Fin ((X.tr g).take k)).1.length < blocksOf P L (g / L.block) :=
  by
    obtain ⟨-, -, -, h4⟩ := w0Fin_cnt_gen hp hX hFw hw he hub (by omega)
    exact h4 hpc

/-- **The block index of the exchange load**: a load of the peer's word (pc 572, or 1157 in the
epilogue) after `2 r + 2` barrier-9 events is after `r` closed blocks. -/
theorem w0Fin_length_exch (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k r : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 572 ∨ e.pc = 1157)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2) :
    (w0Fin ((X.tr g).take k)).1.length = r := by
  have := w0_cnt_exch hp hX hFw hw he hub hpc
  omega

/-- **The block index of the exchange store**: a store of the lane's word (pc 566, or 1155) after
`2 r + 1` barrier-9 events is after `r` closed blocks. -/
theorem w0Fin_length_st (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k r : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 566 ∨ e.pc = 1155)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1) :
    (w0Fin ((X.tr g).take k)).1.length = r := by
  have := w0_cnt_st hp hX hFw hw he hub hpc
  omega

/-- **The block index of the vote**: the vote at pc 578 has made as many full-mask votes as the
lane has closed blocks, and that is below the CTA's block count. -/
theorem w0_vote_ord (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hpc : e.pc = 578) :
    ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = (w0Fin ((X.tr g).take k)).1.length ∧
      (w0Fin ((X.tr g).take k)).1.length < blocksOf P L (g / L.block) := by
  have hg := Frame.lt_of_get hX he
  have hub := noUb_kind hnu he
  obtain ⟨σ, hσ, -, hinv, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  rcases w0_bst hFw hnu hw hg hσ with ⟨b, n, rfl, -⟩ | ⟨d, n, rfl, hC, hL, -⟩
  · have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpcσ
    omega
  have hs : d.site = .vote := Wg0.site_vote_of_pc (by rw [← hpc]; exact hpcσ.symm)
  have hreg : d.site.reg = Wg0.Reg.loop := by rw [hs]; rfl
  have hl2 : 2 ≤ d.site.lens := Wg0.lens_two (by rw [hreg]; decide)
  obtain ⟨r, hrR, hv, hn⟩ := vOrd_loop hC hL hreg hl2
  obtain ⟨-, hvc, -, -⟩ := w0_tc hp hX hFw hw hg k (noUbBefore_of_noUb hnu) _ hσ
  have hno := w0_noEarly_pre hp hX hFw hw (noUbBefore_of_noUb hnu : LaneUbFree X g k)
  rw [w0Fin_length hno, w0Closed_arrs hp hX hFw hw (noUbBefore_of_noUb hnu : LaneUbFree X g k),
    arrs_counts hp hn (fun l => wg0_arrivals hp hX hFw hw k l)]
  have hz : ¬ 38 < d.site.ord := by rw [hs]; decide
  simp only [hz, ↓reduceIte, add_zero] at hv
  exact ⟨hvc.trans hv, hrR⟩

/-- **The barrier count of a P store**: a store of the lane at pc 704 to 707 is after `2 r + 2`
barrier-9 events, `r` the number of closed blocks. -/
theorem w0_cnt_pst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hw : warp L g < 4)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : 704 ≤ e.pc ∧ e.pc < 708) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * (w0Fin ((X.tr g).take k)).1.length + 2 :=
  by
  have hal := noUbBefore_of_get hX he
  have hno := w0_noEarly_pre hp hX hFw hw hal
  rw [w0Fin_length hno, w0Closed_arrs hp hX hFw hw hal]
  obtain ⟨d, hR, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  obtain ⟨hC, hL, -, ht⟩ := hR (wg0_take_noUb hX he)
  have hB : w0BarCnt X g k = Wg0.barOrd d := ht
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) k hal, hB]
  have hA := fun l => wg0_arrivals hp hX hFw hw k l
  have hs : d.site = .ost ⟨e.pc - 704, by omega⟩ :=
    Wg0.Data.site_pc_ost (by omega) (by rw [← hpc']; omega)
  have hl2 : 2 ≤ d.site.lens := by rw [hs]; simp [Wg0.Site.lens]
  obtain ⟨r', hrR, ho, hn⟩ := barOrd_loop hC hL (by rw [hs]; rfl) hl2
  simp only [hs, Wg0.Site.bidx] at ho
  rw [ho, (w0Cnt9_site _ _ hrR).2]
  rw [arrs_counts hp hn hA]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
