-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The collectives of warps 0 to 3

`w0Cls`: the `CollCls` of the lanes of warp `w < 4` of one CTA: the startup's collectives, and for
the warps 0 and 1 the four elections of the output chunks. The barrier of a chunk (named barrier
9 of the warpgroup) is followed by its election, so after it the lanes of the warp are at the
election having made their barrier of the same ordinal (`w0_last`, the barrier arm of `CollCls`;
`w0_obarCnt`: the barrier-9 events before the barrier of chunk `c` are `2 R + 2 + c`). -/

/-! # The times of the collectives of warps 0 to 3

The slots of warp `w`'s collectives in a CTA of `R` blocks: the startup's (`pc + 2`: shuffles at 6
and 9, the elections of warp 0 at 16 and 31), then the four output chunks' elections of the warps
0 and 1 at warpgroup 0's epilogue (`roleBase + wg0EpiBlk0 + stride * R + 7 + 38 c + 36`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **The slot of the `n`-th collective** of warp `w` in a CTA of `R` blocks. -/
def w0Slot (w R n : Nat) : Nat :=
  if n < 2 then (if n = 0 then 8 else 11)
  else if w = 0 ∧ n < 4 then (if n = 2 then 18 else 33)
  else roleBase + wg0EpiBlk0 + stride * R + (7 + 38 * (n - w0Base w)) + 36

theorem w0Slot_mono {w R a b : Nat} (hw : w < 4) (hab : a < b)
    (hb : ((collList w)[b]?).isSome = true) : w0Slot w R a < w0Slot w R b := by
  have hb' : b < (collList w).length := by
    by_contra h
    have := List.getElem?_eq_none (l := collList w) (i := b) (by omega)
    rw [this] at hb
    simp at hb
  interval_cases w <;>
    simp only [collList] at hb' <;> simp at hb' <;>
    interval_cases b <;> interval_cases a <;>
    simp [w0Slot, roleBase, wg0EpiBlk0, loopBase, w0Epi, wg0Org, stride, w0Base]

/-- **The time of a lane of warps 0 to 3 at a collective is its slot.** -/
theorem w0_time_at (hp : Pre P L m) (hFw : Follow P L X) (hub : ¬ HasUb X)
    (hx : x < L.threads) (hw : warpOf L x < 4) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hc : CollAt P L x σ) :
    time P L x σ = w0Slot (warpOf L x) (blocksOf P L (x / L.block)) (ncT P L x σ) := by
  have hc' := collAt_iff.mp hc
  rcases w0_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc'
    show Startup.time d = _
    by_cases h0 : warpOf L x = 0
    · rcases startup_coll_site hW hc' with ⟨j, hj⟩ | ⟨j, hj⟩ <;>
        (obtain ⟨site, x1, x2⟩ := d; simp only at hj; subst hj;
         rw [Startup.time_of_ne (by simp)]; unfold ncT; rw [pc_startup, h0]
         fin_cases j <;> simp [ncW, collList, w0Slot, Startup.Site.pc])
    · obtain ⟨j, hj⟩ := sh_site h0 hW hc'
      obtain ⟨site, x1, x2⟩ := d
      simp only at hj
      subst hj
      rw [Startup.time_of_ne (by simp)]
      unfold ncT
      rw [pc_startup]
      have : ncW (warpOf L x) 6 = 0 ∧ ncW (warpOf L x) 9 = 1 := ⟨ncW_six _, ncW_nine _⟩
      fin_cases j <;> simp [Startup.Site.pc, w0Slot, this]
  · obtain ⟨c, hs⟩ : ∃ c, d.site = .oel c := by
      rw [pc_w0, w0_pc_coll] at hc'
      generalize d.site = s at hc'
      cases s <;> simp [Wg0.Site.isOel] at hc' ⊢
    have hlt := w0_lt2 hp hFw hx hw hσ (by rw [hs]; rfl)
    rcases w0_bst hFw hub hw hx hσ with ⟨d', n', h', -⟩ |
      ⟨d', n', h', hC, hL, -, hB⟩
    · cases h'
    · simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h'
      obtain ⟨rfl, -⟩ := h'
      have hR := Wg0.rounds_blocks hL (by rw [hs]; simp [Wg0.Site.lens])
      have hn : ncT P L x (w0S P L x d n) = w0Base (warpOf L x) + c.val := by
        rw [ncT_w0 hw]
        simp only [hlt, ite_true, Wg0.segOf_site, hs]
        rfl
      rw [hn]
      show roleBase + Wg0.time d = _
      unfold Wg0.time
      rw [Wg0.place_reg (by rw [hs]; simp)]
      simp only [Wg0.regPlace, hs, Wg0.Site.reg, hR, Wg0.Site.ord, Wg0.elOff, Wg0.chunkBase]
      rcases (by omega : warpOf L x = 0 ∨ warpOf L x = 1) with h | h <;>
        simp [w0Slot, w0Base, h, roleBase, wg0EpiBlk0, stride, loopBase, w0Epi, wg0Org] <;>
        split_ifs <;> omega

/-- The most an element adds to a site's place. -/
def elMax : Wg0.Site → Nat
  | .ost _ | .ost2 _ _ => 3
  | .pld _ => 1
  | _ => 0

theorem elOff_le_elMax (d : Wg0.Control.D) : Wg0.elOff d ≤ elMax d.site := by
  unfold Wg0.elOff
  cases d.site <;> simp [elMax]

theorem ord_epi_lt {s : Wg0.Site} {c : Nat} (hr : s.reg = .epi) (ho : s.isOel = false)
    (hs : s.seg ≤ c) (hc : c < 4) : s.ord + elMax s < 43 + 38 * c := by
  cases s <;> simp only [Wg0.Site.reg, reduceCtorEq] at hr <;>
    simp only [Wg0.Site.ord, Wg0.Site.seg, Wg0.Site.isOel, Wg0.chunkBase, w0Wsv, elMax,
      Bool.true_eq_false] at ho hs ⊢ <;>
    (try have := ‹Fin 4›.isLt) <;> (try have := ‹Fin 8›.isLt) <;> omega

/-- **A state of warpgroup 0 that is no election and is before the election `c`** is placed
before it. -/
theorem w0_place_lt {d : Wg0.Control.D} {n : Wg0.Cnt → Nat} (hC : Wg0.RefCore L x d n)
    (hL : Wg0.LaunchOk P L x d) {c : Nat} (hs : d.site.seg ≤ c) (hc : c < 4)
    (ho : d.site.isOel = false) :
    Wg0.place d < wg0EpiBlk0 + stride * blocksOf P L (x / L.block) + (7 + 38 * c) + 36 := by
  have h26 := Wg0.rounds_lt d.l0 d.l1
  have he := elOff_le_elMax d
  have hseg4 : ¬ (d.site = .ebar ∨ d.site = .dealloc ∨ d.site = .exit) := by
    rintro (h | h | h) <;> simp [Wg0.Site.seg, h] at hs <;> omega
  rw [Wg0.place_reg (by tauto)]
  unfold Wg0.RefCore at hC
  have hrg : d.site.reg = .setup ∨ d.site.reg = .loop ∨ d.site.reg = .epi := by
    generalize d.site = s at hseg4 ⊢
    cases s <;> simp_all [Wg0.Site.reg]
  rcases hrg with hk | hk | hk
  · have ho5 : d.site.ord ≤ 5 := by
      generalize d.site = s at hk
      cases s <;> simp_all [Wg0.Site.reg, Wg0.Site.ord, w0ArrL]
    simp only [Wg0.regPlace, hk]
    simp only [wg0EpiBlk0, loopBase, w0Epi, wg0Org, stride]
    omega
  · have hR := Wg0.rounds_blocks hL (by
      generalize d.site = s at hk
      cases s <;> simp_all [Wg0.Site.reg, Wg0.Site.lens])
    rw [hk] at hC
    obtain ⟨r, ⟨-, hR', hr, hbi, -⟩, -⟩ := hC
    simp only [Wg0.Control.D.words] at hbi hr
    have hlp := Wg0.ord_loop_le d.site hk
    have := Wg0.elOff_le d
    simp only [Wg0.regPlace, hk, hbi, toNat_W (show r + 1 < 2 ^ 64 by omega)]
    rw [← hR] at *
    simp only [wg0Blk0, wg0Off, wg0EpiBlk0, loopBase, w0Epi, wg0Org, stride]
    omega
  · have hR := Wg0.rounds_blocks hL (by
      generalize d.site = s at hk hseg4
      cases s <;> simp_all [Wg0.Site.reg, Wg0.Site.lens])
    have := ord_epi_lt hk ho hs hc
    simp only [Wg0.regPlace, hk, hR]
    omega

theorem startup_lt {w R n t p : Nat} (hw : w < 4) (hn : n < (collList w).length)
    (hle : ncW w p ≤ n) (ht : t ≤ p + 2) (hlt : t < 100) (hp : p ≤ 97) (h6 : p ≠ 6)
    (h9 : p ≠ 9) (h16 : w = 0 → p ≠ 16) (h31 : w = 0 → p ≠ 31) : t < w0Slot w R n := by
  have a1 : ¬ 1350 < p := by omega
  have a2 : ¬ 1507 < p := by omega
  have a3 : ¬ 1664 < p := by omega
  have a4 : ¬ 1822 < p := by omega
  interval_cases w <;>
    simp [ncW, collList, List.filter_cons, a1, a2, a3, a4] at hn hle <;>
    simp only [w0Slot, roleBase, wg0EpiBlk0, stride, loopBase, w0Epi, wg0Org] <;>
    split_ifs at hle ⊢ <;> (try simp only [List.length_cons, List.length_nil] at hle) <;>
      first | omega | simp_all

theorem w0_time_lt (hFw : Follow P L X) (hub : ¬ HasUb X)
    (hx : x < L.threads) (hw : warpOf L x < 4) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hc : ¬ CollAt P L x σ) {n : Nat}
    (hn : ((collList (warpOf L x))[n]?).isSome = true) (hle : ncT P L x σ ≤ n) :
    time P L x σ < w0Slot (warpOf L x) (blocksOf P L (x / L.block)) n := by
  have hn' : n < (collList (warpOf L x)).length := by
    by_contra h
    have := List.getElem?_eq_none (l := collList (warpOf L x)) (i := n) (by omega)
    rw [this] at hn
    simp at hn
  rcases w0_cls hFw hx hw hσ with ⟨d, n0, rfl, hW, hxd⟩ | ⟨d, n0, rfl⟩
  · have hc' : (thread P L x).pc (.inl d, n0) ∉ collPcs := fun h => hc (collAt_iff.mpr h)
    rw [pc_startup] at hc'
    have ht : Startup.time d ≤ d.site.pc + 2 := Startup.time_le d
    have hlt := Startup.time_lt hxd
    have h6 : d.site.pc ≠ 6 := fun h => hc' (h ▸ by decide)
    have h9 : d.site.pc ≠ 9 := fun h => hc' (h ▸ by decide)
    have h16 : d.site.pc ≠ 16 := fun h => hc' (h ▸ by decide)
    have h31 : d.site.pc ≠ 31 := fun h => hc' (h ▸ by decide)
    unfold ncT at hle
    rw [pc_startup] at hle
    have hp97 := Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hxd
    exact startup_lt hw hn' hle ht hlt hp97 h6 h9 (fun _ => h16) (fun _ => h31)
  · have hno : d.site.isOel = false := by
      cases h : d.site.isOel
      · rfl
      · exact absurd (collAt_iff.mpr (by rw [pc_w0, w0_pc_coll]; exact h)) hc
    have hlen : (collList (warpOf L x)).length = w0Base (warpOf L x) + 4 ∨ 2 ≤ warpOf L x := by
      rcases (by omega : warpOf L x = 0 ∨ warpOf L x = 1 ∨ 2 ≤ warpOf L x) with h | h | h <;>
        simp [h, collList, w0Base]
    have hlt : warpOf L x < 2 := by
      by_contra h2
      have h2' : 2 ≤ warpOf L x := by omega
      rw [ncT_w0 hw] at hle
      simp only [show ¬ warpOf L x < 2 by omega, ite_false, w0Base] at hle
      have : (collList (warpOf L x)).length = 2 := by
        rcases (by omega : warpOf L x = 2 ∨ warpOf L x = 3) with h | h <;> simp [h, collList]
      split_ifs at hle <;> omega
    rcases w0_bst hFw hub hw hx hσ with ⟨d', n', h', -⟩ | ⟨d', n', h', hC, hL, -, hB⟩
    · cases h'
    · simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h'
      obtain ⟨rfl, -⟩ := h'
      rw [ncT_w0 hw] at hle
      simp only [hlt, ite_true, Wg0.segOf_site] at hle
      have hc4 : n - w0Base (warpOf L x) < 4 := by
        rcases hlen with h | h <;> omega
      have hp := w0_place_lt (P := P) (L := L) (x := x) hC hL
        (c := n - w0Base (warpOf L x)) (by omega) hc4 hno
      show roleBase + Wg0.time d < _
      unfold Wg0.time
      have hb : w0Base (warpOf L x) ≤ n := by omega
      rcases (by omega : warpOf L x = 0 ∨ warpOf L x = 1) with h | h <;>
        simp [w0Slot, w0Base, h, roleBase] at hb hp ⊢ <;>
        split_ifs <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **The barrier-9 events before the barrier of chunk `c`** of a lane of warps 0 to 3. -/
theorem w0_obarCnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {t : Nat} (hw : warpOf L x < 4) (hy : x < L.threads)
    {d : Wg0.Control.D} {n : Cls → Nat} {c : Fin 4}
    (hσ : Frame.stateAt (thread P L) X x t = some (some (w0S P L x d n)))
    (hs : d.site = .obar c) :
    ((X.tr x).take t).countP (Execution.isBarId 9) = 2 * blocksOf P L (x / L.block) + 2 + c := by
  rcases w0_bst hFw hnu hw hy hσ with ⟨_, _, h, -⟩ | ⟨d', n', h, hC, hL, -, hB⟩
  · cases h
  simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  have hsb : d.site.isBar = true := by rw [hs]; rfl
  have hO : Wg0.barOrd d = 3 * blocksOf P L (x / L.block) + 2 + c := by
    rcases Wg0.bar_ord hsb hC hL with ⟨hr, -⟩ | ⟨-, ho⟩
    · rw [hs] at hr; cases hr
    · rw [ho, hs]; simp only [Wg0.Site.bidx]; omega
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) t hnu, w0BarCnt, Wg0.barTot]
  simp only [Wg0.barTot] at hB
  rw [hB, hO, Nat.add_assoc, w0Cnt9_epi _ _ _ (by omega)]
  omega

theorem obar_of {s : Wg0.Site} (h : s.isObar = true) : ∃ c, s = .obar c := by
  cases s <;> simp [Wg0.Site.isObar] at h ⊢

/-- **The startup's collectives are before the elections.** -/
theorem startup_ncT_lt {d : Startup.D} {n : Cls → Nat} (hc : CollAt P L x (.inl d, n))
    (hxd : Startup.exitOf d = none) (hW : Startup.RefW L x d (n .shfl)) :
    ncT P L x (.inl d, n) < w0Base (warpOf L x) := by
  have hc' := collAt_iff.mp hc
  rw [pc_startup] at hc'
  have hle := Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hxd
  unfold ncT
  rw [pc_startup]
  by_cases h0 : warpOf L x = 0
  · rcases startup_coll_site hW hc' with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rw [hj] <;> fin_cases j <;>
      simp [Startup.Site.pc, h0, ncW, collList, w0Base]
  · obtain ⟨j, hj⟩ := sh_site h0 hW hc'
    rw [hj]
    have h6 := ncW_six (warpOf L x)
    have h9 := ncW_nine (warpOf L x)
    fin_cases j <;> simp [Startup.Site.pc, h6, h9, w0Base, h0]

theorem w0_succ_ne {w : BitVec 64} {d : Wg0.Control.D} {e : Event}
    (hev : Wg0.Ev P L x w d e) (hne : ∀ f, e.kind ≠ .ub f)
    (hb : ¬ Sched.Unblocking e.kind) :
    Wg0.Control.succ P L x w d e ≠ none := by
  obtain ⟨-, hK⟩ := hev
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  unfold Wg0.EvK at hK
  simp only at hK
  cases site <;> first
    | (simp [Wg0.Control.succ]; done)
    | (exfalso; apply hb
       aesop (config := { terminal := true }) (add norm simp [Sched.Unblocking, Wg0.PollEv,
         Wg0.ArrEv, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, RdAt, WrAt, GenWrAt, GWrAt]))
    | (rcases hK with ⟨vals, hk⟩ | ⟨f, hk⟩
       · rename_i k
         fin_cases k <;> simp [Wg0.Control.succ, Wg0.Control.tcLoad, hk]
       · exact absurd hk (hne f))

/-- **After a blocking event of a lane of warps 0 to 3** the machine runs on, at no election, or
(after the barrier of a chunk) at its election, at which every lane of the warp has made its
barrier-9 event of the same ordinal. -/
theorem w0_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) {w c : Nat} (hA : W0Lane L w c x) (hw4 : w < 4)
    {k : Nat} {σ : (thread P L x).D} {e : Event} (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' ∨ (∃ id cnt, e.kind = .bar id cnt .sync ∧
        ∀ y σy, W0Lane L w c y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          ncT P L y σy = ncT P L x σ' → ∃ pc cnt', X.get (y, (X.tr y).length - 1) =
            some ⟨pc, .bar id cnt' .sync⟩ ∧
            ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId id) =
              ((X.tr x).take k).countP (Execution.isBarId id)) := by
  obtain ⟨hx, rfl, rfl⟩ := hA
  have hw : warpOf L x < 4 := hw4
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  rcases w0_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · obtain ⟨h1, h2⟩ := startup_last hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' hn => .inl fun hc => h2 σ' hn (collAt_iff.mp hc)⟩
  obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  have hev' : Wg0.Ev P L x (warpW L x) d e := hev
  refine ⟨?_, fun σ' hn => ?_⟩
  · intro h
    rw [next_frag] at h
    simp only [Option.map_eq_none_iff] at h
    exact w0_succ_ne hev' hne hb h
  · obtain ⟨d', hsu, rfl⟩ := w0_next hn
    by_cases hoel : d'.site.isOel = true
    · right
      have hg : scmpi .gt .s (warpW L x) 1 = false := by
        obtain ⟨-, hgt⟩ := Wg0.succ_oel (batch_in hp x) hsu hoel
        exact hgt
      obtain ⟨hobar, -⟩ := Wg0.succ_oel (batch_in hp x) hsu hoel
      obtain ⟨c, hsd⟩ := obar_of hobar
      have hd' := Wg0.succ_obar hg hsd hsu
      obtain ⟨-, hK⟩ := hev'
      have hk : e.kind = .bar 9 (some 128) .sync := by
        unfold Wg0.EvK at hK
        rw [hsd] at hK
        exact hK
      refine ⟨9, some 128, hk, fun y σy hy hs hσy hcy hnc => ?_⟩
      have hyy : y < L.threads := hy.1
      have hwy : warpOf L y = warpOf L x := hy.2.1
      have hwy4 : warpOf L y < 4 := by omega
      have hcta : y / L.block = x / L.block := hs.1.2.2
      rcases w0_cls hFw hyy hwy4 hσy with ⟨dy, ny, rfl, hWy, hxdy⟩ | ⟨dy, ny, rfl⟩
      · have h1 := startup_ncT_lt hcy hxdy hWy
        rw [ncT_w0 hw] at hnc
        simp only [hwy] at h1
        have : w0Base (warpOf L x) ≤ ncT P L x (w0S P L x d' (Code.bump cls n e)) := by
          rw [ncT_w0 hw]; omega
        omega
      · have hlen : 0 < (X.tr y).length := by
          by_contra h0
          rw [Nat.eq_zero_of_not_pos h0, Frame.stateAt_zero] at hσy
          cases hσy
        obtain ⟨ey, hey⟩ : ∃ ey, (X.tr y)[(X.tr y).length - 1]? = some ey :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hst : Frame.stateAt (thread P L) X y ((X.tr y).length - 1 + 1) =
            some (some (w0S P L y dy ny)) := by
          rw [Nat.sub_add_cancel hlen]; exact hσy
        obtain ⟨σm, hσm, hnm⟩ := prev_state hey hst
        have heyget : X.get (y, (X.tr y).length - 1) = some ey := hey
        have hney : ∀ f, ey.kind ≠ .ub f := fun f hf => hub ⟨(y, (X.tr y).length - 1), ey.pc, f, by
          rw [heyget]; obtain ⟨pc, kd⟩ := ey; simp only at hf; rw [hf]⟩
        have hdyoel : dy.site.isOel = true := by
          simpa [pc_w0, w0_pc_coll] using collAt_iff.mp hcy
        rcases w0_cls hFw hyy hwy4 hσm with ⟨dm, nm, rfl, hWm, -⟩ | ⟨dm, nm, rfl⟩
        · have := startup_to_w0 hp hwy4 hWm hnm rfl
          rw [this] at hdyoel
          cases hdyoel
        · obtain ⟨dy', hsuy, hσyeq⟩ := w0_next hnm
          simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
            true_and] at hσyeq
          obtain ⟨rfl, -⟩ := hσyeq
          obtain ⟨hobm, hgm⟩ := Wg0.succ_oel (batch_in hp y) hsuy hdyoel
          obtain ⟨cm, hsm⟩ := obar_of hobm
          have hgm' : scmpi .gt .s (warpW L y) 1 = false := hgm
          have hdy := Wg0.succ_obar hgm' hsm hsuy
          have hcc : cm.val = c.val := by
            have hlt2 : warpOf L x < 2 := by
              have := gt_warpW (L := L) (x := x) (by omega)
              rw [hg] at this
              simpa using this
            rw [ncT_w0 hwy4, ncT_w0 hw, hdy, hd', hwy] at hnc
            simp only [Wg0.segOf_site, Wg0.Site.seg, hlt2, ite_true] at hnc
            omega
          obtain ⟨σ0m, hσ0m, -, -, hevm⟩ := ev_state hp hX hFw heyget hney
          rw [hσm] at hσ0m
          obtain rfl := Option.some.inj (Option.some.inj hσ0m)
          obtain ⟨-, hKm⟩ : Wg0.Ev P L y (warpW L y) dm ey := hevm
          have hkm : ey.kind = .bar 9 (some 128) .sync := by
            unfold Wg0.EvK at hKm
            rw [hsm] at hKm
            exact hKm
          refine ⟨ey.pc, some 128, ?_, ?_⟩
          · obtain ⟨pcy, kdy⟩ := ey
            simp only at hkm
            subst hkm
            exact heyget
          · rw [w0_obarCnt hp hX hFw hub hwy4 hyy hσm hsm,
              w0_obarCnt hp hX hFw hub hw hx hσ hsd, hcta, hcc]
    · exact .inl fun hc => hoel (by simpa [pc_w0, w0_pc_coll] using collAt_iff.mp hc)

theorem W0Lane.lt4 {w c y : Nat} (hA : W0Lane L w c y) (h : w < 4) : warpOf L y < 4 := by
  rw [hA.2.1]; exact h

theorem w0_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) {n : Nat}
    (hn : ((collList (warpOf L x))[n]?).isSome = true) : n < ncT P L x σ := by
  have hn' : n < (collList (warpOf L x)).length := by
    by_contra h
    have := List.getElem?_eq_none (l := collList (warpOf L x)) (i := n) (by omega)
    rw [this] at hn
    simp at hn
  have hpc : pc = (thread P L x).pc σ :=
    Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ (fun f h => by cases h)
  have h3 : pc = 3611 := exit_event_pc hX he
  unfold ncT
  rw [← hpc, h3, ncW_big (by omega)]
  exact hn'

/-- **The collectives of the lanes of warp `w < 4` of CTA `c`.** -/
def w0Cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hub : ¬ HasUb X) (w c : Nat) (hw4 : w < 4) :
    CollCls P L X (W0Lane L w c) (collS P L) where
  cn n := (collList w)[n]?
  slot := w0Slot w (blocksOf P L c)
  nc := ncT P L
  count := fun {y k σ} hA hσ =>
    ncT_count hp hX hub (fun {k σ e σ'} he hσ' hn =>
      w0_step hp hX hFw hub hA.1 (hA.lt4 hw4) he hσ' hn) k σ hσ
  at_ := fun {y k σ} hA hσ => by
    have h := w0_at hp hFw hA.1 (hA.lt4 hw4) hσ
    rwa [hA.2.1] at h
  isP := fun hA hσ he hc => coll_isP hp hX hσ he hc
  slot_mono := fun {a b} hab hb => w0Slot_mono hw4 hab hb
  time_at := fun {y k σ} hA hσ hc => by
    have h := w0_time_at hp hFw hub hA.1 (hA.lt4 hw4) hσ hc
    rwa [hA.2.1, hA.2.2] at h
  time_lt := fun {y k σ} hA hσ hc n hn hle => by
    have h := w0_time_lt hFw hub hA.1 (hA.lt4 hw4) hσ hc (by rwa [hA.2.1]) hle
    rwa [hA.2.1, hA.2.2] at h
  static := fun {y z k k' σ σ'} hA hB hσ hσ' hc hc' hn => by
    have h1 := (w0_at hp hFw hA.1 (hA.lt4 hw4) hσ).mp hc
    have h2 := (w0_at hp hFw hB.1 (hB.lt4 hw4) hσ').mp hc'
    rw [hA.2.1] at h1
    rw [hB.2.1] at h2
    have hn' : ncT P L y σ = ncT P L z σ' := hn
    rw [hn', h2] at h1
    have := Option.some.inj h1
    show pcShape _ = pcShape _
    rw [this]
  exit := fun {y k pc σ} hA hσ he n hn => by
    have h := w0_exit hp hX hσ he (n := n) (by rwa [hA.2.1])
    exact h
  last := fun {y k σ e} hA he hσ hb => by
    obtain ⟨h1, h2⟩ := w0_last hp hX hFw hub hA hw4 he hσ hb
    exact ⟨h1, fun σ' h => (h2 σ' h).imp_right .inr⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
