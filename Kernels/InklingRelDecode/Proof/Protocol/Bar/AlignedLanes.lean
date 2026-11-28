-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedKind
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Common.Export.BarPc
import Kernels.InklingRelDecode.Proof.Common.Export.WorkerBarPc
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Lemmas.Flow.OrdinalCount

@[expose] public section

/-! # ERR-ALIGNED, divergence at `barrier{.cta}`

The lanes of a warp at the same barrier ordinal are at the same pc. A worker warp has one pc per
ordinal (`Export.worker_bar_pc`). A data warp has one per ordinal not counting the optional
rendezvous at pc 2326, which takes the place of the fourth fixed rendezvous of a round
(`Export.data_bar_pc`); the lanes agree on it by `rescale_follow`. The induction is over the
ordinal: below it the lanes are at equal pcs, so they have made the same numbers of optional
and publication rendezvous. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
open PTX PTX.Flow Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem clash (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {a ia b ib ca cb}
    (ea : X.get (a,ia) = some ⟨2326, .bar 0 ca .sync⟩)
    (eb : X.get (b,ib) = some ⟨999, .bar 0 cb .sync⟩) (la : a % L.block < 128)
    (lb : b % L.block < 128) (cta : b / L.block = a / L.block)
    (ord : ((X.tr b).take ib).countP (Execution.isBarId 0) =
      ((X.tr a).take ia).countP (Execution.isBarId 0)) : False := by
  have uni := rescale_agree hp hX hf safe ea (fun _ => nofun) (by dsimp only; decide)
    (by dsimp only; decide) la
  have := rescale_follow hp hX hf safe uni la lb cta ea rfl eb (by decide) ord
  omega

private theorem ord_eq {Q' : Event → Bool} {g j n' : Nat} {e : Event}
    (he : X.get (g,j) = some e) (be : Execution.isBar e = true)
    (c : ((X.tr g).take j).countP Execution.isBar = n') :
    ordEv X Execution.isBar Q' g n' = Q' e := by
  rw [← c]
  exact ordEv_eq he be

private theorem count_eq {Q' : Event → Bool} (hqp : ∀ e, Q' e = true → Execution.isBar e = true)
    {x ix y iy n}
    (ox : ((X.tr x).take ix).countP Execution.isBar = n)
    (oy : ((X.tr y).take iy).countP Execution.isBar = n)
    (same : ∀ n' < n, ordEv X Execution.isBar Q' x n' = ordEv X Execution.isBar Q' y n') :
    ((X.tr x).take ix).countP Q' = ((X.tr y).take iy).countP Q' := by
  rw [countP_ordinal hqp, countP_ordinal hqp, ox, oy]
  exact List.countP_congr fun n' mem => by rw [same n' (List.mem_range.mp mem)]

private theorem rescale_isBar (e : Event) (h : rescaleBar e = true) : Execution.isBar e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [rescaleBar, Execution.isBarId, Execution.isBar]

private theorem one_isBar (e : Event) (h : Execution.isBarId 1 e = true) :
    Execution.isBar e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isBarId, Execution.isBar]

private theorem data_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) (n : Nat) :
    ∀ {x ix y iy px py kx ky}, x / L.block = y / L.block → x % L.block < 128 →
      y % L.block < 128 →
      X.get (x,ix) = some ⟨px,kx⟩ → X.get (y,iy) = some ⟨py,ky⟩ →
      Execution.isBar ⟨px,kx⟩ = true → Execution.isBar ⟨py,ky⟩ = true →
      ((X.tr x).take ix).countP Execution.isBar = n →
      ((X.tr y).take iy).countP Execution.isBar = n → px = py := by
  have hb : L.block = 256 := hp.block
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ix y iy px py kx ky cta lx ly hx hy bx by' ox oy
  obtain ⟨ax, nx, dx, rfl⟩ := bar_shape bx
  obtain ⟨ay, ny, dy, rfl⟩ := bar_shape by'
  have early : ∀ n' < n, ∃ jx jy ex ey, X.get (x,jx) = some ex ∧ X.get (y,jy) = some ey ∧
      Execution.isBar ex = true ∧ Execution.isBar ey = true ∧
      ((X.tr x).take jx).countP Execution.isBar = n' ∧
      ((X.tr y).take jy).countP Execution.isBar = n' ∧ ex.pc = ey.pc := by
    intro n' lt
    obtain ⟨jx, ⟨qx, kx'⟩, -, gx, bx', cx⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := x)
      (k := ix) (n := n') (by omega)
    obtain ⟨jy, ⟨qy, ky'⟩, -, gy, by'', cy⟩ := exists_nthEv (X := X) (p := Execution.isBar)
      (g := y) (k := iy) (n := n') (by omega)
    exact ⟨jx, jy, _, _, gx, gy, bx', by'', cx, cy, ih n' lt cta lx ly gx gy bx' by'' cx cy⟩
  have same {Q' : Event → Bool}
      (id : ∀ e e' : Event, e.pc = e'.pc → Execution.isBarId 0 e = Execution.isBarId 0 e' →
        Execution.isBarId 1 e = Execution.isBarId 1 e' → Q' e = Q' e') :
      ∀ n' < n, ordEv X Execution.isBar Q' x n' = ordEv X Execution.isBar Q' y n' := by
    intro n' lt
    obtain ⟨jx, jy, ex, ey, gx, gy, bex, bey, cx, cy, pcs⟩ := early n' lt
    rw [ord_eq gx bex cx, ord_eq gy bey cy]
    obtain ⟨pe, ke⟩ := ex
    obtain ⟨pf, kf⟩ := ey
    simp only at pcs
    subst pcs
    exact id _ _ rfl (isBarId_of_pc hX hb gx gy bex bey 0) (isBarId_of_pc hX hb gx gy bex bey 1)
  have res : ((X.tr x).take ix).countP rescaleBar = ((X.tr y).take iy).countP rescaleBar :=
    count_eq rescale_isBar ox oy (same fun e e' hpc h0 _ => by simp only [rescaleBar, h0, hpc])
  have one : ((X.tr x).take ix).countP (Execution.isBarId 1) =
      ((X.tr y).take iy).countP (Execution.isBarId 1) :=
    count_eq one_isBar ox oy (same fun e e' _ _ h1 => h1)
  have sx := bar_count_split (g := x) (k := ix) hX hb
  have sy := bar_count_split (g := y) (k := iy) hX hb
  have zero : ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0) := by omega
  have rx := count_rescale hp hX hx
  have ry := count_rescale hp hX hy
  have kx := Export.data_bar_pc hp hX hf hx lx
  have ky := Export.data_bar_pc hp hX hf hy ly
  dsimp only at kx ky
  rw [← cta] at ky
  have teq : ((X.tr x).take ix).countP (Execution.isBarId 0) +
      ((X.tr x).take ix).countP (Execution.isBarId 1) -
      ((X.tr x).take ix).countP (fun e => e.pc == 2326) =
      ((X.tr y).take iy).countP (Execution.isBarId 0) +
      ((X.tr y).take iy).countP (Execution.isBarId 1) -
      ((X.tr y).take iy).countP (fun e => e.pc == 2326) := by
    rw [rx, ry, res, zero, one]
  rw [teq] at kx
  have off : ∀ q, q = 999 ∨ q = 2326 → q ∉ Lib.barOneSites := by
    rintro q (rfl | rfl) <;> decide
  rcases kx with h | ⟨h, h'⟩ <;> rcases ky with g | ⟨g, g'⟩
  · exact h.trans g.symm
  · exfalso
    obtain ⟨ix0, dx0⟩ := zero_sync hX hb hx (off _ (.inl (h.trans g')))
    obtain ⟨iy0, dy0⟩ := zero_sync hX hb hy (off _ (.inr g))
    subst ix0 iy0 dx0 dy0
    rw [h.trans g'] at hx
    rw [g] at hy
    exact clash hp hX hf safe hy hx ly lx cta zero
  · exfalso
    obtain ⟨ix0, dx0⟩ := zero_sync hX hb hx (off _ (.inr h))
    obtain ⟨iy0, dy0⟩ := zero_sync hX hb hy (off _ (.inl (g.trans h')))
    subst ix0 iy0 dx0 dy0
    rw [g.trans h'] at hy
    rw [h] at hx
    exact clash hp hX hf safe hx hy lx ly cta.symm zero.symm
  · exact h.trans g.symm

/-- **Two data lanes of a CTA at the same barrier ordinal are at the same pc.** -/
theorem data_bar_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy px py kx ky}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨px,kx⟩) (hy : X.get (y,iy) = some ⟨py,ky⟩)
    (bx : Execution.isBar ⟨px,kx⟩ = true) (by' : Execution.isBar ⟨py,ky⟩ = true)
    (ord : ((X.tr x).take ix).countP Execution.isBar = ((X.tr y).take iy).countP Execution.isBar) :
    px = py :=
  data_agree hp hX hf safe _ cta lx ly hx hy bx by' rfl ord.symm

private theorem zero_isBar (e : Event) (h : Execution.isBarId 0 e = true) :
    Execution.isBar e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isBarId, Execution.isBar]

private theorem ord_same (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy N}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hxN : N ≤ ((X.tr x).take ix).countP Execution.isBar)
    (hyN : N ≤ ((X.tr y).take iy).countP Execution.isBar) {Q' : Event → Bool}
    (id : ∀ e e' : Event, e.pc = e'.pc → Execution.isBarId 0 e = Execution.isBarId 0 e' →
      Execution.isBarId 1 e = Execution.isBarId 1 e' → Q' e = Q' e') :
    ∀ n' < N, ordEv X Execution.isBar Q' x n' = ordEv X Execution.isBar Q' y n' := by
  intro n' lt
  obtain ⟨jx, ⟨qx, kx⟩, -, gx, bx, cx⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := x)
    (k := ix) (n := n') (by omega)
  obtain ⟨jy, ⟨qy, ky⟩, -, gy, by', cy⟩ := exists_nthEv (X := X) (p := Execution.isBar)
    (g := y) (k := iy) (n := n') (by omega)
  have pcs := data_bar_agree hp hX hf safe cta lx ly gx gy bx by' (cx.trans cy.symm)
  rw [ord_eq gx bx cx, ord_eq gy by' cy]
  subst pcs
  exact id _ _ rfl (isBarId_of_pc hX hp.block gx gy bx by' 0)
    (isBarId_of_pc hX hp.block gx gy bx by' 1)

private theorem zero_lt_false (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy pc c md}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨pc,.bar 0 c md⟩)
    (ord : ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0))
    (lt : ((X.tr x).take ix).countP Execution.isBar < ((X.tr y).take iy).countP Execution.isBar) :
    False := by
  have hb : L.block = 256 := hp.block
  obtain ⟨j, ⟨q, kq⟩, hj, gj, bj, cj⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := y)
    (k := iy) (n := ((X.tr x).take ix).countP Execution.isBar) (by omega)
  have bx : Execution.isBar ⟨pc, .bar 0 c md⟩ = true := by simp [Execution.isBar]
  have same := ord_same hp hX hf safe cta lx ly le_rfl lt.le (Q' := Execution.isBarId 0)
    (fun e e' _ h0 _ => h0)
  have c0eq := count_eq (Q' := Execution.isBarId 0) zero_isBar rfl cj same
  have pq := data_bar_agree hp hX hf safe cta lx ly hx gj bx bj cj.symm
  obtain ⟨id', cnt', md', rfl⟩ := bar_shape bj
  have i0 := bar_id_of_pc hX hb hx
  have i1 := bar_id_of_pc hX hb gj
  subst pq
  have hid : id' = 0 := i1.trans i0.symm
  subst hid
  have step := countP_take_succ (p := Execution.isBarId 0) gj (by simp [Execution.isBarId])
  have mono := countP_take_mono (Execution.isBarId 0) (X.tr y) (show j + 1 ≤ iy from hj)
  omega

/-- **Two data lanes of a CTA with the same number of earlier barrier-0 events have the same
number of earlier barrier events.** -/
theorem zero_count_isBar (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy pc pc' c c' md md'}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨pc,.bar 0 c md⟩) (hy : X.get (y,iy) = some ⟨pc',.bar 0 c' md'⟩)
    (ord : ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0)) :
    ((X.tr x).take ix).countP Execution.isBar = ((X.tr y).take iy).countP Execution.isBar := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · exact zero_lt_false hp hX hf safe cta lx ly hx ord lt
  · exact zero_lt_false hp hX hf safe cta.symm ly lx hy ord.symm gt

private theorem final_lt_false (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy px py}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨px,.bar 0 none .sync⟩)
    (hy : X.get (y,iy) = some ⟨py,.bar 0 none .sync⟩)
    (ox : 2 ≤ ((X.tr x).take ix).countP (Execution.isBarId 0))
    (oy : 2 ≤ ((X.tr y).take iy).countP (Execution.isBarId 0))
    (lt : ((X.tr x).take ix).countP Execution.isBar < ((X.tr y).take iy).countP Execution.isBar) :
    False := by
  obtain ⟨j, ⟨q, kq⟩, hj, gj, bj, cj⟩ := exists_nthEv (X := X) (p := Execution.isBar) (g := y)
    (k := iy) (n := ((X.tr x).take ix).countP Execution.isBar) (by omega)
  have bx : Execution.isBar ⟨px, .bar 0 none .sync⟩ = true := by simp [Execution.isBar]
  have pq := data_bar_agree hp hX hf safe cta lx ly hx gj bx bj cj.symm
  subst pq
  have fin := (Export.final_late hp hX hx).mpr ox
  have first := Export.final_first hp hX hy ((Export.final_late hp hX hy).mpr oy)
  have mem : (⟨px, kq⟩ : Event) ∈ (X.tr y).take iy :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact gj)
  exact List.countP_eq_zero.mp first _ mem fin

/-- **Two data lanes of a CTA agree on the number of barrier-zero events before their
last-generation arrival.** -/
theorem final_ordinal_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy px py}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨px,.bar 0 none .sync⟩)
    (hy : X.get (y,iy) = some ⟨py,.bar 0 none .sync⟩)
    (ox : 2 ≤ ((X.tr x).take ix).countP (Execution.isBarId 0))
    (oy : 2 ≤ ((X.tr y).take iy).countP (Execution.isBarId 0)) :
    ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0) := by
  have eq : ((X.tr x).take ix).countP Execution.isBar =
      ((X.tr y).take iy).countP Execution.isBar := by
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt | gt
    · exact final_lt_false hp hX hf safe cta lx ly hx hy ox oy lt
    · exact final_lt_false hp hX hf safe cta.symm ly lx hy hx oy ox gt
  have same := ord_same hp hX hf safe cta lx ly le_rfl eq.le (Q' := Execution.isBarId 0)
    (fun e e' _ h0 _ => h0)
  exact count_eq (Q' := Execution.isBarId 0) zero_isBar rfl eq.symm same

private theorem cnt_of_pc (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256)
    {i j pc c c' md md'} (hi : X.get i = some ⟨pc,.bar 0 c md⟩)
    (hj : X.get j = some ⟨pc,.bar 0 c' md'⟩) : c = c' := by
  obtain ⟨-, r⟩ := Lib.recorded_bar hX hb hi
  obtain ⟨-, r'⟩ := Lib.recorded_bar hX hb hj
  have disj : ∀ p ∈ BarRow.fullZeroSites, p ∉ BarRow.halfZeroSites := by decide
  rcases r with ⟨h, -⟩ | ⟨-, e, f⟩ | ⟨-, e, hh⟩
  · exact absurd h (by decide)
  · rcases r' with ⟨h', -⟩ | ⟨-, e', f'⟩ | ⟨-, e', hh'⟩
    · exact absurd h' (by decide)
    · exact e.trans e'.symm
    · exact absurd hh' (disj _ f)
  · rcases r' with ⟨h', -⟩ | ⟨-, e', f'⟩ | ⟨-, e', hh'⟩
    · exact absurd h' (by decide)
    · exact absurd hh (disj _ f')
    · exact e.trans e'.symm

/-- **Two data lanes of a CTA agree on the count of their barrier-0 arrival of each ordinal.** -/
theorem alpha_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy pc pc' c c' md md'}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨pc,.bar 0 c md⟩) (hy : X.get (y,iy) = some ⟨pc',.bar 0 c' md'⟩)
    (ord : ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0)) : c = c' := by
  have ordB := zero_count_isBar hp hX hf safe cta lx ly hx hy ord
  have pcs := data_bar_agree hp hX hf safe cta lx ly hx hy (by simp [Execution.isBar])
    (by simp [Execution.isBar]) ordB
  subst pcs
  exact cnt_of_pc hX hp.block hx hy

/-- **The lanes of a warp at the same barrier ordinal are at the same pc.** -/
theorem bar_same_pc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (safe : ¬ Race L X) {x ix y iy px py kx ky}
    (w : SameWarp L x y) (hx : X.get (x,ix) = some ⟨px,kx⟩) (hy : X.get (y,iy) = some ⟨py,ky⟩)
    (bx : Execution.isBar ⟨px,kx⟩ = true) (by' : Execution.isBar ⟨py,ky⟩ = true)
    (ord : ((X.tr x).take ix).countP Execution.isBar = ((X.tr y).take iy).countP Execution.isBar) :
    px = py := by
  have hb : L.block = 256 := hp.block
  by_cases lx : x % L.block < 128
  · exact data_bar_agree hp hX hf safe w.1.2.2 lx (by have := w.2; omega) hx hy bx by' ord
  · obtain ⟨ax, nx, dx, rfl⟩ := bar_shape bx
    obtain ⟨ay, ny, dy, rfl⟩ := bar_shape by'
    have ly : ¬ y % L.block < 128 := by have := w.2; omega
    have a := Export.worker_bar_pc hp hX words hx (by omega)
    have b := Export.worker_bar_pc hp hX words hy (by omega)
    dsimp only at a b
    rw [a, b, ← bar_count_split hX hb, ← bar_count_split hX hb, ord, w.2]

/-- **No two lanes of a warp diverge at `barrier{.cta}`.** -/
theorem not_divergent (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (safe : ¬ Race L X) :
    ¬ AlignedClass.bar.Divergent L kernel X := by
  rintro ⟨e, f, pe, pf, ke, kf, w, he, hf', bx, by', ord, -, hne⟩
  rcases hne with hne | hne
  · exact hne (bar_same_pc hp hX hf words safe w he hf' bx by' ord)
  · exact hne rfl

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Bar
