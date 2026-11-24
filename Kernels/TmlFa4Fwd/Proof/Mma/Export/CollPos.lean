-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's collectives, by their number

`MCls` says where a state of the MMA warp stands: with `N` collectives made, at time `t`, at a
collective (`some` tag) or not. Two lanes of one CTA with one number at a collective have one tag
(`MCls.same`); a lane with at most as many as a lane at a collective, and not at that collective, is
earlier (`MCls.lag`), and has not exited (`MCls.lt_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (Late clk scanBase endBase primeBase shPc PickedC)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Pos selN)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {c : Nat}

/-- The broadcasts and elections before a place. -/
def pipeCnt (q r : Nat) : Nat := shAt q r + electAll q r

/-- The places of the pipeline's collectives. -/
def collQ : List Nat :=
  [3, 4, 5, 7, 10, 11, 13, 15, 22, 23, 24, 25, 30, 31, 33, 36, 37, 38, 42, 44, 46, 48, 60, 62, 66,
    67, 68, 69, 74, 75, 76, 80, 82, 84]

/-- A place and round of a tile of `R` rounds. -/
def PlaceOk (q r R : Nat) : Prop :=
  q < 86 ∧ (q < 20 → r = 0) ∧ (20 ≤ q ∧ q < 60 → r < R) ∧ (60 ≤ q → r = R)

theorem pipeCnt_lin (q r : Nat) : pipeCnt q r = pipeCnt q 0 + 14 * r := by
  simp only [pipeCnt, shAt, electAll, pq]
  norm_num
  omega

private theorem tab1 : ∀ q ∈ collQ, (q < 20 → pipeCnt q 0 < 8) ∧ (q < 60 → pipeCnt q 0 < 22) ∧
    (60 ≤ q → pipeCnt q 0 < 20) := by decide

private theorem tab100 : pipeCnt 100 0 = 20 := by decide

private theorem tab2 : ∀ q < 86, 20 ≤ q → 8 ≤ pipeCnt q 0 := by decide

private theorem tab3 : ∀ q ∈ collQ, ∀ q' < 86, q < q' → (q' < 20 ∨ (20 ≤ q ∧ q' < 60) ∨ 60 ≤ q) →
    pipeCnt q 0 < pipeCnt q' 0 := by decide

/-- **An earlier place by the number of collectives is earlier in time.** -/
theorem place_lt {q r q' r' R : Nat} (hq : q ∈ collQ) (h : PlaceOk q r R) (h' : PlaceOk q' r' R)
    (hle : pipeCnt q' r' ≤ pipeCnt q r) (hne : ¬ (q' = q ∧ r' = r)) :
    Progress.Mm.pipeT p q' r' < Progress.Mm.pipeT p q r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  obtain ⟨b1, b2, -⟩ := tab1 q hq
  have t2' := tab2 q' h1'
  have ht := tab3 q hq q' h1'
  rw [pipeCnt_lin q', pipeCnt_lin q] at hle
  generalize pipeCnt q 0 = a at *
  generalize pipeCnt q' 0 = a' at *
  have key : (if q' < 20 then 0 else r' + 1) < (if q < 20 then 0 else r + 1) ∨
      ((if q' < 20 then 0 else r' + 1) = (if q < 20 then 0 else r + 1) ∧ q' < q) := by
    split_ifs <;> omega
  unfold Progress.Mm.pipeT
  rcases key with h | ⟨h, hlt⟩
  · exact Progress.clk_lt_of_slot h (by unfold Progress.span; omega)
  · rw [h]
    exact Progress.clk_lt_of_off (o := 2 * q') (o' := 2 * q) (by omega)

/-- The choice of the first pass: its collectives. -/
def chN (R : Nat) (bal : BitVec 64) : Nat := 4 + 7 * (R + 1) + selN bal

/-- What a state at a collective is at. -/
inductive CollTag
  | start (j : Fin 3)
  | site (s : Site)

/-- **Where a state of the MMA warp stands**: `N` collectives made, time `t`, the collective it is
at. -/
inductive MCls (p : Params) (L : Launch) (g : Nat) : Nat → Nat → Option CollTag → Prop
  | start (j : Fin 3) : MCls p L g j.val (shPc j.val) (some (.start j))
  | early (t : Nat) (ht : t < scanBase + 6) : MCls p L g 3 t none
  | bcast : MCls p L g 3 (scanBase + 6) (some (.site .bcast))
  | scanOff (n t : Nat) (hn : 3 ≤ n) (ht : t < scanBase + 2 * (n + 1))
      (ht' : t < primeBase p) : MCls p L g (n + 1) t none
  | scan (q : Nat) (s : Site) (hs : s.epi = s.toE) (hsc : s.scan = true)
      (hq : Pos p (g / L.block) false q s.epi) :
      MCls p L g (4 + q) (scanBase + 2 * (4 + q)) (some (.site s))
  | end1 (ns nv t : Nat) (hx : Epilogue.Fits.ExitAt p L g false ns nv) :
      MCls p L g (1 + ns + nv) t none
  | pipe (R0 : Nat) (bal : BitVec 64) (R q r : Nat) (o : Option CollTag)
      (hP : Epilogue.Picked p L g R0 bal) (hR : MmaRounds p L g R) (hp : PlaceOk q r R)
      (ho : ∃ s : Site, s.ord = q ∧ s.pipe = true ∧ (q ∈ collQ → o = some (.site s)) ∧
        ∀ x, o = some x → q ∈ collQ) :
      MCls p L g (1 + chN R0 bal + pipeCnt q r) (Progress.Mm.pipeT p q r) o
  | scan2Off (R0 : Nat) (bal : BitVec 64) (R n t : Nat) (hP : Epilogue.Picked p L g R0 bal)
      (hR : MmaRounds p L g R) (hn : chN R0 bal ≤ n)
      (ht : endBase p ≤ t) (ht' : t < endBase p + 2 * n) :
      MCls p L g (1 + pipeCnt 100 R + n) t none
  | scan2 (R0 : Nat) (bal : BitVec 64) (R n0 v0 q : Nat) (s : Site)
      (hP : Epilogue.Picked p L g R0 bal) (hR : MmaRounds p L g R)
      (hps : Epilogue.PassStart p L g true n0 v0)
      (hs : s.epi = s.toE) (hsc : s.scan = true) (hq : Pos p (g / L.block) true q s.epi) :
      MCls p L g (1 + pipeCnt 100 R + (n0 + v0 + q)) (endBase p + 2 * (n0 + v0 + q))
        (some (.site s))
  | end2 (R0 : Nat) (bal : BitVec 64) (R ns nv t : Nat) (hP : Epilogue.Picked p L g R0 bal)
      (hR : MmaRounds p L g R) (hx : Epilogue.Fits.ExitAt p L g true ns nv) :
      MCls p L g (1 + pipeCnt 100 R + (ns + nv)) t none

theorem pipe_lt_total {q r R : Nat} (hq : q ∈ collQ) (h : PlaceOk q r R) :
    pipeCnt q r < pipeCnt 100 R := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨b1, b2, b3⟩ := tab1 q hq
  rw [pipeCnt_lin q, pipeCnt_lin 100, tab100]
  omega

variable {g h : Nat}

/-- A collective of the first pass is before the choice's end. -/
private theorem pos_chN {q R : Nat} {bal : BitVec 64} {s : Epilogue.Site}
    (hq : Pos p (g / L.block) false q s) (hP : Epilogue.Picked p L g R bal) :
    3 + q < chN R bal := by
  have h1 := Epilogue.pos_late (L := L) (g := g) (n0 := 3) (v0 := 0) (by
    simp [Epilogue.PassStart]) hq
  by_contra hcon
  have : Late p (g / L.block) (3 + 0 + q) := ⟨R, bal, hP, by unfold chN at hcon; omega⟩
  exact absurd (h1.mp this) (by simp)

private theorem chN_ge (R : Nat) (bal : BitVec 64) : 12 ≤ chN R bal := by
  have := (Epilogue.selN_pos bal).1
  unfold chN; omega

private theorem pass2_ge {n0 v0 R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) (hps : Epilogue.PassStart p L g true n0 v0) :
    n0 + v0 = chN R bal := by
  simp only [Epilogue.PassStart, ite_true] at hps
  obtain ⟨R', bal', hP', rfl, rfl⟩ := hps
  obtain ⟨rfl, rfl⟩ := hP'.unique hP
  unfold chN; omega

private theorem picked_cta' {R : Nat} {bal : BitVec 64} (hc : h / L.block = g / L.block)
    (hP : Epilogue.Picked p L h R bal) : Epilogue.Picked p L g R bal := Epilogue.Picked.cta hc hP

private theorem chN_le (hp : Pre p L m) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) : chN R bal ≤ Progress.cmax p := by
  have := Epilogue.chosen_coll_le hp (d := Epilogue.chosenD p (g / L.block) R bal)
    (ns := 3 + 7 * (R + 1) + selN bal) (nv := 1) ⟨hP, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold chN Progress.cmax
  omega

private theorem scan_tag {s s' : Site} (hs : s.epi = s.toE) (hsc : s.scan = true)
    (hs' : s'.epi = s'.toE) (hsc' : s'.scan = true) (h : s.epi = s'.epi) : s = s' := by
  rw [hs, hs'] at h
  cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;> cases s' <;>
    simp only [Site.scan, Bool.false_eq_true] at hsc' <;>
    simp only [Site.toE, reduceCtorEq] at h <;> simp_all

/-- The pipeline's sites. -/
private def pipeSites : List Site :=
  (List.finRange 10).map .wt ++ (List.finRange 14).map .sh ++ (List.finRange 4).map .eq ++
  (List.finRange 4).map .ep ++ (List.finRange 12).map .ce ++ (List.finRange 12).map .cm ++
  ((List.finRange 4).flatMap fun b => (List.finRange 8).map (.qk b) ++
    (List.finRange 8).map (.pv b) ++ [false, true].map (.mw b))

private theorem mem_pipeSites {s : Site} (h : s.pipe = true) : s ∈ pipeSites := by
  cases s <;> simp [Site.pipe] at h <;> simp [pipeSites]
  case mw b ld => cases ld <;> simp

private theorem ord_tag : ∀ {s s' : Site}, s.pipe = true → s'.pipe = true → s.ord ∈ collQ →
    s.ord = s'.ord → s = s' := by
  intro s s' hs hs' hq h
  have key : pipeSites.all (fun y => !collQ.contains y.ord ||
      pipeSites.all (fun z => z.ord != y.ord || z == y)) = true := by decide +kernel
  have h1 := List.all_eq_true.mp key s (mem_pipeSites hs)
  have hq' : collQ.contains s.ord = true := by simpa using hq
  rw [hq'] at h1
  have h2 := List.all_eq_true.mp (by simpa only [Bool.not_true, Bool.false_or] using h1) s'
    (mem_pipeSites hs')
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h2
  exact (h2.resolve_left (by simp [h])).symm

private theorem exit2_ge {ns nv R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L g R bal)
    (hx : Epilogue.Fits.ExitAt p L g true ns nv) : chN R bal ≤ ns + nv := by
  obtain ⟨n1, v1, hps, R1, -, hx⟩ := hx
  have := pass2_ge hP hps
  rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega

/-- The pipeline is before the second scan. -/
theorem early_lt (hp : Pre p L m) (hg : g < L.threads) {q r R : Nat} (h : PlaceOk q r R)
    (hR : MmaRounds p L g R) : Progress.Mm.pipeT p q r < endBase p := by
  have hbm := mma_rounds_bmax hp hg hR
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : (if q < 20 then 0 else r + 1) ≤ Progress.bmax p := by split <;> omega
  have := Progress.clk_lt_tail (p := p) (a := (if q < 20 then 0 else r + 1)) (o := 2 * q)
    (by unfold Progress.span; omega)
  rw [Progress.slotOf_eq hs] at this
  unfold Progress.Mm.pipeT endBase
  omega

set_option maxHeartbeats 4000000 in
/-- **The number of collectives gives the collective**, and the lag of a lane not at it. -/
theorem MCls.order {N N' t t' : Nat} {x : CollTag} {o : Option CollTag} (hp : Pre p L m)
    (hh : h < L.threads) (hc : h / L.block = g / L.block)
    (hG : MCls p L g N t (some x)) (hH : MCls p L h N' t' o) (hle : N' ≤ N) :
    t' < t ∨ (N' = N ∧ o = some x ∧ t' = t) := by
  have hpr := Progress.scanBase_le_primeBase p
  have hend : primeBase p + 1024 ≤ endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold endBase Progress.tailBase; omega
  have hpipe : ∀ q r, primeBase p + 1024 ≤ Progress.Mm.pipeT p q r := fun q r =>
    Progress.primeBase_le_clk p _ _
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  generalize ho : some x = ox at hG
  cases hG with
  | early | scanOff | end1 | scan2Off | end2 => cases ho
  | start j =>
    cases ho
    have hj := j.isLt
    have hsh : ∀ a b : Fin 3, a < b → shPc a.val < shPc b.val := by decide
    cases hH with
    | start j' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · exact .inl (hsh j' j h1)
      · have := Fin.ext h1
        subst this
        exact .inr ⟨rfl, rfl, rfl⟩
    | early | bcast | scan => omega
    | scanOff n t hn => omega
    | end1 ns nv t hx => have := Epilogue.exit_ge hx; omega
    | pipe R0 bal => have := chN_ge R0 bal; omega
    | scan2Off R0 bal R n t hP hR hn => have := chN_ge R0 bal; omega
    | scan2 R0 bal R n0 v0 q s hP hR hps => have := pass2_ge hP hps; have := chN_ge R0 bal; omega
    | end2 R0 bal R ns nv t hP hR hx => have := Epilogue.exit_ge hx; omega
  | bcast =>
    cases ho
    cases hH with
    | start j' =>
      left
      have : ∀ a : Fin 3, shPc a.val < 200 := by decide
      have := this j'
      omega
    | early t ht => exact .inl ht
    | bcast => exact .inr ⟨rfl, rfl, rfl⟩
    | scanOff n t hn => omega
    | scan => omega
    | end1 ns nv t hx => have := Epilogue.exit_ge hx; omega
    | pipe R0 bal => have := chN_ge R0 bal; omega
    | scan2Off R0 bal R n t hP hR hn => have := chN_ge R0 bal; omega
    | scan2 R0 bal R n0 v0 q s hP hR hps => have := pass2_ge hP hps; have := chN_ge R0 bal; omega
    | end2 R0 bal R ns nv t hP hR hx => have := Epilogue.exit_ge hx; omega
  | scan q s hs hsc hq =>
    cases ho
    cases hH with
    | start j' =>
      left
      have : ∀ a : Fin 3, shPc a.val < 200 := by decide
      have := this j'
      omega
    | early t ht => left; omega
    | bcast => left; omega
    | scanOff n t hn ht => left; omega
    | scan q' s' hs' hsc' hq' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        have := scan_tag hs' hsc' hs hsc (hq'.unique hq)
        subst this
        exact .inr ⟨rfl, rfl, rfl⟩
    | end1 ns nv t hx =>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx
      omega
    | pipe R0 bal R q' r o hP =>
      have := pos_chN hq (picked_cta' hc hP)
      omega
    | scan2Off R0 bal R n t hP hR hn =>
      have := pos_chN hq (picked_cta' hc hP)
      omega
    | scan2 R0 bal R n0 v0 q' s' hP hR hps =>
      have := pos_chN hq (picked_cta' hc hP)
      have := pass2_ge hP hps
      omega
    | end2 R0 bal R ns nv t hP hR hx =>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx
      omega
  | pipe R0 bal R q r o hP hR hpl ho' =>
    obtain ⟨s, hsq, hsp, hso, hcq⟩ := ho'
    have hcq := hcq x ho.symm
    have hx' : x = .site s := by
      have := ho.trans (hso hcq); exact Option.some.inj this
    subst hx'
    have hT := hpipe q r
    cases hH with
    | start j' =>
      left
      have : ∀ a : Fin 3, shPc a.val < 200 := by decide
      have := this j'
      omega
    | early t ht => left; omega
    | bcast => left; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left
      have := pos_chN hq' (picked_cta' hc.symm hP)
      have := chN_le hp hP
      omega
    | end1 ns nv t hx => exact (Epilogue.exit_not_picked hx (picked_cta' hc.symm hP)).elim
    | pipe R0' bal' R' q' r' o' hP' hR' hpl' ho'' =>
      obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      obtain rfl := (hR'.cta hc).unique hR
      by_cases hne : q' = q ∧ r' = r
      · obtain ⟨rfl, rfl⟩ := hne
        obtain ⟨s', hsq', hsp', hso', -⟩ := ho''
        have := ord_tag hsp hsp' (by rw [hsq]; exact hcq) (hsq.trans hsq'.symm)
        subst this
        exact .inr ⟨rfl, (hso' hcq).trans ho, rfl⟩
      · exact .inl (place_lt hcq hpl hpl' (by omega) hne)
    | scan2Off R0' bal' R' n t hP' hR' hn =>
      obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      obtain rfl := (hR'.cta hc).unique hR
      have := pipe_lt_total hcq hpl
      omega
    | scan2 R0' bal' R' n0 v0 q' s' hP' hR' hps =>
      obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      obtain rfl := (hR'.cta hc).unique hR
      have := pipe_lt_total hcq hpl
      have := pass2_ge hP' hps
      omega
    | end2 R0' bal' R' ns nv t hP' hR' hx =>
      obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      obtain rfl := (hR'.cta hc).unique hR
      have := pipe_lt_total hcq hpl
      have := exit2_ge hP' hx
      omega
  | scan2 R0 bal R n0 v0 q s hP hR hps hs hsc hq =>
    cases ho
    have hge := pass2_ge hP hps
    have hc2 := chN_ge R0 bal
    cases hH with
    | start j' =>
      left
      have : ∀ a : Fin 3, shPc a.val < 200 := by decide
      have := this j'
      omega
    | early t ht => left; omega
    | bcast => left; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left
      have := pos_chN hq' (picked_cta' hc.symm hP)
      have := chN_le hp hP
      omega
    | end1 ns nv t hx => exact (Epilogue.exit_not_picked hx (picked_cta' hc.symm hP)).elim
    | pipe R0' bal' R' q' r' o' hP' hR' hpl' ho'' =>
      left
      have := early_lt hp hh hpl' hR'
      omega
    | scan2Off R0' bal' R' n t hP' hR' hn ht ht' =>
      obtain rfl := (hR'.cta hc).unique hR
      left; omega
    | scan2 R0' bal' R' n0' v0' q' s' hP' hR' hps' hs' hsc' hq' =>
      obtain rfl := (hR'.cta hc).unique hR
      obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      have hge' := pass2_ge hP' hps'
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        have := scan_tag hs' hsc' hs hsc (hq'.unique hq)
        subst this
        refine .inr ⟨by omega, rfl, by omega⟩
    | end2 R0' bal' R' ns nv t hP' hR' hx =>
      obtain rfl := (hR'.cta hc).unique hR
      have := Epilogue.pos_lt_exit hps hq hc.symm hx
      omega

/-- Where a lane of the MMA warp that returns stands. -/
def ExitN (p : Params) (L : Launch) (g N : Nat) : Prop :=
  (∃ ns nv, Epilogue.Fits.ExitAt p L g false ns nv ∧ N = 1 + ns + nv) ∨
    ∃ R0 bal R ns nv, Epilogue.Picked p L g R0 bal ∧ MmaRounds p L g R ∧
      Epilogue.Fits.ExitAt p L g true ns nv ∧ N = 1 + pipeCnt 100 R + (ns + nv)

/-- **A lane returns after more collectives than a lane at one has made.** -/
theorem MCls.lt_exit {N N' t : Nat} {x : CollTag} (hc : h / L.block = g / L.block)
    (hG : MCls p L g N t (some x)) (hH : ExitN p L h N') : N < N' := by
  have hge : 11 ≤ N' := by
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨R0, bal, R, ns, nv, -, -, hx, rfl⟩ <;>
      have := Epilogue.exit_ge hx <;> omega
  generalize ho : some x = ox at hG
  cases hG with
  | early | scanOff | end1 | scan2Off | end2 => cases ho
  | start j => have := j.isLt; omega
  | bcast => omega
  | scan q s hs hsc hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨R0, bal, R, ns, nv, -, -, hx, rfl⟩ <;>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx <;> omega
  | pipe R0 bal R q r o hP hR hpl ho' =>
    obtain ⟨s, hsq, hsp, hso, hcq⟩ := ho'
    have hcq := hcq x ho.symm
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨R0', bal', R', ns, nv, hP', hR', hx, rfl⟩
    · exact (Epilogue.exit_not_picked hx (picked_cta' hc.symm hP)).elim
    · obtain ⟨rfl, rfl⟩ := (picked_cta' hc hP').unique hP
      obtain rfl := (hR'.cta hc).unique hR
      have := pipe_lt_total hcq hpl
      have := exit2_ge hP' hx
      omega
  | scan2 R0 bal R n0 v0 q s hP hR hps hs hsc hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨R0', bal', R', ns, nv, hP', hR', hx, rfl⟩
    · exact (Epilogue.exit_not_picked hx (picked_cta' hc.symm hP)).elim
    · obtain rfl := (hR'.cta hc).unique hR
      have := Epilogue.pos_lt_exit hps hq hc.symm hx
      omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
