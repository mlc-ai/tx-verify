-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollPos
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' collectives, by their number

`LCls` says where a state of a loader warp stands: with `N` collectives made, at time `t`, at a
collective (`some` tag) or not. A lane with at most as many as a lane at a collective, and not at
that collective, is earlier (`LCls.order`), and a lane that returns has made more
(`LCls.lt_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk scanBase endBase primeBase doneBase shPc)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Pos selN Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat}

/-- What a state at a collective is at. -/
inductive CollTag
  | start (j : Fin 3)
  | site (s : Site)

/-- The collective a site is at. -/
def tagS (s : Site) : Option CollTag := if s.wcoll then some (.site s) else none

/-- The elections of the drain before a site, on warp 14 (`b = false`) or 15. -/
def drN (b : Bool) (s : Site) : Nat := if b then 0 else drainEl s

/-- The time of a drain's site. -/
def drT : Site → Nat
  | .dw j => 2 * j.val
  | .dq => 6
  | .de => 8
  | .da => 10
  | _ => 12

/-- **Where a state of a loader warp stands**: `N` collectives made, time `t`, the collective it is
at. -/
inductive LCls (p : Params) (L : Launch) (g : Nat) (b : Bool) :
    Nat → Nat → Option CollTag → Prop
  | start (j : Fin 3) : LCls p L g b j.val (shPc j.val) (some (.start j))
  | scanOff (n t : Nat) (hn : 3 ≤ n) (ht : t < scanBase + 2 * n) (ht' : t < primeBase p) :
      LCls p L g b n t none
  | scan (q : Nat) (s : Site) (hs : s.epi = s.toE) (hsc : s.scan = true)
      (hq : Pos p (g / L.block) false q s.epi) (hd : scanBase + 2 * (3 + q) < primeBase p) :
      LCls p L g b (3 + q) (scanBase + 2 * (3 + q)) (some (.site s))
  | req (ch W : Nat) (l : Bool) (P t : Nat) (hT : Tile p L g ch W l P)
      (ht : t < primeBase p + 8) : LCls p L g b ch t none
  | blk (ch W : Nat) (l : Bool) (P x : Nat) (o : Blk) (s : Site) (hT : Tile p L g ch W l P)
      (hb : bc s = some o) (hx : Plc W l P x o) (ht : b = true → isT s = false) :
      LCls p L g b (ch + plcN b W l x s) (blkT p x s) (tagS s)
  | scan2Off (ch W : Nat) (l : Bool) (P n t : Nat) (hT : Tile p L g ch W l P) (hn : ch ≤ n)
      (ht : endBase p ≤ t) (ht' : t + 2 < endBase p + 2 * n) (hd : t < doneBase p) :
      LCls p L g b (blkTot b W l P + n) t none
  | scan2 (ch W : Nat) (l : Bool) (P n0 v0 q : Nat) (s : Site) (hT : Tile p L g ch W l P)
      (hps : Epilogue.PassStart p L g true n0 v0) (hs : s.epi = s.toE) (hsc : s.scan = true)
      (hq : Pos p (g / L.block) true q s.epi) (hv : v0 = 1)
      (hd : endBase p + 2 * (n0 + q) < doneBase p) :
      LCls p L g b (blkTot b W l P + (n0 + v0 + q)) (endBase p + 2 * (n0 + q))
        (some (.site s))
  | end1 (ns nv : Nat) (s : Site) (hs : lc s = .drain) (hb : b = true → s ≠ .de)
      (hx : Epilogue.Fits.ExitAt p L g false ns nv) :
      LCls p L g b (ns + nv + drN b s) (doneBase p + drT s) (tagS s)
  | end2 (ch W : Nat) (l : Bool) (P ns nv : Nat) (s : Site) (hT : Tile p L g ch W l P)
      (hs : lc s = .drain) (hb : b = true → s ≠ .de)
      (hx : Epilogue.Fits.ExitAt p L g true ns nv) :
      LCls p L g b (blkTot b W l P + (ns + nv) + drN b s) (doneBase p + drT s) (tagS s)

/-- The returns of a CTA's passes are after one number of collectives. -/
theorem exit_same {l : Bool} {ns nv ns' nv' : Nat} (hc : h / L.block = g / L.block)
    (hx : Epilogue.Fits.ExitAt p L g l ns nv) (hx' : Epilogue.Fits.ExitAt p L h l ns' nv') :
    ns' + nv' = ns + nv := by
  obtain ⟨n0, v0, hP, R, hE, hx⟩ := hx
  obtain ⟨n0', v0', hP', R', hE', hx'⟩ := hx'
  obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same hc.symm hP hP'
  rw [hc] at hE' hx'
  obtain rfl := hE'.unique hE
  rcases hx with ⟨h1, h2, h3⟩ | ⟨a, hB, h1, h2, h3, -⟩ <;>
    rcases hx' with ⟨h1', h2', h3'⟩ | ⟨a', hB', h1', h2', h3', -⟩
  · omega
  · rw [h1] at h1'; cases h1'
  · rw [h1] at h1'; cases h1'
  · obtain rfl := hB'.unique hB
    omega

private theorem Tile.not_exit {ch W P ns nv : Nat} {l : Bool} (hc : h / L.block = g / L.block)
    (hT : Tile p L g ch W l P) (hx : Epilogue.Fits.ExitAt p L h false ns nv) : False := by
  obtain ⟨R, bal, hP, -⟩ := hT
  exact Epilogue.exit_not_picked hx (Epilogue.Picked.cta hc.symm hP)

/-- A collective of the first pass is before the choice's end. -/
private theorem Tile.pos_lt {ch W P q : Nat} {l : Bool} {s : Epilogue.Site}
    (hc : h / L.block = g / L.block) (hT : Tile p L g ch W l P)
    (hq : Pos p (h / L.block) false q s) : 3 + q < ch := by
  obtain ⟨R, bal, hP, rfl, -⟩ := hT
  rw [hc] at hq
  have h1 := Epilogue.pos_late (L := L) (g := g) (n0 := 3) (v0 := 0) (by
    simp [Epilogue.PassStart]) hq
  by_contra hcon
  have : Progress.Late p (g / L.block) (3 + 0 + q) := ⟨R, bal, hP, by unfold chN at hcon; omega⟩
  exact absurd (h1.mp this) (by simp)

private theorem Tile.pass2 {ch W P n0 v0 : Nat} {l : Bool} (hT : Tile p L g ch W l P)
    (hps : Epilogue.PassStart p L g true n0 v0) : n0 + v0 = ch := by
  obtain ⟨R, bal, hP, rfl, -⟩ := hT
  simp only [Epilogue.PassStart, ite_true] at hps
  obtain ⟨R', bal', hP', rfl, rfl⟩ := hps
  obtain ⟨rfl, rfl⟩ := hP'.unique hP
  unfold chN; omega

private theorem Tile.exit2 {ch W P ns nv : Nat} {l : Bool} (hT : Tile p L g ch W l P)
    (hx : Epilogue.Fits.ExitAt p L g true ns nv) : ch ≤ ns + nv := by
  obtain ⟨n1, v1, hps, R1, -, hx⟩ := hx
  have := hT.pass2 hps
  rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega

private theorem scan_tag {s s' : Site} (hs : s.epi = s.toE) (hsc : s.scan = true)
    (hs' : s'.epi = s'.toE) (hsc' : s'.scan = true) (h : s.epi = s'.epi) : s = s' := by
  rw [hs, hs'] at h
  cases s <;> simp only [Site.scan, Bool.false_eq_true] at hsc <;> cases s' <;>
    simp only [Site.scan, Bool.false_eq_true] at hsc' <;>
    simp only [Site.toE, reduceCtorEq] at h <;> simp_all

private theorem drain_tag {s : Site} {x : CollTag} (hs : lc s = .drain)
    (hx : some x = tagS s) : s = .de ∧ x = .site .de := by
  cases s <;> simp only [lc, reduceCtorEq] at hs
  case de => exact ⟨rfl, by simpa [tagS, Site.wcoll] using hx⟩
  case dw | dq | da | exit => simp [tagS, Site.wcoll] at hx
  all_goals (split_ifs at hs)

/-- The order at the drain's election. -/
private theorem drain_order {b : Bool} {s : Site} (hs : lc s = .drain) (hb : b = false)
    (hle : drN b s ≤ drN b .de) : drT s < drT .de ∨ s = .de := by
  subst hb
  cases s <;> simp only [lc, reduceCtorEq] at hs
  case de => exact .inr rfl
  case dq => left; decide
  case dw j => left; have := j.isLt; simp only [drT]; omega
  case da | exit => simp [drN, drainEl] at hle
  all_goals (split_ifs at hs)

private theorem bl_cases {s : Site} (hw : tagS s ≠ none) : s.wcoll = true := by
  unfold tagS at hw
  by_contra h
  simp [h] at hw

private theorem shPc_lt (j : Fin 3) : shPc j.val < 200 := by revert j; decide

set_option maxHeartbeats 4000000 in
/-- **The number of collectives gives the collective**, and the lag of a lane not at it. -/
theorem LCls.order {N N' t t' : Nat} {b : Bool} {x : CollTag} {o : Option CollTag}
    (hp : Pre p L m) (hh : h < L.threads) (hc : h / L.block = g / L.block)
    (hG : LCls p L g b N t (some x)) (hH : LCls p L h b N' t' o) (hle : N' ≤ N) :
    t' < t ∨ (N' = N ∧ o = some x ∧ t' = t) := by
  have hpr := Progress.scanBase_le_primeBase p
  have hend : primeBase p + 1024 ≤ endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold endBase Progress.tailBase; omega
  have hdone : endBase p + 4 * Progress.cmax p + 8 = doneBase p := rfl
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  generalize ho : some x = ox at hG
  cases hG with
  | scanOff | req | scan2Off => cases ho
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
    | scanOff | scan => omega
    | req ch W l P t hT => have := hT.ch_ge; omega
    | blk ch W l P x o s hT => have := hT.ch_ge; omega
    | scan2Off ch W l P n t hT hn => have := hT.ch_ge; omega
    | scan2 ch W l P n0 v0 q s hT hps => have := hT.pass2 hps; have := hT.ch_ge; omega
    | end1 ns nv s hs hb hx => have := Epilogue.exit_ge hx; omega
    | end2 ch W l P ns nv s hT hs hb hx => have := Epilogue.exit_ge hx; omega
  | scan q s hs hsc hq =>
    cases ho
    cases hH with
    | start j' => left; have := shPc_lt j'; omega
    | scanOff n t hn ht => left; omega
    | scan q' s' hs' hsc' hq' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        have := scan_tag hs' hsc' hs hsc (hq'.unique hq)
        subst this
        exact .inr ⟨rfl, rfl, rfl⟩
    | req ch W l P t hT => have := hT.pos_lt hc.symm hq; omega
    | blk ch W l P x o s hT => have := hT.pos_lt hc.symm hq; omega
    | scan2Off ch W l P n t hT hn => have := hT.pos_lt hc.symm hq; omega
    | scan2 ch W l P n0 v0 q' s' hT hps =>
      have := hT.pos_lt hc.symm hq; have := hT.pass2 hps; omega
    | end1 ns nv s hs hb hx | end2 ch W l P ns nv s hT hs hb hx =>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx
      omega
  | blk ch W l P x o s hT hb hx ht =>
    have hw : s.wcoll = true := bl_cases (by rw [← ho]; simp)
    have hT8 := blkT_ge p hb hx
    cases hH with
    | start j' => left; have := shPc_lt j'; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left; have := hT.pos_lt hc hq'; have := hT.ch_le hp; omega
    | req ch' W' l' P' t hT' ht' => left; omega
    | blk ch' W' l' P' x' o' s' hT' hb' hx' ht' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      rcases plc_order (p := p) hb hb' hw (fun h => ⟨ht h, ht' h⟩) hx hx' (by omega) with
        h1 | ⟨rfl, rfl⟩
      · exact .inl h1
      · exact .inr ⟨rfl, rfl, rfl⟩
    | scan2Off ch' W' l' P' n t hT' hn =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := plcN_tot hb hw ht hx hT.warm_le
      omega
    | scan2 ch' W' l' P' n0 v0 q s hT' hps =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := plcN_tot hb hw ht hx hT.warm_le
      have := hT'.pass2 hps
      omega
    | end1 ns nv s hs hb hx => exact (hT.not_exit hc hx).elim
    | end2 ch' W' l' P' ns nv s hT' hs hb' hx' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := plcN_tot hb hw ht hx hT.warm_le
      have := hT'.exit2 hx'
      omega
  | scan2 ch W l P n0 v0 q s hT hps hs hsc hq hv hd =>
    cases ho
    have hge := hT.pass2 hps
    cases hH with
    | start j' => left; have := shPc_lt j'; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left; have := hT.pos_lt hc hq'; have := hT.ch_le hp; omega
    | req ch' W' l' P' t hT' ht' => left; omega
    | blk ch' W' l' P' x' o' s' hT' hb' hx' ht' =>
      left
      have := blkT_lt (p := p) (s := s') hx' hT'.warm_le (hT'.pkts_le hp hh)
      omega
    | scan2Off ch' W' l' P' n t hT' hn ht ht' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      left; omega
    | scan2 ch' W' l' P' n0' v0' q' s' hT' hps' hs' hsc' hq' hv' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have hge' := hT'.pass2 hps'
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        have := scan_tag hs' hsc' hs hsc (hq'.unique hq)
        subst this
        refine .inr ⟨by omega, rfl, by omega⟩
    | end1 ns nv s hs hb hx => exact (hT.not_exit hc hx).elim
    | end2 ch' W' l' P' ns nv s hT' hs hb hx =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := Epilogue.pos_lt_exit hps hq hc.symm hx
      omega
  | end1 ns nv s hs hb hx =>
    obtain ⟨rfl, rfl⟩ := drain_tag hs ho
    have hbf : b = false := by
      cases b with
      | true => exact absurd rfl (hb rfl)
      | false => rfl
    cases hH with
    | start j' => left; have := shPc_lt j'; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left; omega
    | req ch' W' l' P' t hT' => exact (hT'.not_exit hc.symm hx).elim
    | blk ch' W' l' P' x' o' s' hT' => exact (hT'.not_exit hc.symm hx).elim
    | scan2Off ch' W' l' P' n t hT' => exact (hT'.not_exit hc.symm hx).elim
    | scan2 ch' W' l' P' n0' v0' q' s' hT' => exact (hT'.not_exit hc.symm hx).elim
    | end1 ns' nv' s' hs' hb' hx' =>
      have he := exit_same hc hx hx'
      rcases drain_order hs' hbf (by omega) with h1 | rfl
      · left; omega
      · exact .inr ⟨by omega, ho.symm, rfl⟩
    | end2 ch' W' l' P' ns nv s hT' => exact (hT'.not_exit hc.symm hx).elim
  | end2 ch W l P ns nv s hT hs hb hx =>
    obtain ⟨rfl, rfl⟩ := drain_tag hs ho
    have hbf : b = false := by
      cases b with
      | true => exact absurd rfl (hb rfl)
      | false => rfl
    cases hH with
    | start j' => left; have := shPc_lt j'; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hs' hsc' hq' =>
      left; have := hT.pos_lt hc hq'; have := hT.ch_le hp; omega
    | req ch' W' l' P' t hT' => left; omega
    | blk ch' W' l' P' x' o' s' hT' hb' hx' ht' =>
      left
      have := blkT_lt (p := p) (s := s') hx' hT'.warm_le (hT'.pkts_le hp hh)
      omega
    | scan2Off => left; omega
    | scan2 => left; omega
    | end1 ns' nv' s' hs' hb' hx' => exact (hT.not_exit hc hx').elim
    | end2 ch' W' l' P' ns' nv' s' hT' hs' hb' hx' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have he := exit_same hc hx hx'
      rcases drain_order hs' hbf (by omega) with h1 | rfl
      · left; omega
      · exact .inr ⟨by omega, ho.symm, rfl⟩

/-- Where a lane of a loader warp that returns stands. -/
def ExitN (p : Params) (L : Launch) (g : Nat) (b : Bool) (N : Nat) : Prop :=
  (∃ ns nv, Epilogue.Fits.ExitAt p L g false ns nv ∧ N = ns + nv + drN b .exit) ∨
    ∃ ch W l P ns nv, Tile p L g ch W l P ∧ Epilogue.Fits.ExitAt p L g true ns nv ∧
      N = blkTot b W l P + (ns + nv) + drN b .exit

/-- A state at the return. -/
theorem LCls.exit {N : Nat} {b : Bool} (hp : Pre p L m) (hg : g < L.threads)
    (hG : LCls p L g b N (doneBase p + 12) none) : ExitN p L g b N := by
  have hpr := Progress.scanBase_le_primeBase p
  have hend : primeBase p + 1024 ≤ endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold endBase Progress.tailBase; omega
  have hdone : endBase p + 4 * Progress.cmax p + 8 = doneBase p := rfl
  have key : ∀ {s : Site} {t : Nat}, lc s = .drain → doneBase p + drT s = t →
      t = doneBase p + 12 → s = .exit := fun {s t} hs ht h => by
    have h12 : drT s = 12 := by omega
    clear ht h
    cases s <;> simp only [lc, reduceCtorEq] at hs
    case exit => rfl
    case dq | de | da => simp [drT] at h12
    case dw j => have := j.isLt; simp only [drT] at h12; omega
    all_goals (split_ifs at hs)
  generalize ht : doneBase p + 12 = t at hG
  generalize ho : (none : Option CollTag) = o at hG
  cases hG with
  | start | scan | scan2 => cases ho
  | scanOff | req | scan2Off => omega
  | blk ch W l P x o s hT hb hx =>
    have := blkT_lt (p := p) (s := s) hx hT.warm_le (hT.pkts_le hp hg)
    omega
  | end1 ns nv s hs hb hx =>
    obtain rfl := key hs rfl ht.symm
    exact .inl ⟨ns, nv, hx, rfl⟩
  | end2 ch W l P ns nv s hT hs hb hx =>
    obtain rfl := key hs rfl ht.symm
    exact .inr ⟨ch, W, l, P, ns, nv, hT, hx, rfl⟩

/-- **A lane returns after more collectives than a lane at one has made.** -/
theorem LCls.lt_exit {N N' t : Nat} {b : Bool} {x : CollTag} (hc : h / L.block = g / L.block)
    (hG : LCls p L g b N t (some x)) (hH : ExitN p L h b N') : N < N' := by
  have hge : 10 ≤ N' := by
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨ch, W, l, P, ns, nv, -, hx, rfl⟩ <;>
      have := Epilogue.exit_ge hx <;> omega
  have hde : ∀ {s : Site}, some x = tagS s → lc s = .drain → (b = true → s ≠ .de) →
      drN b s < drN b .exit := fun hx hs hb => by
    obtain ⟨rfl, -⟩ := drain_tag hs hx
    cases b with
    | true => exact absurd rfl (hb rfl)
    | false => decide
  generalize ho : some x = ox at hG
  cases hG with
  | scanOff | req | scan2Off => cases ho
  | start j => have := j.isLt; omega
  | scan q s hs hsc hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨ch, W, l, P, ns, nv, -, hx, rfl⟩ <;>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx <;> omega
  | blk ch W l P x o s hT hb hx ht =>
    have hw : s.wcoll = true := bl_cases (by rw [← ho]; simp)
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨ch', W', l', P', ns, nv, hT', hx', rfl⟩
    · exact (hT.not_exit hc hx).elim
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := plcN_tot hb hw ht hx hT.warm_le
      have := hT'.exit2 hx'
      omega
  | scan2 ch W l P n0 v0 q s hT hps hs hsc hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨ch', W', l', P', ns, nv, hT', hx', rfl⟩
    · exact (hT.not_exit hc hx).elim
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have := Epilogue.pos_lt_exit hps hq hc.symm hx'
      omega
  | end1 ns nv s hs hb hx =>
    have := hde ho hs hb
    rcases hH with ⟨ns', nv', hx', rfl⟩ | ⟨ch', W', l', P', ns', nv', hT', hx', rfl⟩
    · have he := exit_same hc hx hx'
      omega
    · exact (hT'.not_exit hc.symm hx).elim
  | end2 ch W l P ns nv s hT hs hb hx =>
    have := hde ho hs hb
    rcases hH with ⟨ns', nv', hx', rfl⟩ | ⟨ch', W', l', P', ns', nv', hT', hx', rfl⟩
    · exact (hT.not_exit hc hx').elim
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hT.same hc hT'
      have he := exit_same hc hx hx'
      omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
