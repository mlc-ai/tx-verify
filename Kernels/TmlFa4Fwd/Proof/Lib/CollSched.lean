-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
public import Kernels.TmlFa4Fwd.Proof.Progress.Order
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of a warp that runs the scheduler twice around its rounds

`SCls` says where a state of such a warp stands: with `N` collectives made, at time `t`, at a
collective (`some` tag) or not. The rounds between the passes are a parameter (`Mid`). A lane with
at most as many collectives as a lane at one, and not at it, is earlier (`SCls.order`), and a lane
that returns has made more (`SCls.lt_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase doneBase shPc)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Pos selN Picked)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat} {β τ : Type}

/-- What a state at a collective is at. -/
inductive STag (β : Type)
  | start (j : Fin 3)
  | init (j : Fin 16)
  | scan (s : Epilogue.Site)
  | mid (b : β)

/-- **The rounds between the passes**: what a lane's tile fixes (`tile`), the collectives of the
first pass and of the rounds, and where a state of the rounds stands, its collectives counted
with the first pass's. -/
structure Mid (p : Params) (L : Launch) (β τ : Type) where
  tile : Nat → τ → Prop
  ch : τ → Nat
  tot : τ → Nat
  M : τ → Nat → Nat → Option β → Prop
  same : ∀ {g h a b}, h / L.block = g / L.block → tile g a → tile h b → b = a
  picked : ∀ {g a}, tile g a → ∃ R bal, Picked p L g R bal ∧ ch a = 4 + 7 * (R + 1) + selN bal
  ge : ∀ {a N t o}, M a N t o → ch a ≤ N
  tge : ∀ {a N t x}, M a N t (some x) → primeBase p + 8 ≤ t
  lt_tot : ∀ {a N t x}, M a N t (some x) → N < ch a + tot a
  lt_end : ∀ {g a N t o}, g < L.threads → tile g a → M a N t o → t < endBase p
  order : ∀ {a N N' t t' x o}, M a N t (some x) → M a N' t' o → N' ≤ N →
    t' < t ∨ (N' = N ∧ o = some x ∧ t' = t)

namespace Mid

variable {R : Mid p L β τ}

theorem ch_ge (R : Mid p L β τ) {a : τ} (h : R.tile g a) : 12 ≤ R.ch a := by
  obtain ⟨R0, bal, -, e⟩ := R.picked h
  have := (Epilogue.selN_pos bal).1
  omega

theorem ch_le (R : Mid p L β τ) (hp : Pre p L m) {a : τ} (h : R.tile g a) :
    R.ch a ≤ Progress.cmax p := by
  obtain ⟨R0, bal, hP, e⟩ := R.picked h
  have := Epilogue.chosen_coll_le hp (d := Epilogue.chosenD p (g / L.block) R0 bal)
    (ns := 3 + 7 * (R0 + 1) + selN bal) (nv := 1) ⟨hP, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold Progress.cmax
  omega

theorem not_exit (R : Mid p L β τ) {a : τ} {ns nv : Nat} (hc : h / L.block = g / L.block)
    (hT : R.tile g a) (hx : Epilogue.Fits.ExitAt p L h false ns nv) : False := by
  obtain ⟨R0, bal, hP, -⟩ := R.picked hT
  exact Epilogue.exit_not_picked hx (Epilogue.Picked.cta hc.symm hP)

/-- A collective of the first pass is before the choice's end. -/
theorem pos_lt (R : Mid p L β τ) {a : τ} {q : Nat} {s : Epilogue.Site}
    (hc : h / L.block = g / L.block) (hT : R.tile g a) (hq : Pos p (h / L.block) false q s) :
    3 + q < R.ch a := by
  obtain ⟨R0, bal, hP, e⟩ := R.picked hT
  rw [hc] at hq
  have h1 := Epilogue.pos_late (L := L) (g := g) (n0 := 3) (v0 := 0) (by
    simp [Epilogue.PassStart]) hq
  by_contra hcon
  have : Progress.Late p (g / L.block) (3 + 0 + q) := ⟨R0, bal, hP, by omega⟩
  exact absurd (h1.mp this) (by simp)

theorem pass2 (R : Mid p L β τ) {a : τ} {n0 v0 : Nat} (hT : R.tile g a)
    (hps : Epilogue.PassStart p L g true n0 v0) : n0 + v0 = R.ch a := by
  obtain ⟨R0, bal, hP, e⟩ := R.picked hT
  simp only [Epilogue.PassStart, ite_true] at hps
  obtain ⟨R', bal', hP', rfl, rfl⟩ := hps
  obtain ⟨rfl, rfl⟩ := hP'.unique hP
  omega

theorem exit2 (R : Mid p L β τ) {a : τ} {ns nv : Nat} (hT : R.tile g a)
    (hx : Epilogue.Fits.ExitAt p L g true ns nv) : R.ch a ≤ ns + nv := by
  obtain ⟨n1, v1, hps, R1, -, hx⟩ := hx
  have := R.pass2 hT hps
  rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega

end Mid

/-- **Where a state stands**: `N` collectives made (`E0` of them the startup's elections), time
`t`, the collective it is at. -/
inductive SCls (R : Mid p L β τ) (g E0 : Nat) : Nat → Nat → Option (STag β) → Prop
  | start (j : Fin 3) : SCls R g E0 j.val (shPc j.val) (some (.start j))
  | init (j : Fin 16) (hE : E0 = 16) :
      SCls R g E0 (3 + j.val) (Startup.Site.elect j).pc (some (.init j))
  | initOff (j t : Nat) (hE : E0 = 16)
      (ht : ∀ i : Fin 16, j ≤ i.val → t < (Startup.Site.elect i).pc) (ht' : t ≤ 173) :
      SCls R g E0 (3 + j) t none
  | scanOff (n t : Nat) (hn : 3 ≤ n) (ht : t < scanBase + 2 * n) (ht' : t < primeBase p) :
      SCls R g E0 (E0 + n) t none
  | scan (q : Nat) (s : Epilogue.Site) (hq : Pos p (g / L.block) false q s)
      (hd : scanBase + 2 * (3 + q) < primeBase p) :
      SCls R g E0 (E0 + (3 + q)) (scanBase + 2 * (3 + q)) (some (.scan s))
  | mid (a : τ) (N t : Nat) (o : Option β) (hT : R.tile g a) (hM : R.M a N t o) :
      SCls R g E0 (E0 + N) t (o.map .mid)
  | scan2Off (a : τ) (n t : Nat) (hT : R.tile g a) (hn : R.ch a ≤ n) (ht : endBase p ≤ t)
      (ht' : t + 2 < endBase p + 2 * n) :
      SCls R g E0 (E0 + R.tot a + n) t none
  | scan2 (a : τ) (n0 v0 q : Nat) (s : Epilogue.Site) (hT : R.tile g a)
      (hps : Epilogue.PassStart p L g true n0 v0) (hq : Pos p (g / L.block) true q s)
      (hv : v0 = 1) :
      SCls R g E0 (E0 + R.tot a + (n0 + v0 + q)) (endBase p + 2 * (n0 + q)) (some (.scan s))
  | end1 (ns nv t : Nat) (hx : Epilogue.Fits.ExitAt p L g false ns nv) :
      SCls R g E0 (E0 + (ns + nv)) t none
  | end2 (a : τ) (ns nv t : Nat) (hT : R.tile g a)
      (hx : Epilogue.Fits.ExitAt p L g true ns nv) :
      SCls R g E0 (E0 + R.tot a + (ns + nv)) t none

private theorem start_lt : (∀ j : Fin 3, shPc j.val < 40) ∧
    (∀ i : Fin 16, 40 ≤ (Startup.Site.elect i).pc ∧ (Startup.Site.elect i).pc ≤ 173) ∧
    (∀ a b : Fin 3, a < b → shPc a.val < shPc b.val) ∧
    ∀ a b : Fin 16, a < b → (Startup.Site.elect a).pc < (Startup.Site.elect b).pc := by decide

set_option maxHeartbeats 4000000 in
/-- **The number of collectives gives the collective**, and the lag of a lane not at it. -/
theorem SCls.order {R : Mid p L β τ} {E0 N N' t t' : Nat} {x : STag β} {o : Option (STag β)}
    (hp : Pre p L m) (hh : h < L.threads) (hc : h / L.block = g / L.block)
    (hG : SCls R g E0 N t (some x)) (hH : SCls R h E0 N' t' o) (hle : N' ≤ N) :
    t' < t ∨ (N' = N ∧ o = some x ∧ t' = t) := by
  have hpr := Progress.scanBase_le_primeBase p
  have hend : primeBase p + 1024 ≤ endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold endBase Progress.tailBase; omega
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  obtain ⟨sh1, el1, sh2, el2⟩ := start_lt
  generalize ho : some x = ox at hG
  cases hG with
  | initOff | scanOff | scan2Off | end1 | end2 => cases ho
  | start j =>
    cases ho
    have hj := j.isLt
    cases hH with
    | start j' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · exact .inl (sh2 j' j h1)
      · have := Fin.ext h1
        subst this
        exact .inr ⟨rfl, rfl, rfl⟩
    | init | initOff | scanOff | scan => omega
    | mid a N t o hT hM => have := R.ch_ge hT; have := R.ge hM; omega
    | scan2Off a n t hT hn => have := R.ch_ge hT; omega
    | scan2 a n0 v0 q s hT hps => have := R.pass2 hT hps; have := R.ch_ge hT; omega
    | end1 ns nv t hx | end2 a ns nv t hT hx => have := Epilogue.exit_ge hx; omega
  | init j hE =>
    cases ho
    have hj := j.isLt
    cases hH with
    | start j' => left; have := sh1 j'; have := (el1 j).1; omega
    | init j' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · exact .inl (el2 j' j (by simp only [Fin.lt_def]; omega))
      · have : j' = j := Fin.ext (by omega)
        subst this
        exact .inr ⟨rfl, rfl, rfl⟩
    | initOff j' t hE ht => exact .inl (ht j (by omega))
    | scanOff | scan => omega
    | mid a N t o hT hM => have := R.ch_ge hT; have := R.ge hM; omega
    | scan2Off a n t hT hn => have := R.ch_ge hT; omega
    | scan2 a n0 v0 q s hT hps => have := R.pass2 hT hps; have := R.ch_ge hT; omega
    | end1 ns nv t hx | end2 a ns nv t hT hx => have := Epilogue.exit_ge hx; omega
  | scan q s hq hd =>
    cases ho
    cases hH with
    | start j' => left; have := sh1 j'; omega
    | init j' => left; have := (el1 j').2; omega
    | initOff => left; omega
    | scanOff n t hn ht => left; omega
    | scan q' s' hq' =>
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        obtain rfl := hq'.unique hq
        exact .inr ⟨rfl, rfl, rfl⟩
    | mid a N t o hT hM => have := R.pos_lt hc.symm hT hq; have := R.ge hM; omega
    | scan2Off a n t hT hn => have := R.pos_lt hc.symm hT hq; omega
    | scan2 a n0 v0 q' s' hT hps =>
      have := R.pos_lt hc.symm hT hq; have := R.pass2 hT hps; omega
    | end1 ns nv t hx | end2 a ns nv t hT hx =>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx
      omega
  | mid a N t o0 hT hM =>
    cases o0 with
    | none => cases ho
    | some y =>
      cases ho
      have hT8 := R.tge hM
      cases hH with
      | start j' => left; have := sh1 j'; omega
      | init j' => left; have := (el1 j').2; omega
      | initOff => left; omega
      | scanOff n t hn ht ht' => left; omega
      | scan q' s' hq' => left; have := R.pos_lt hc hT hq'; have := R.ch_le hp hT; omega
      | mid a' N' t' o' hT' hM' =>
        obtain rfl := R.same hc hT hT'
        rcases R.order hM hM' (by omega) with h1 | ⟨rfl, rfl, rfl⟩
        · exact .inl h1
        · exact .inr ⟨rfl, rfl, rfl⟩
      | scan2Off a' n t hT' hn =>
        obtain rfl := R.same hc hT hT'
        have := R.lt_tot hM
        omega
      | scan2 a' n0 v0 q s hT' hps =>
        obtain rfl := R.same hc hT hT'
        have := R.lt_tot hM
        have := R.pass2 hT' hps
        omega
      | end1 ns nv t hx => exact (R.not_exit hc hT hx).elim
      | end2 a' ns nv t hT' hx' =>
        obtain rfl := R.same hc hT hT'
        have := R.lt_tot hM
        have := R.exit2 hT' hx'
        omega
  | scan2 a n0 v0 q s hT hps hq hv =>
    cases ho
    have hge := R.pass2 hT hps
    have hcg := R.ch_ge hT
    cases hH with
    | start j' => left; have := sh1 j'; omega
    | init j' => left; have := (el1 j').2; omega
    | initOff => left; omega
    | scanOff n t hn ht ht' => left; omega
    | scan q' s' hq' => left; have := R.pos_lt hc hT hq'; have := R.ch_le hp hT; omega
    | mid a' N' t' o' hT' hM' => left; have := R.lt_end hh hT' hM'; omega
    | scan2Off a' n t hT' hn ht ht' =>
      obtain rfl := R.same hc hT hT'
      left; omega
    | scan2 a' n0' v0' q' s' hT' hps' hq' hv' =>
      obtain rfl := R.same hc hT hT'
      have hge' := R.pass2 hT' hps'
      rcases Nat.lt_or_eq_of_le hle with h1 | h1
      · left; omega
      · obtain rfl : q' = q := by omega
        rw [hc] at hq'
        obtain rfl := hq'.unique hq
        refine .inr ⟨by omega, rfl, by omega⟩
    | end1 ns nv t hx => exact (R.not_exit hc hT hx).elim
    | end2 a' ns nv t hT' hx =>
      obtain rfl := R.same hc hT hT'
      have := Epilogue.pos_lt_exit hps hq hc.symm hx
      omega

/-- Where a lane that returns stands. -/
def SExitN (R : Mid p L β τ) (g E0 N : Nat) : Prop :=
  (∃ ns nv, Epilogue.Fits.ExitAt p L g false ns nv ∧ N = E0 + (ns + nv)) ∨
    ∃ a ns nv, R.tile g a ∧ Epilogue.Fits.ExitAt p L g true ns nv ∧
      N = E0 + R.tot a + (ns + nv)

/-- **A lane returns after more collectives than a lane at one has made.** -/
theorem SCls.lt_exit {R : Mid p L β τ} {E0 N N' t : Nat} {x : STag β}
    (hc : h / L.block = g / L.block) (hG : SCls R g E0 N t (some x)) (hH : SExitN R h E0 N') :
    N < N' := by
  have hge : E0 + 10 ≤ N' := by
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨a, ns, nv, -, hx, rfl⟩ <;>
      have := Epilogue.exit_ge hx <;> omega
  generalize ho : some x = ox at hG
  cases hG with
  | initOff | scanOff | scan2Off | end1 | end2 => cases ho
  | start j => have := j.isLt; omega
  | init j hE => have := j.isLt; omega
  | scan q s hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨a, ns, nv, -, hx, rfl⟩ <;>
      have := Epilogue.pos_lt_exit (L := L) (g := g) (n0 := 3) (v0 := 0)
        (by simp [Epilogue.PassStart]) hq hc.symm hx <;> omega
  | mid a N t o0 hT hM =>
    cases o0 with
    | none => cases ho
    | some y =>
      rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨a', ns, nv, hT', hx', rfl⟩
      · exact (R.not_exit hc hT hx).elim
      · obtain rfl := R.same hc hT hT'
        have := R.lt_tot hM
        have := R.exit2 hT' hx'
        omega
  | scan2 a n0 v0 q s hT hps hq =>
    rcases hH with ⟨ns, nv, hx, rfl⟩ | ⟨a', ns, nv, hT', hx', rfl⟩
    · exact (R.not_exit hc hT hx).elim
    · obtain rfl := R.same hc hT hT'
      have := Epilogue.pos_lt_exit hps hq hc.symm hx'
      omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
