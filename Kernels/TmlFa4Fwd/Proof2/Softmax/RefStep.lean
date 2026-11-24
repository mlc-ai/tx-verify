-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.RefCases
public import Kernels.TmlFa4Fwd.Proof2.Softmax.RefEv

@[expose] public section

/-! # The softmax warps' counts are kept by every step

`counts_step`: a step of the softmax machine on an event of the state's shape that is no
undefined behaviour keeps the count conjuncts (`RefQ`), with the rounds done updated: one more
biased round at the end of a biased round, one more plain round at the end of a plain round. The
round counters `%r6188` and `%r6194` are kept in closed form (`rb - nB - 1`, `rp - nP`), so the
exit tests of the rounds, on 32-bit words, decide `rb + 1 = nB` and `rp + 1 = nP`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32 (i32_addi toSigned_r32 ne_m1 ne_0 scmpi_lt1 neg_eq sub32_swap xor_par)
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (r32 i32 addi sub32 xor32 scmpi)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### Site facts, checked by evaluation -/

theorem moveOk_of {lzb : Bool} {s s' : Site} (h : s' ∈ nexts lzb s) : moveOk lzb s s' = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp moves_ok lzb (by
    cases lzb <;> simp)) s (mem_allSites s)) s' h

set_option maxRecDepth 100000 in
theorem nexts_facts_all : [false, true].all (fun lzb => allSites.all fun s =>
    (nexts lzb s).all fun s' => (!s'.isParr2 || s.isPel) && (!s'.isBarr || lzb)) = true := by
  decide +kernel

theorem nexts_facts {lzb : Bool} {s s' : Site} (h : s' ∈ nexts lzb s) :
    (s'.isParr2 = true → s.isPel = true) ∧ (s'.isBarr = true → lzb = true) := by
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp nexts_facts_all lzb (by
    cases lzb <;> simp)) s (mem_allSites s)) s' h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this
  constructor
  · intro hp; rcases h1 with h1 | h1
    · simp [h1] at hp
    · exact h1
  · intro hb; rcases h2 with h2 | h2
    · simp [h2] at hb
    · exact h2

theorem sig_a112 (s : Site) : sig s = some (.arrive 112) ↔ s.isParr2 = true := by
  cases s <;> simp [sig, Site.isParr2]

theorem pel_parr2 {s : Site} (h : s.isPel = true) : s.isParr2 = false := by
  cases s <;> simp_all [Site.isPel, Site.isParr2]

/-! ### The round counts read only the tile's words -/

theorem nB_congr {v v' : V} (h : frameT v v') : nB p L g v' = nB p L g v := by
  obtain ⟨h1, h2⟩ := h
  simp only [nB, r169, r299, r166, r165, r168, r1808, rowOff, h1, h2]

theorem nP_congr {v v' : V} (h : frameT v v') : nP p L g v' = nP p L g v := by
  obtain ⟨h1, h2⟩ := h
  simp only [nP, r431, r169, r299, r166, r165, r168, r1808, rowOff, h1, h2]

theorem nB_lt (v : V) : nB p L g v < 2 ^ 31 := (toSigned_r32 _).2
theorem nP_lt (v : V) : nP p L g v < 2 ^ 31 := (toSigned_r32 _).2

/-- The bias counter's first value. -/
theorem nb_init (v : V) : sub32 (r299 p L g v) (r166 p L g v) = i32 (0 - nB p L g v - 1) := by
  rw [sub32_swap]; rfl

/-- The plain counter's first value. -/
theorem pl_init (v : V) : Mma.neg32 (r431 p L g v) = i32 (0 - nP p L g v) := neg_eq _

/-! ### The count conjuncts -/

theorem bump_sig {e : Event} {n : Cnt → Nat} {s : Site} {c : Cnt}
    (hc : cls L g c e = decide (sig s = some c)) :
    Code.bump (cls L g) n e c = n c + if sig s = some c then 1 else 0 := by
  simp only [Code.bump, hc, decide_eq_true_eq]

/-- The pointed counts after a move from `d` to `d'` that passes the point of `d`'s site. -/
theorem cnt_move {d d' : D} {e : Event} {n : Cnt → Nat} {rb rp rb' rp' : Nat}
    (hQ : RefQ p L g d n rb rp)
    (hc : ∀ c, c.sited = true → cls L g c e = decide (sig d.site = some c))
    (hp : ∀ c, passed (ptsOf (lz L g) c) d'.site rb' rp' =
      passed (ptsOf (lz L g) c) d.site rb rp + if d.site.pos ∈ ptsOf (lz L g) c then 1 else 0)
    (c : Cnt) (hcs : c.pointed = true) :
    Code.bump (cls L g) n e c = passed (ptsOf (lz L g) c) d'.site rb' rp' := by
  rw [bump_sig (hc c (by simp [Cnt.sited, hcs])), hQ.cnt c hcs, hp c]
  congr 1
  by_cases h : sig d.site = some c
  · simp [h, (sig_pts d.site hcs hQ.barr).mpr h]
  · have : d.site.pos ∉ ptsOf (lz L g) c := fun hm => h ((sig_pts d.site hcs hQ.barr).mp hm)
    simp [h, this]

/-- The elected lane's arrivals after a move. -/
theorem elect_move {d d' : D} {e : Event} {n : Cnt → Nat} {rb rp : Nat}
    (hQ : RefQ p L g d n rb rp) (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hc : ∀ c, c.sited = true → cls L g c e = decide (sig d.site = some c))
    (hF : MoveFacts L g d d' e) :
    Code.bump (cls L g) n e (.arrive 112) + (if d'.site.isParr2 then 1 else 0) =
      Code.bump (cls L g) n e (.won 4859) + Code.bump (cls L g) n e (.won 6544) +
        Code.bump (cls L g) n e (.won 7449) := by
  have hE := hQ.elect
  have hn := nexts_facts hF.1
  rw [bump_sig (hc _ (by decide))]
  by_cases hpel : d.site.isPel = true
  · obtain ⟨s, v, k, acc⟩ := d
    cases s <;> simp [Site.isPel] at hpel
    rename_i r
    obtain ⟨m, inst, ld, hk, hw⟩ := ev_won_pel hev hub
    have hpar := hF.2.2.2.2.2.2.2 rfl m inst ld hk
    by_cases hld : ld = laneOf L g
    · have h2 : d'.site.isParr2 = true := hpar.mpr hld.symm
      rw [h2]
      simp only [Code.bump, hw] at hE ⊢
      simp only [Site.isParr2, sig, ite_false] at hE ⊢
      cases r <;> simp [Site.pc, Rd.pc, hld] at hE ⊢ <;> omega
    · have h2 : d'.site.isParr2 = false := by
        cases h : d'.site.isParr2
        · rfl
        · exact absurd (hpar.mp h).symm hld
      rw [h2]
      simp only [Code.bump, hw] at hE ⊢
      simp only [Site.isParr2, sig, ite_false] at hE ⊢
      cases r <;> simp [Site.pc, Rd.pc, hld] at hE ⊢ <;> omega
  · have hw : ∀ pc, cls L g (.won pc) e = false := ev_won hev hub (by simpa using hpel)
    have h2 : d'.site.isParr2 = false := by
      cases h : d'.site.isParr2
      · rfl
      · exact absurd (hn.1 h) hpel
    simp only [Code.bump, hw, h2]
    by_cases h1 : d.site.isParr2 = true
    · simp only [(sig_a112 _).mpr h1, h1] at hE ⊢; simp at hE ⊢; omega
    · have : sig d.site ≠ some (.arrive 112) := fun h => h1 ((sig_a112 _).mp h)
      simp only [this, ↓reduceIte] at hE ⊢
      simp only [Bool.not_eq_true] at h1
      simp [h1] at hE ⊢; omega

/-- A move from a site that does not end a round passes the site's point and enters no
region. -/
theorem moveOk_pmove {lzb : Bool} {s s' : Site} (hs : s.special = false)
    (h : moveOk lzb s s' = true) : pmove lzb s s' = true ∧ regOk s s' = true := by
  cases s
  case pwend r => simp [Site.special] at hs
  all_goals (simp only [moveOk, Site.special, Bool.false_or, Bool.and_eq_true] at h; exact h)

/-! ### The step -/

/-- A step that stays at its site with its values fires no event of a class. -/
theorem bump_stay {d : D} {e : Event} {n : Cnt → Nat} (hev : Ev p L g d e) (hN : NoCls d e) :
    Code.bump (cls L g) n e = n := by
  funext c
  rcases hN with ⟨m, par, a, sc, hk⟩ | ⟨a, bs, hk⟩ | ⟨hd, hk0⟩
  · cases c <;> simp [Code.bump, cls, hk]
  · cases c <;> simp [Code.bump, cls, hk]
  · obtain ⟨s, v, k, acc⟩ := d
    simp only at hd hk0
    subst hk0
    cases s <;> (try simp [Site.delayed] at hd)
    rename_i r q
    have hk : e.kind = .tc .waitLd := by
      simp only [Ev] at hev
      split at hev
      · exact hev
      · rename_i hn; exact absurd (by rw [Bool.and_eq_true]; exact ⟨hd, rfl⟩) hn
    cases c <;> simp [Code.bump, cls, hk]

/-- The count conjuncts after a step that stays at its site with its values. -/
theorem refq_stay {d d' : D} {n : Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d n rb rp)
    (hs : d'.site = d.site) (hv : d'.v = d.v) (hw : d.site.isSldw = false) :
    RefQ p L g d' n rb rp := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨s', v', k', acc'⟩ := d'
  simp only at hs hv hw
  subst hs hv
  exact ⟨hQ.cnt, hQ.elect, hQ.barr, hQ.pre, hQ.bias, hQ.plain, hQ.after, hQ.fin, hQ.noTile,
    fun c h => by simp only at h; subst h; simp [Site.isSldw] at hw⟩

/-- The pwend step's successor. -/
theorem succ_pwend {r : Rd} {v : V} {k : Fin 4} {acc : List Value} {e : Event} {d' : D}
    (h : succ p L g ⟨.pwend r, v, k, acc⟩ e = some (some d')) :
    (∃ m par a sc, e.kind = .wait m par false a sc) ∨
      d' = afterRound p L g ⟨.pwend r, v, k, acc⟩ r := by
  simp only [succ] at h
  split at h
  · rename_i m par ok a sc hk
    cases ok
    · exact .inl ⟨m, par, a, sc, hk⟩
    · simp only [↓reduceIte, Option.some.injEq] at h
      exact .inr h.symm
  · cases h

theorem parB_one (v : V) (h1 : v.spar = i32 1) (h2 : v.ppar = i32 1) (h3 : v.bpar = i32 1) :
    parB 1 v := by
  simp only [parB, Nat.one_mod, Nat.cast_one]; exact ⟨h1, h2, h3⟩

/-- A flipped parity word. -/
theorem par_flip {x : BitVec 64} {j : Nat} (h : x = i32 ((j % 2 : Nat) : Int)) :
    xor32 x (i32 1) = i32 (((j + 1) % 2 : Nat) : Int) := by
  rw [h, xor_par]

/-! ### The round counts as functions of the tile's words

`nBt`, `nPt` take the scan and the used-K length, so that the round counts of a successor's
values (a structure update of the state's values) evaluate to those of the state by projection. -/

def nBt (p : Params) (L : Launch) (g : Nat) (sc : Epilogue.D) (ukw : BitVec 64) : Int :=
  nB p L g { sc := sc, ukw := ukw }
def nPt (p : Params) (L : Launch) (g : Nat) (sc : Epilogue.D) (ukw : BitVec 64) : Int :=
  nP p L g { sc := sc, ukw := ukw }

theorem nB_t (v : V) : nB p L g v = nBt p L g v.sc v.ukw := (nB_congr ⟨rfl, rfl⟩).symm
theorem nP_t (v : V) : nP p L g v = nPt p L g v.sc v.ukw := (nP_congr ⟨rfl, rfl⟩).symm

theorem lt1_nB (v : V) :
    scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = decide (nB p L g v < 1) := by
  rw [scmpi_lt1]; rfl
theorem lt1_nP (v : V) : scmpi .lt .s (r431 p L g v) 1 = decide (nP p L g v < 1) := by
  rw [scmpi_lt1]; rfl

/-- The bias counter's first value, by the round count of its scan and used-K length. -/
theorem nb_init' (v : V) :
    sub32 (r299 p L g v) (r166 p L g v) = i32 (0 - nBt p L g v.sc v.ukw - 1) := by
  rw [nb_init, nB_t]
theorem pl_init' (v : V) : Mma.neg32 (r431 p L g v) = i32 (0 - nPt p L g v.sc v.ukw) := by
  rw [pl_init, nP_t]

set_option hygiene false in
/-- A region the successor does not enter. -/
macro "not_in" : tactic => `(tactic| (intro h; dsimp only at h; exact absurd h (by decide)))

set_option hygiene false in
/-- A plain load's implicit wait is not the successor. -/
macro "no_wait" : tactic => `(tactic| (intro c h; dsimp only at h; cases h))

/-- **The end of the first round.** -/
theorem refq_first {v : V} {k : Fin 4} {acc : List Value} {e : Event} {n : Cnt → Nat}
    (hQ : RefQ p L g ⟨.pwend .first, v, k, acc⟩ n 0 0)
    (hc : ∀ c, c.sited = true → cls L g c e = decide (sig (.pwend .first) = some c))
    (hm : pmove (lz L g) (.pwend .first) (afterFirst p L g ⟨.pwend .first, v, k, acc⟩).site =
      true)
    (hel : Code.bump (cls L g) n e (.arrive 112) +
      (if (afterFirst p L g ⟨.pwend .first, v, k, acc⟩).site.isParr2 then 1 else 0) =
      Code.bump (cls L g) n e (.won 4859) + Code.bump (cls L g) n e (.won 6544) +
        Code.bump (cls L g) n e (.won 7449)) :
    RefQ p L g (afterFirst p L g ⟨.pwend .first, v, k, acc⟩) (Code.bump (cls L g) n e) 0 0 := by
  have hq := cnt_move hQ hc (passed_move (lz := lz L g) 0 0 hm)
  revert hq hel
  simp only [afterFirst, plainEntry, D.ite, D.mk', lt1_nB, lt1_nP, nB_t, nP_t]
  by_cases h1 : nBt p L g v.sc v.ukw < 1
  · by_cases h2 : nPt p L g v.sc v.ukw < 1
    · simp only [h1, h2, decide_true, ↓reduceIte]
      intro hel hq
      refine ⟨hq, hel, by not_in, fun _ => ⟨rfl, rfl⟩, by not_in, by not_in, fun _ => rfl,
        fun _ => ⟨.inr ⟨rfl, ?_⟩, .inr ⟨rfl, ?_⟩⟩, by not_in, by no_wait⟩
      · simp only [nB_t]; exact h1
      · simp only [nP_t]; exact h2
    · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
      intro hel hq
      refine ⟨hq, hel, by not_in, by not_in, by not_in,
        fun _ => ⟨⟨rfl, rfl⟩, ?_, ?_, .inr ⟨rfl, ?_⟩⟩, by not_in, by not_in, by not_in,
        by no_wait⟩
      · simp only [nP_t]; push_cast; omega
      · dsimp only; rw [pl_init', nP_t]; rfl
      · simp only [nB_t]; exact h1
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    intro hel hq
    refine ⟨hq, hel, by not_in, by not_in,
      fun _ => ⟨rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩, by not_in, by not_in, by not_in, by not_in,
      by no_wait⟩
    · simp only [nB_t]; push_cast; omega
    · dsimp only; rw [nb_init', nB_t]; rfl

/-- **The end of a biased round.** -/
theorem refq_bias {v : V} {k : Fin 4} {acc : List Value} {e : Event} {n : Cnt → Nat}
    {rb rp : Nat} (hQ : RefQ p L g ⟨.pwend .bias, v, k, acc⟩ n rb rp)
    (hc : ∀ c, c.sited = true → cls L g c e = decide (sig (.pwend .bias) = some c))
    (hm : rmove (lz L g) inBias (.pwend .bias)
      (afterBias p L g ⟨.pwend .bias, v, k, acc⟩).site = true)
    (hel : Code.bump (cls L g) n e (.arrive 112) +
      (if (afterBias p L g ⟨.pwend .bias, v, k, acc⟩).site.isParr2 then 1 else 0) =
      Code.bump (cls L g) n e (.won 4859) + Code.bump (cls L g) n e (.won 6544) +
        Code.bump (cls L g) n e (.won 7449)) :
    RefQ p L g (afterBias p L g ⟨.pwend .bias, v, k, acc⟩) (Code.bump (cls L g) n e)
      (rb + 1) 0 := by
  obtain ⟨hrp, ⟨hs, hpp, hbp⟩, hlt, hnb⟩ := hQ.bias (by dsimp only; decide)
  subst hrp
  have hq := cnt_move hQ hc (passed_rmoveB (lz := lz L g) rb 0 hm)
  simp only [nB_t] at hlt hnb
  have hB0 := nB_lt (p := p) (L := L) (g := g) { sc := v.sc, ukw := v.ukw }
  have hstep : addi v.nb 1 = i32 ((rb : Int) - nBt p L g v.sc v.ukw) := by
    rw [hnb, i32_addi, sub_add_cancel]
  have c1 : scmpi .ne .b (addi v.nb 1) (-1) = decide ((rb : Int) + 1 ≠ nBt p L g v.sc v.ukw) := by
    rw [hstep]
    by_cases h : (rb : Int) + 1 ≠ nBt p L g v.sc v.ukw
    · rw [(ne_m1 (by unfold nBt; omega) (by omega)).mpr (by omega)]; simp [h]
    · have : ¬ (scmpi .ne .b (i32 ((rb : Int) - nBt p L g v.sc v.ukw)) (-1) = true) := fun h' =>
        h (by have := (ne_m1 (by unfold nBt; omega) (by omega)).mp h'; omega)
      simp only [Bool.not_eq_true] at this; rw [this]; simp [h]
  have hs' := par_flip (j := 1 + rb) hs
  have hpp' := par_flip (j := 1 + rb) hpp
  have hbp' := par_flip (j := 1 + rb) hbp
  have e1 : 1 + rb + 1 = 1 + (rb + 1) := by omega
  have e2 : 1 + rb + 1 = 1 + (rb + 1) + 0 := by omega
  rw [e1] at hs' hpp' hbp'
  revert hq hel
  simp only [afterBias, plainEntry, D.ite, D.mk', lt1_nP, nP_t, c1]
  by_cases h1 : (rb : Int) + 1 ≠ nBt p L g v.sc v.ukw
  · simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    intro hel hq
    refine ⟨hq, hel, by not_in, by not_in,
      fun _ => ⟨rfl, ⟨hs', hpp', hbp'⟩, ?_, ?_⟩, by not_in, by not_in, by not_in, by not_in,
      by no_wait⟩
    · simp only [nB_t]; push_cast; omega
    · simp only [nB_t]
      rw [hstep, show ((rb + 1 : Nat) : Int) - nBt p L g v.sc v.ukw - 1 =
        (rb : Int) - nBt p L g v.sc v.ukw by push_cast; ring]
  · have hdone : ((rb + 1 : Nat) : Int) = nBt p L g v.sc v.ukw := by push_cast; omega
    have h1e : (rb : Int) + 1 = nBt p L g v.sc v.ukw := by omega
    simp only [h1e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [show 1 + (rb + 1) = 1 + (rb + 1) + 0 by omega] at hs' hpp'
    by_cases h2 : nPt p L g v.sc v.ukw < 1
    · simp only [h2, decide_true, ↓reduceIte]
      intro hel hq
      refine ⟨hq, hel, by not_in, by not_in, by not_in, by not_in,
        fun _ => hpp', fun _ => ⟨.inl ?_, .inr ⟨rfl, ?_⟩⟩, by not_in, by no_wait⟩
      · simp only [nB_t]; exact hdone
      · simp only [nP_t]; exact h2
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      intro hel hq
      refine ⟨hq, hel, by not_in, by not_in, by not_in,
        fun _ => ⟨⟨hs', hpp'⟩, ?_, ?_, .inl ?_⟩, by not_in, by not_in, by not_in,
        by no_wait⟩
      · simp only [nP_t]; push_cast; omega
      · dsimp only; rw [pl_init', nP_t]; rfl
      · simp only [nB_t]; exact hdone

/-- The count conjuncts do not read the recorded row maximum and sum. -/
theorem refQ_rec {s : Site} {v : V} {k : Fin 4} {acc : List Value} {n : Cnt → Nat} {rb rp : Nat}
    {a : Bool} {b c : ℝ} (h : RefQ p L g ⟨s, v, k, acc⟩ n rb rp) :
    RefQ p L g ⟨s, { v with mf := a, mr := b, rs := c }, k, acc⟩ n rb rp :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10⟩

/-- **The end of a plain round.** -/
theorem refq_plain {v : V} {k : Fin 4} {acc : List Value} {e : Event} {n : Cnt → Nat}
    {rb rp : Nat} (hQ : RefQ p L g ⟨.pwend .plain, v, k, acc⟩ n rb rp)
    (hc : ∀ c, c.sited = true → cls L g c e = decide (sig (.pwend .plain) = some c))
    (hm : rmove (lz L g) inPlain (.pwend .plain)
      (afterPlain ⟨.pwend .plain, v, k, acc⟩).site = true)
    (hel : Code.bump (cls L g) n e (.arrive 112) +
      (if (afterPlain ⟨.pwend .plain, v, k, acc⟩).site.isParr2 then 1 else 0) =
      Code.bump (cls L g) n e (.won 4859) + Code.bump (cls L g) n e (.won 6544) +
        Code.bump (cls L g) n e (.won 7449)) :
    RefQ p L g (afterPlain ⟨.pwend .plain, v, k, acc⟩) (Code.bump (cls L g) n e) rb (rp + 1) := by
  obtain ⟨⟨hs, hpp⟩, hlt, hpl, hdb⟩ := hQ.plain (by dsimp only; decide)
  have hq := cnt_move hQ hc (passed_rmoveP (lz := lz L g) rb rp hm)
  simp only [nP_t, nB_t] at hlt hpl hdb
  have hP0 := nP_lt (p := p) (L := L) (g := g) { sc := v.sc, ukw := v.ukw }
  have hstep : addi v.pl 1 = i32 ((rp : Int) + 1 - nPt p L g v.sc v.ukw) := by
    rw [hpl, i32_addi, sub_add_eq_add_sub]
  have c1 : scmpi .ne .b (addi v.pl 1) 0 = decide ((rp : Int) + 1 ≠ nPt p L g v.sc v.ukw) := by
    rw [hstep]
    by_cases h : (rp : Int) + 1 ≠ nPt p L g v.sc v.ukw
    · rw [(ne_0 (by unfold nPt; omega) (by omega)).mpr (by omega)]; simp [h]
    · have : ¬ (scmpi .ne .b (i32 ((rp : Int) + 1 - nPt p L g v.sc v.ukw)) 0 = true) :=
        fun h' => h (by have := (ne_0 (by unfold nPt; omega) (by omega)).mp h'; omega)
      simp only [Bool.not_eq_true] at this; rw [this]; simp [h]
  have hs' := par_flip (j := 1 + rb + rp) hs
  have hpp' := par_flip (j := 1 + rb + rp) hpp
  rw [show 1 + rb + rp + 1 = 1 + rb + (rp + 1) by omega] at hs' hpp'
  revert hq hel
  simp only [afterPlain, D.ite, D.mk', c1]
  by_cases h1 : (rp : Int) + 1 ≠ nPt p L g v.sc v.ukw
  · simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    intro hel hq
    refine ⟨hq, hel, by not_in, by not_in, by not_in,
      fun _ => ⟨⟨hs', hpp'⟩, ?_, ?_, ?_⟩, by not_in, by not_in, by not_in, by no_wait⟩
    · simp only [nP_t]; push_cast; omega
    · simp only [nP_t]; rw [hstep]; try push_cast; try rfl
    · simp only [nB_t]; exact hdb
  · have h1e : (rp : Int) + 1 = nPt p L g v.sc v.ukw := by omega
    simp only [h1e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    intro hel hq
    refine ⟨hq, hel, by not_in, by not_in, by not_in, by not_in,
      fun _ => hpp', fun _ => ⟨?_, .inl ?_⟩, by not_in, by no_wait⟩
    · simp only [nB_t]; exact hdb
    · simp only [nP_t]; push_cast; omega

set_option maxRecDepth 100000 in
/-- **The counts are kept by every step** of the softmax machine on an event of the state's shape
that is no undefined behaviour. -/
theorem counts_step (hp : Pre p L m) {d d' : D} {e : Event} {n : Cnt → Nat} {rb rp : Nat}
    (hQ : RefQ p L g d n rb rp) (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (h : succ p L g d e = some (some d')) :
    ∃ rb' rp', RefQ p L g d' (Code.bump (cls L g) n e) rb' rp' := by
  rcases succ_cases h with ⟨hs, hv, hw, hN⟩ | hF
  · exact ⟨rb, rp, by rw [bump_stay hev hN]; exact refq_stay hQ hs hv hw⟩
  have hc := fun (c : Cnt) (hcs : c.sited = true) =>
    ev_cls hp hev hub hF.2.2.1 hF.2.2.2.1 hQ.wait hcs
  have hel := elect_move hQ hev hub hc hF
  have hm := moveOk_of hF.1
  have hn := nexts_facts hF.1
  obtain ⟨s, v, k, acc⟩ := d
  simp only at hm hn hF hel hc
  by_cases hsp : s.special = true
  · -- the end of a round
    cases s <;> simp [Site.special] at hsp
    rename_i r
    rcases succ_pwend h with ⟨m, par, a, sc, hk⟩ | hd'
    · exact absurd hk (hF.2.2.1 rfl m par a sc)
    subst hd'
    simp only [moveOk, Bool.and_eq_true] at hm
    cases r
    · obtain ⟨hrb, hrp⟩ := hQ.pre (by dsimp only; decide)
      subst hrb hrp
      exact ⟨0, 0, refq_first hQ hc hm.1 hel⟩
    · obtain ⟨hrp, -⟩ := hQ.bias (by dsimp only; decide)
      subst hrp
      exact ⟨rb + 1, 0, refq_bias hQ hc hm.1 hel⟩
    · exact ⟨rb, rp + 1, refq_plain (refQ_rec hQ) hc hm.1 hel⟩
  · -- a move inside a region, or into one from before it
    have hsp' : s.special = false := by simpa using hsp
    obtain ⟨hpm, hreg⟩ := moveOk_pmove hsp' hm
    simp only [regOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hreg
    obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := hreg
    have hfP := hF.2.2.2.2.1 hsp'
    have hfT := hF.2.2.2.2.2.1 hsp'
    refine ⟨rb, rp, cnt_move hQ hc (passed_move rb rp hpm), hel, hn.2, ?_, ?_, ?_, ?_, ?_, ?_,
      fun c hc' => by rw [hF.2.1, hc']; rfl⟩
    · intro h'
      rcases hr3 with h3 | h3
      · simp [h'] at h3
      · exact hQ.pre h3
    · intro h'
      have hin : inBias s.pos = true := by rcases hr1 with h1 | h1 <;> simp_all
      obtain ⟨a1, a2, a3, a4⟩ := hQ.bias hin
      obtain ⟨f1, f2, f3, f4, f5⟩ := hfP (.inl h')
      obtain ⟨t1, t2⟩ := hfT (.inl h')
      simp only at a2 a3 a4
      refine ⟨a1, ?_, ?_, ?_⟩
      · simp only [parB] at a2 ⊢; rw [f1, f2, f3]; exact a2
      · rw [nB_congr ⟨t1, t2⟩]; exact a3
      · rw [nB_congr ⟨t1, t2⟩, f4]; exact a4
    · intro h'
      have hin : inPlain s.pos = true := by rcases hr2 with h1 | h1 <;> simp_all
      obtain ⟨a1, a2, a3, a4⟩ := hQ.plain hin
      obtain ⟨f1, f2, f3, f4, f5⟩ := hfP (.inr (.inl h'))
      obtain ⟨t1, t2⟩ := hfT (.inr (.inl h'))
      simp only at a1 a2 a3 a4
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [parP] at a1 ⊢; rw [f1, f2]; exact a1
      · rw [nP_congr ⟨t1, t2⟩]; exact a2
      · rw [nP_congr ⟨t1, t2⟩, f5]; exact a3
      · rw [nB_congr ⟨t1, t2⟩]; exact a4
    · intro h'
      have hin : afterR s = true := by rcases hr4 with h1 | h1 <;> simp_all
      obtain ⟨f1, f2, f3, f4, f5⟩ := hfP (.inr (.inr h'))
      rw [f2]; exact hQ.after hin
    · intro h'
      have hin : finR s = true := by rcases hr5 with h1 | h1 <;> simp_all
      obtain ⟨t1, t2⟩ := hfT (.inr (.inr h'))
      rw [nB_congr ⟨t1, t2⟩, nP_congr ⟨t1, t2⟩]; exact hQ.fin hin
    · intro h'
      rcases hF.2.2.2.2.2.2.1 h' with h1 | ⟨h1, h2⟩
      · exact h1
      · rw [h2]; exact hQ.noTile h1

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
