-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
public import Kernels.TmlFa4Fwd.Proof.Lib.Interval
public import Kernels.TmlFa4Fwd.Proof.Mma.Warp
public import Lemmas.Kernel.Source.WarpColl
public import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # What the MMA warp's broadcasts deliver

Every pipeline broadcast of the MMA warp (`sh k`) sends lane 0's operand of a broadcast site
(`shSrc`): a constant, the K/V slot's descriptor word, or the first stage's descriptor word. All of
them have the pattern `BW`: below `2 ^ 27`, with their low 16 bits at most 16320 (an `and` with
16320 and a tag bit 16 or 26, or a small constant). The broadcast before the scan (`bcast`) sends
the Q descriptors' base `qx`. `recv_word`: a lane at a broadcast site receives such a word, from
the source lane at the same broadcast instance, which is at a broadcast site too (a scan shuffle
and the startup's shuffles are at other shuffle counts, `mshfl_same`, `mband`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The pattern of a broadcast word. -/
def BW (x : BitVec 64) : Prop := x.toNat < 2 ^ 27 ∧ x.toNat % 65536 ≤ 16320

/-- The Q descriptors' base, which the broadcast before the scan sends. -/
abbrev qx (L : Launch) : BitVec 64 := ori (andi (shru (addi (sbW L) 35840) 4) 16320) 65536

theorem bw_i32 (n : Nat) (h : n ≤ 16320) : BW (i32 n) := by
  unfold BW; rw [toNat_i32 n (by omega)]; omega

/-- A masked word with a tag bit. -/
theorem bw_ori (y : BitVec 64) (t : Nat) (ht : t = 16 ∨ t = 26) :
    BW (ori (andi y 16320) (2 ^ t : Nat)) := by
  have hi : (i32 ((2 ^ t : Nat) : Int)).toNat = 2 ^ t :=
    toNat_i32 _ (by rcases ht with rfl | rfl <;> decide)
  have ha : (andi y 16320).toNat ≤ 16320 := (iv_andi (x := y) 16320 (by decide)).2
  have hr : (r32 (andi y 16320)).toNat = (andi y 16320).toNat := by
    rw [toNat_r32]; omega
  unfold BW
  simp only [ori, BitVec.toNat_or, hr, hi]
  have hlt : (andi y 16320).toNat < 2 ^ t := by rcases ht with rfl | rfl <;> omega
  rw [Nat.or_two_pow_eq_add_of_lt hlt]
  rcases ht with rfl | rfl <;> omega

/-- **Every broadcast operand has the pattern.** -/
theorem bw_shSrc (v : V) (k : Fin 14) : BW (shSrc L v k) := by
  fin_cases k
  · exact bw_ori _ 16 (.inl rfl)
  · exact bw_i32 0 (by decide)
  · exact bw_i32 128 (by decide)
  · exact bw_i32 64 (by decide)
  · exact bw_ori _ 26 (.inr rfl)
  · exact bw_i32 256 (by decide)
  · exact bw_ori _ 16 (.inl rfl)
  · exact bw_i32 192 (by decide)
  · exact bw_i32 384 (by decide)
  · exact bw_i32 64 (by decide)
  · exact bw_ori _ 26 (.inr rfl)
  · exact bw_i32 256 (by decide)
  · exact bw_i32 192 (by decide)
  · exact bw_i32 384 (by decide)

/-- A state past the broadcast before the scan is at shuffle count 4 or more. -/
theorem four_of {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) (he : d.site.early = false) :
    4 ≤ ns := by
  obtain ⟨h1, h2, -⟩ := mfits_main he hF
  have := Epilogue.fits_three h2
  omega

set_option maxHeartbeats 4000000 in
/-- **A broadcast site receives a broadcast word**: the Q base at `bcast`, a word of the pattern at
a pipeline broadcast. -/
theorem recv_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {a recv : Value}
    {b c : Nat} {mode : ShflMode} {ok : Bool} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hJ : RefCounts p L g (d, rc n)) (hF : MFits p L g d (n .shfl) (n .vote))
    (IH : GoodUpTo p L X (n .shfl + n .vote))
    (hs : d.site = .bcast ∨ ∃ i, d.site = .sh i) :
    ∃ x, recv = .bits 32 x ∧ (d.site = .bcast → x = qx L) ∧ BW x := by
  have hev := (mfired hp hX he hσ).1
  have hmode : mode = .idx ∧ b = 0 ∧ c = 31 := by
    rcases hs with hs | ⟨i, hs⟩ <;> simp only [Ev, hs, Kind.shfl.injEq] at hev <;>
      obtain ⟨_, _, h1, -, h2, h3, -⟩ := hev <;> exact ⟨h1, h2, h3⟩
  obtain ⟨rfl, rfl, rfl⟩ := hmode
  have hsl := Step.shflSource_lt .idx (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hsT, hsW, hsC, -, -⟩ := lane_facts hp hg hw hsl
  obtain ⟨j, pc', b', c', r', o', hj, hG, hcj⟩ := mshfl_src hp hX hg hw he hσ hJ hF IH
  have h3 := mfits_three hF
  obtain ⟨d1, n1, -, hJ1, hF1, hE1, hs1, -⟩ :=
    role_at hp hX hj hG (.inr (.inr ⟨rfl, by omega⟩))
  have hn1 : n1 .shfl = n .shfl := by omega
  rcases msh_cases ((mev_coll hE1).1 rfl) with hb | ⟨i, hi⟩ | hse
  · simp only [Ev, hb, Kind.shfl.injEq] at hE1
    obtain ⟨_, _, -, hx, -⟩ := hE1
    rcases hs with hs | ⟨i, hs⟩
    · exact ⟨_, hx, fun _ => rfl, bw_ori _ 16 (.inl rfl)⟩
    · have h4 := four_of hF (by rw [hs]; rfl)
      have h5 := (early_ns hF1 (by rw [hb]; rfl)).1
      omega
  · simp only [Ev, hi, Kind.shfl.injEq] at hE1
    obtain ⟨_, _, -, hx, -⟩ := hE1
    refine ⟨_, hx, fun hb => ?_, bw_shSrc _ _⟩
    have h4 := four_of hF1 (by rw [hi]; rfl)
    have h5 := (early_ns hF (by rw [hb]; rfl)).1
    omega
  · exfalso
    have hd : d.site.msh = true := by rcases hs with hs | ⟨i, hs⟩ <;> rw [hs] <;> rfl
    obtain ⟨hsite, -⟩ := mshfl_same hsC hF1 hse hF hJ hd hn1
    rcases hs with hs | ⟨i, hs⟩ <;> rw [hs] at hsite <;> rw [← hsite] at hse <;>
      simp [Site.epi, Epilogue.Site.shfl] at hse

/-! ### The descriptor words a state records -/

/-- The recorded word of broadcast `k`. -/
def sAt (v : V) : Fin 14 → BitVec 64
  | 0 => v.s0 | 1 => v.s1 | 2 => v.s2 | 3 => v.s3 | 4 => v.s4 | 5 => v.s5 | 6 => v.s6
  | 7 => v.s7 | 8 => v.s8 | 9 => v.s9 | 10 => v.s10 | 11 => v.s11 | 12 => v.s12 | 13 => v.s13

/-- Every recorded broadcast word has the pattern. -/
def SOk (v : V) : Prop := ∀ k, BW (sAt v k)

/-- The sites between a QK block's election that moves the Q descriptors by `-2048` and the next
one, which moves them back. -/
def neg : Site → Bool
  | .qk b _ => b.val % 2 = 0
  | .ce c | .cm c => c.val = 0 ∨ c.val = 3 ∨ c.val = 4
  | .wt k => k.val = 2 ∨ k.val = 6
  | .sh k => k.val = 2 ∨ k.val = 7 ∨ k.val = 8
  | .eq b => b.val % 2 = 1
  | .ep b | .pv b _ | .mw b _ => b.val = 1
  | _ => false

/-- The Q descriptors at a site past the broadcast. -/
def qv (L : Launch) (b : Bool) : Fin 8 → BitVec 64 :=
  if b then fun i => qstep (qinit (qx L) i) (-2048) else qinit (qx L)

/-- The Q descriptors of a state: none before the broadcast, `qv` after. -/
def QOk (L : Launch) (d : D) : Prop := d.site.early = false → d.v.qd = qv L (neg d.site)

theorem sOk_setS {v : V} (h : SOk v) {x : BitVec 64} (hx : BW x) (k : Fin 14) :
    SOk (setS v x k) := by
  intro i
  fin_cases k <;> fin_cases i <;> simp only [setS, sAt] <;>
    first
      | exact hx
      | exact h 0
      | exact h 1
      | exact h 2
      | exact h 3
      | exact h 4
      | exact h 5
      | exact h 6
      | exact h 7
      | exact h 8
      | exact h 9
      | exact h 10
      | exact h 11
      | exact h 12
      | exact h 13

theorem sOk_ps {v : V} (h : SOk v) (n : Nat) : SOk { v with ps := n } := h

/-! ### The Q descriptors' moves -/

theorem toNat_tb32 (y : BitVec 64) : (truncBits 32 y).toNat = y.toNat % 2 ^ 32 := toNat_r32 y

theorem dhi_lt : dhi.toNat < 2 ^ 32 := by
  simp only [dhi, i32, truncBits, BitVec.toNat_ofNat]; omega

theorem toNat_join {lo : BitVec 64} (hlo : lo.toNat < 2 ^ 32) :
    (lo ||| dhi <<< 32).toNat = lo.toNat + dhi.toNat * 2 ^ 32 := by
  have hd := dhi_lt
  have h64 : dhi.toNat * 2 ^ 32 < 2 ^ 64 :=
    calc dhi.toNat * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hd (by positivity)
      _ = 2 ^ 64 := by norm_num
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt h64, ← Nat.shiftLeft_eq,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
  omega

/-- A move of a joined descriptor moves its low word. -/
theorem qstep_join {lo : BitVec 64} (hlo : lo.toNat < 2 ^ 32) (off : Int) :
    qstep (lo ||| dhi <<< 32) off = addi lo off ||| dhi <<< 32 := by
  have hd := dhi_lt
  have hj := toNat_join hlo
  have h1 : truncBits 32 (lo ||| dhi <<< 32) = lo := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_tb32, hj]
    omega
  have h2 : truncBits 32 (BitVec.ofNat 64 ((lo ||| dhi <<< 32).toNat / 2 ^ 32)) = dhi := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_tb32, hj, BitVec.toNat_ofNat]
    omega
  unfold qstep
  rw [h1, h2]

theorem toNat_addi_lt (x : BitVec 64) (n : Int) : (addi x n).toNat < 2 ^ 32 := by
  simp only [addi, truncBits, BitVec.toNat_ofNat]
  omega

theorem addi_back {lo : BitVec 64} (h1 : 2048 ≤ lo.toNat) (h2 : lo.toNat < 2 ^ 32) :
    addi (addi lo (-2048)) 2048 = lo := by
  apply BitVec.eq_of_toNat_eq
  have := iv_addi (iv_addi_neg (show Iv lo.toNat lo.toNat lo from ⟨le_rfl, le_rfl⟩) 2048 h1 h2)
    2048 (by omega)
  unfold Iv at this
  have e : ((2048 : Nat) : Int) = 2048 := rfl
  rw [e] at this
  omega

theorem qx_iv : Iv 65536 81856 (qx L) := by
  have ha : (andi (shru (addi (sbW L) 35840) 4) 16320).toNat ≤ 16320 :=
    (iv_andi (x := shru (addi (sbW L) 35840) 4) 16320 (by decide)).2
  have hi : (i32 65536).toNat = 2 ^ 16 := rfl
  have hr : (r32 (andi (shru (addi (sbW L) 35840) 4) 16320)).toNat =
      (andi (shru (addi (sbW L) 35840) 4) 16320).toNat := by rw [toNat_r32]; omega
  unfold Iv
  simp only [qx, ori, BitVec.toNat_or, hr, hi]
  rw [Nat.or_two_pow_eq_add_of_lt (by omega)]
  omega

theorem qlo_iv (i : Fin 8) : Iv 65536 82886 (qlo (qx L) i) := by
  have hx : Iv 65536 81856 (qx L) := qx_iv
  unfold qlo
  split
  · exact iv_mono le_rfl (by omega) hx
  · have hq : ∃ n : Nat, qoff i = n ∧ n ≤ 1030 := by
      fin_cases i <;> simp [qoff] <;> first | exact ⟨_, rfl, by decide⟩ | omega
    obtain ⟨n, hn, hn'⟩ := hq
    rw [hn]
    exact iv_mono (by omega) (by omega) (iv_addi hx n (by omega))

/-- **The Q descriptors move back**: the second QK block's election undoes the first's move. -/
theorem qv_back (i : Fin 8) : qstep (qv L true i) 2048 = qinit (qx L) i := by
  have hl := qlo_iv (L := L) i
  unfold Iv at hl
  simp only [qv, ↓reduceIte, qinit]
  rw [qstep_join (by omega), qstep_join (toNat_addi_lt _ _), addi_back (by omega) (by omega)]

/-! ### Steps keep the descriptor words -/

/-- A state keeps its descriptor words: its broadcast words have the pattern and, past the
broadcast, its Q descriptors are those of its site. -/
def DOk (L : Launch) (d : D) : Prop := SOk d.v ∧ QOk L d

/-- The successor of a step that changes no descriptor word: same words, same `neg`. -/
theorem dok_of {d d' : D} (h : DOk L d) (hs : sAt d'.v = sAt d.v) (hq : d'.v.qd = d.v.qd)
    (he : d'.site.early = false → d.site.early = false)
    (hn : neg d'.site = neg d.site) : DOk L d' :=
  ⟨fun k => by rw [hs]; exact h.1 k, fun h' => by rw [hq, hn]; exact h.2 (he h')⟩

theorem dok_passStart {d : D} (h : DOk L d) (hn : d.site.early = false → neg d.site = false)
    (hq : d.site.early = true → d.v.qd = qv L false) (late : Bool) :
    DOk L (passStart p L g late d) := by
  refine ⟨fun k => ?_, fun _ => ?_⟩
  · cases late <;> simp only [passStart] <;> split_ifs <;> exact h.1 k
  · have hqd : (passStart p L g late d).v.qd = d.v.qd := by
      cases late <;> simp only [passStart] <;> split_ifs <;> rfl
    have hsn : neg (passStart p L g late d).site = false := by
      cases late <;> simp only [passStart] <;> split_ifs <;> rfl
    rw [hqd, hsn]
    cases he : d.site.early
    · rw [h.2 he, hn he]
    · exact hq he

theorem neg_wtNext : ∀ k, neg (wtNext k) = neg (.wt k) := by decide
theorem neg_shNext : ∀ k, neg (shNext k) = neg (.sh k) := by decide
theorem neg_qkDone : ∀ b, neg (qkDone b) = neg (.qk b 0) := by decide
theorem neg_pvDone : ∀ b, neg (pvDone b) = neg (.pv b 0) := by decide
theorem early_wtNext : ∀ k, (wtNext k).early = false := by decide
theorem early_shNext : ∀ k, (shNext k).early = false := by decide
theorem early_qkDone : ∀ b, (qkDone b).early = false := by decide
theorem early_pvDone : ∀ b, (pvDone b).early = false := by decide

set_option hygiene false in
/-- A commit's successor keeps the descriptor words (one theorem per commit index). -/
macro "dok_ce " n:ident c:num : command => `(
theorem $n {d : D} (h : DOk L d) (hn : neg d.site = neg (.ce $c))
    (he : d.site.early = false) : DOk L (ceNext p L g d $c) := by
  simp only [ceNext]
  first
    | (simp only [enterLoop]; split <;> exact dok_of h rfl rfl (fun _ => he) (by rw [hn]; rfl))
    | (simp only [loopEnd]; split <;> exact dok_of h rfl rfl (fun _ => he) (by rw [hn]; rfl))
    | exact dok_passStart h (fun _ => by rw [hn]; rfl) (fun h' => by rw [he] at h'; cases h')
        true
    | exact dok_of h rfl rfl (fun _ => he) (by rw [hn]; rfl))

dok_ce dok_ce0 0
dok_ce dok_ce1 1
dok_ce dok_ce2 2
dok_ce dok_ce3 3
dok_ce dok_ce4 4
dok_ce dok_ce5 5
dok_ce dok_ce6 6
dok_ce dok_ce7 7
dok_ce dok_ce8 8
dok_ce dok_ce9 9
dok_ce dok_ce10 10
dok_ce dok_ce11 11

theorem dok_ceNext {d : D} (h : DOk L d) (c : Fin 12) (hn : neg d.site = neg (.ce c))
    (he : d.site.early = false) : DOk L (ceNext p L g d c) := by
  fin_cases c
  · exact dok_ce0 h hn he
  · exact dok_ce1 h hn he
  · exact dok_ce2 h hn he
  · exact dok_ce3 h hn he
  · exact dok_ce4 h hn he
  · exact dok_ce5 h hn he
  · exact dok_ce6 h hn he
  · exact dok_ce7 h hn he
  · exact dok_ce8 h hn he
  · exact dok_ce9 h hn he
  · exact dok_ce10 h hn he
  · exact dok_ce11 h hn he

theorem dok_afterTotal {d : D} (h : DOk L d) (he : d.site.early = false)
    (hn : neg d.site = false) (k : Epilogue.Scan) (x : BitVec 64) :
    DOk L (afterTotal p L g k d x) := by
  cases k <;> simp only [afterTotal, scanExit, loopHead] <;> split_ifs <;>
    exact dok_of h rfl rfl (fun _ => he) (by rw [hn]; rfl)

theorem dok_afterTiles {d d' : D} (h : DOk L d) (he : d.site.early = false)
    (hn : neg d.site = false) {x : BitVec 64} (hs : afterTiles p L g d x = some d') :
    DOk L d' := by
  dsimp only [afterTiles] at hs
  split_ifs at hs <;> simp only [Option.some.injEq, reduceCtorEq] at hs <;> subst hs <;>
    exact dok_of h rfl rfl (fun _ => he) (by rw [hn]; rfl)

/-- What a broadcast site receives, as `recv_word` gives it. -/
def RecvOk (L : Launch) (d : D) (e : Event) : Prop :=
  (d.site = .bcast ∨ ∃ i, d.site = .sh i) → ∀ md a b c r o, e.kind = .shfl md a b c r o →
    ∃ x, r = .bits 32 x ∧ (d.site = .bcast → x = qx L) ∧ BW x

set_option maxHeartbeats 16000000 in
/-- **A step keeps the descriptor words.** -/
theorem succ_desc {d d' : D} {e : Event} (h : DOk L d) (hR : RecvOk L d e)
    (hs : succ p L g d e = some (some d')) : DOk L d' := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case bcast =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    rename_i md a b c r o
    obtain ⟨x, rfl, hx, -⟩ := hR (.inl rfl) md a b c r o rfl
    rw [hx rfl] at hs
    simp only [word32, Option.some.injEq] at hs
    subst hs
    exact dok_passStart (d := ⟨.bcast, { v with qd := qinit (qx L) }⟩) ⟨h.1, fun h' => by cases h'⟩
      (fun h' => by cases h') (fun _ => by simp [qv]) false
  case sh k =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    rename_i md a b c r o
    obtain ⟨x, rfl, -, hx⟩ := hR (.inr ⟨k, rfl⟩) md a b c r o rfl
    simp only [word32, Option.some.injEq] at hs
    subst hs
    refine ⟨sOk_ps (sOk_setS h.1 hx k) _, fun he => ?_⟩
    have hq := h.2 rfl
    show (setS v x k).qd = _
    rw [show (setS v x k).qd = v.qd by fin_cases k <;> rfl, hq]
    exact congrArg _ (neg_shNext k).symm
  case eq b =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    rename_i mk inst ld
    simp only [Option.some.injEq] at hs
    subst hs
    have hq := h.2 rfl
    refine ⟨h.1, fun _ => ?_⟩
    simp only at hq ⊢
    rw [hq]
    fin_cases b <;> split <;> funext i <;>
      simp only [neg, qv, qkDone, qkOff, Fin.isValue, Fin.val_zero, Fin.val_one,
        ↓reduceIte] <;> norm_num <;> first | rfl | exact qv_back i
  all_goals try simp only [succ, word32] at hs
  all_goals (repeat' split at hs)
  all_goals first
    | (cases hs; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at hs; subst hs
       first
         | exact dok_ceNext h _ rfl rfl
         | exact dok_afterTotal h rfl rfl _ _
         | (refine dok_of h rfl rfl (fun h' => by first | rfl | simp [Site.early] at h') ?_
            first
              | rfl
              | exact neg_wtNext _
              | exact neg_qkDone _
              | exact neg_pvDone _
              | (split <;> first
                  | rfl
                  | exact neg_qkDone _
                  | exact neg_pvDone _
                  | simp_all [neg])))
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at hs
       obtain ⟨d0, h0, rfl⟩ := hs
       exact dok_afterTiles h rfl rfl h0)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
