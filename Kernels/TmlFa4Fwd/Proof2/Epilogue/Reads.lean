-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Next

public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The output warp's reads return the launch words

The requests the warp reads are requests of the batch (`G_W`, `gxv_W`: the group starts and the
chosen request are words up to the batch), so every read of a state that holds the reference
values is a read of a cumulative query offset (`rdAddr_*`), and it returns the launch word when
the offsets are protected (`expect_read`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {ns nv : Nat}

theorem batch_lt (hp : Pre p L m) : p.batch < 2 ^ 22 := by
  have := hp.shape; omega

theorem batchOf_W (hp : Pre p L m) (late : Bool) : batchOf p late = W p.batch := by
  have := batch_lt hp
  cases late
  · rfl
  · simp only [batchOf, ↓reduceIte, paramW]; exact r32_W (by omega)

theorem laneW_W (L : Launch) (g : Nat) : laneW L g = W (laneOf L g) := by
  have : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  exact r32_W (by omega)

theorem lw_W {ℓ : Nat} (h : ℓ < 32) : lw ℓ = W ℓ := r32_W (by omega)

/-- **The group start of loop round `r ≥ 1`** is `31 (r - 1)` capped at the batch. -/
theorem G_W (hp : Pre p L m) (late : Bool) : ∀ r, 1 ≤ r →
    G p late r = W (min (31 * (r - 1)) p.batch)
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [G, i32_zero]
  | r + 2, _ => by
    have hb := batch_lt hp
    have ih := G_W hp late (r + 1) (by omega)
    simp only [G, ih, batchOf_W hp]
    rw [addi31_W (by omega), min32_W (by omega) (by omega)]
    congr 1
    simp only [Nat.add_sub_cancel]
    omega

/-- The chosen request's group start is a request of the batch. -/
theorem gxv_W (hp : Pre p L m) (c : Nat) (late : Bool) (R : Nat) :
    ∃ x ≤ p.batch, gxv p c late R = W x := by
  have hb := batch_lt hp
  cases R with
  | zero =>
    simp only [gxv]
    split
    · exact ⟨0, by omega, i32_zero⟩
    · rw [G_W hp late 1 le_rfl, batchOf_W hp, addi31_W (by omega),
        min32_W (by omega) (by omega)]
      exact ⟨_, Nat.min_le_right _ _, rfl⟩
  | succ R =>
    simp only [gxv]
    split
    · rw [G_W hp late (R + 1) (by omega), batchOf_W hp, addi31_W (by omega),
        min32_W (by omega) (by omega)]
      exact ⟨_, Nat.min_le_right _ _, rfl⟩
    · rw [G_W hp late (R + 2) (by omega), batchOf_W hp, addi31_W (by omega),
        min32_W (by omega) (by omega)]
      exact ⟨_, Nat.min_le_right _ _, rfl⟩

theorem cuQ_room (hp : Pre p L m) : p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 :=
  hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])

theorem addrU_toNat (hp : Pre p L m) {i : Nat} (hi : i ≤ p.batch) :
    (truncBits 64 (vbits (addrU p.cuQBase (W i))) + BitVec.ofInt 64 0).toNat =
      p.cuQBase + 4 * i := by
  have h := cuQ_room hp
  have hb := batch_lt hp
  have h4 : (i32 4).toNat = 4 := by decide
  simp only [vbits, r32_W (show i < 2 ^ 32 by omega), h4]
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Nat.reducePow]
  omega

theorem addrS_toNat (hp : Pre p L m) {i off : Nat} (hi : i + off / 4 ≤ p.batch) (ho : off ≤ 4) :
    (truncBits 64 (vbits (addrS p.cuQBase (W i))) + BitVec.ofInt 64 off).toNat =
      p.cuQBase + 4 * i + off := by
  have h := cuQ_room hp
  have hb := batch_lt hp
  have hs : toSigned 32 (r32 (W i)) = i := by
    rw [r32_W (by omega)]; exact toSigned_W (by omega)
  have h4 : toSigned 32 (i32 4) = 4 := by decide
  simp only [vbits, hs, h4]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Nat.reducePow]
  omega

/-- The request a lane reads in round `r`. -/
def reqN (p : Params) (r ℓ : Nat) : Nat := if r = 0 then ℓ else min (31 * (r - 1)) p.batch + 31 + ℓ

theorem req_W (hp : Pre p L m) (late : Bool) (r : Nat) {ℓ : Nat} (hℓ : ℓ < 32) :
    req p late r ℓ = W (reqN p r ℓ) := by
  have hb := batch_lt hp
  unfold req reqN
  split
  · exact lw_W hℓ
  · rw [G_W hp late r (by omega), addi31_W (by omega), lw_W hℓ, add32_W (by omega)]

theorem reqN_le (hp : Pre p L m) {late : Bool} {r ℓ : Nat} (hℓ : ℓ < 32)
    (h : reads p late r ℓ = true) : reqN p r ℓ ≤ p.batch := by
  have hb := batch_lt hp
  have hr : reqN p r ℓ < 2 ^ 31 := by unfold reqN; split <;> omega
  simp only [reads, req_W hp late r hℓ, batchOf_W hp,
    scmp_gt_W (b := p.batch) hr (by omega)] at h
  simpa using h

theorem vbits_eq {x y : BitVec 64} (h : x.toNat = y.toNat) : x = y := BitVec.eq_of_toNat_eq h

theorem addrS_toNat0 (hp : Pre p L m) {i : Nat} (hi : i ≤ p.batch) :
    (truncBits 64 (vbits (addrS p.cuQBase (W i))) + BitVec.ofInt 64 0).toNat =
      p.cuQBase + 4 * i := by
  have := addrS_toNat hp (off := 0) (by simpa using hi) (by omega)
  simpa using this

theorem addrS_toNat4 (hp : Pre p L m) {i : Nat} (hi : i + 1 ≤ p.batch) :
    (truncBits 64 (vbits (addrS p.cuQBase (W i))) + BitVec.ofInt 64 4).toNat =
      p.cuQBase + 4 * (i + 1) := by
  have := addrS_toNat hp (off := 4) (by simpa using hi) (by omega)
  simp only [Nat.cast_ofNat] at this
  omega

theorem reqOf_G {late : Bool} {r : Nat} (h0 : r ≠ 0) :
    reqOf L g (G p late r) = req p late r (laneOf L g) := by
  simp [req, h0, reqOf, laneW, lw]

/-- A read of the word of cumulative query offset `i` returns its launch word. -/
theorem read_word (hp : Pre p L m) (hReads : Epilogue.CuQReadsFromLaunch p X) {k i : Nat}
    {bs : List (Option Byte)} {pc : Nat} (hi : i ≤ p.batch)
    (he : X.get (g, k) = some ⟨pc, .rd (wordAcc (p.cuQBase + 4 * i)) bs⟩) :
    rebuild 3 bs = .ok (.bits 32 (qv p (W i))) := by
  have hb : i < 2 ^ 32 := by have := batch_lt hp; omega
  rw [hReads i hi (g, k) bs ⟨pc, he⟩, rebuild_b32]
  simp only [b32, qv, r32_W hb, toNat_W (show i < 2 ^ 64 by omega)]

/-- **The read of a scan round returns the launch word of the lane's request.** -/
theorem expect_word (hp : Pre p L m) (hReads : Epilogue.CuQReadsFromLaunch p X) {k : Nat}
    {k' : Scan} {d : D} {e : Event} (he : X.get (g, k) = some e) (hs : d.site = .word k')
    (hF : Fits p L g d ns nv) (hE : Ev p L g d e) : Expect p L g d ns e := by
  have hb := batch_lt hp
  have hroom := cuQ_room hp
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨pc, kind⟩ := e
  simp only [Ev, hs] at hE
  rcases hE with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [Expect, hs]
  intro r n0 v0 hP hR hns
  simp only [Fits, hs] at hF
  obtain ⟨r', n0', v0', hP', hR', hns', -, hL, hrd⟩ := hF
  obtain ⟨rfl, -⟩ := hP.unique hP'
  obtain rfl : r = r' := by omega
  have hidx := reqN_le hp hl hrd
  have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * reqN p r (laneOf L g) := by
    cases k' with
    | first | second =>
      have h0 : r = 0 := by have := hR.2; simp_all
      subst h0
      simp only [rdAddr, hs, laneW_W]
      rw [addrU_toNat hp (by simpa [reqN] using hidx)]
      simp [reqN]
    | loop | loop2 =>
      have h0 : r ≠ 0 := by have := hR.2; simp_all
      obtain ⟨hg, -⟩ := hL h0
      have hq : reqOf L g d.grp = W (reqN p r (laneOf L g)) := by
        rw [hg, reqOf_G h0, req_W hp _ r hl]
      simp only [rdAddr, hs, hq]
      exact addrS_toNat0 hp hidx
  rw [haddr] at he
  rw [req_W hp _ r hl]
  exact read_word hp hReads hidx he

/-- The chosen request and the next are requests of the batch. -/
theorem chosen_W (hp : Pre p L m) {R : Nat} {bal : BitVec 64} {d : D}
    (hC : ChosenVals p L g R bal d ns nv) : ∃ i, chosen d = W i ∧ i + 1 ≤ p.batch := by
  have hb := batch_lt hp
  obtain ⟨hPk, -, hgx, -, hbal, -⟩ := hC
  obtain ⟨x, hx, hxe⟩ := gxv_W hp (g / L.block) false R
  obtain ⟨c, hc, hce⟩ := popc_W bal
  have hch : chosen d = W (c + x) := by
    simp only [chosen, hgx, hbal, hxe, hce]
    exact add32_W (by omega)
  refine ⟨c + x, hch, ?_⟩
  have hlt := hPk.2.2.2
  simp only [chosen, chosenD, hxe, hce, add32_W (show c + x < 2 ^ 32 by omega)] at hlt
  rw [show paramW p.batch = W p.batch from r32_W (by omega), scmp_lt_W (by omega) (by omega)]
    at hlt
  simpa using hlt

/-- **The chosen request's two reads return its two launch words.** -/
theorem expect_q (hp : Pre p L m) (hReads : Epilogue.CuQReadsFromLaunch p X) {k : Nat}
    {d : D} {e : Event} (he : X.get (g, k) = some e) (hs : d.site = .q0 ∨ d.site = .q1)
    (hF : Fits p L g d ns nv) (hE : Ev p L g d e) : Expect p L g d ns e := by
  have hb := batch_lt hp
  have hroom := cuQ_room hp
  obtain ⟨R, bal, hC⟩ : ∃ R bal, ChosenVals p L g R bal d ns nv := by
    rcases hs with hs | hs <;> simp only [Fits, hs] at hF
    · exact hF
    · obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩
  obtain ⟨i, hi, hib⟩ := chosen_W hp hC
  obtain ⟨pc, kind⟩ := e
  rcases hs with hs | hs <;> simp only [Ev, hs] at hE <;>
    rcases hE with ⟨bs, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> simp only [Expect, hs]
  · have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * i := by
      simp only [rdAddr, hs, hi]
      exact addrS_toNat0 hp (by omega)
    rw [haddr] at he
    rw [hi]
    exact read_word hp hReads (by omega) he
  · have haddr : (rdAddr p L g d).toNat = p.cuQBase + 4 * (i + 1) := by
      simp only [rdAddr, hs, hi]
      exact addrS_toNat4 hp hib
    rw [haddr] at he
    rw [hi, addi1_W (by omega)]
    exact read_word hp hReads hib he

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
