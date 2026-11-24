-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Fact
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The words the MMA warp's broadcasts deliver, as values

`recv_exact`: a lane at a pipeline broadcast receives the word of that broadcast at its own state
(`shSrc`): the source lane is at the same broadcast of the same round (`sh_same`), where the ring
slot is the round's. `words`: a state holds, for each broadcast whose word the code still reads
(`kn`), that word. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The broadcast's place gives the number of broadcasts before it. -/
def shPs (k : Fin 14) (r : Nat) : Nat :=
  if k.val < 3 then k.val else if k.val < 9 then 6 * r + k.val else 6 * r + k.val - 6

theorem shAt_sh (k : Fin 14) (r : Nat) (h : k.val < 3 → r = 0) :
    shAt (Site.sh k).ord r = shPs k r := by
  fin_cases k <;> simp [Site.ord, shAt, pq, shPs] at h ⊢ <;> omega

/-- What the count conjuncts say at a broadcast. -/
theorem sh_refQ {k : Fin 14} {v : V} {cn : Cnt → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g (Site.sh k).ord v cn r w) :
    v.ps = shPs k r ∧ (k.val < 3 → r = 0) ∧ (3 ≤ k.val ∧ k.val < 9 → (r : Int) + 1 < Bs p L g v) ∧
      (9 ≤ k.val → (r : Int) + 1 = Bs p L g v ∨ (r = 0 ∧ Bs p L g v < 2)) ∧
      (3 ≤ k.val → LoopRegs v r) := by
  have ho : (k.val < 3 ↔ (Site.sh k).ord < 20) ∧
      (3 ≤ k.val ∧ k.val < 9 ↔ 20 ≤ (Site.sh k).ord ∧ (Site.sh k).ord < 60) ∧
      (9 ≤ k.val ↔ 60 ≤ (Site.sh k).ord) ∧ (Site.sh k).ord < 100 := by
    clear hQ; revert k; decide
  obtain ⟨o1, o2, o3, o4⟩ := ho
  have h1 : k.val < 3 → r = 0 := fun h => hQ.pre (o1.mp h)
  refine ⟨by rw [hQ.ps, shAt_sh k r h1], h1, fun h => (hQ.loop (o2.mp h)).1,
    fun h => hQ.tail ⟨o3.mp h, o4⟩, fun h => hQ.regs ⟨?_, o4⟩⟩
  by_contra hlt
  have := o1.mpr (by omega)
  omega

theorem shSrc_eq {k : Fin 14} {v v' : V} (h : 3 ≤ k.val → v.slot = v'.slot) :
    shSrc L v k = shSrc L v' k :=
  match k, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, h => by
    show slotDesc L v.slot 67108864 = slotDesc L v'.slot 67108864
    unfold slotDesc
    rw [h (by decide)]
  | 5, _ => rfl
  | 6, h => by
    show slotDesc L (slot1 v) 65536 = slotDesc L (slot1 v') 65536
    unfold slot1
    rw [h (by decide)]
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, h => by
    show slotDesc L v.slot 67108864 = slotDesc L v'.slot 67108864
    unfold slotDesc
    rw [h (by decide)]
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl

/-- **Two lanes of one CTA at pipeline broadcasts with one shuffle count** are at the same
broadcast of the same round. -/
theorem sh_same {h : Nat} {d d' : D} {k k' : Fin 14} {ns ns' nv nv' : Nat} {cn cn' : Cnt → Nat}
    (hc : g / L.block = h / L.block) (hk : d.site = .sh k) (hk' : d'.site = .sh k')
    (hF : MFits p L g d ns nv) (hJ : RefCounts p L g (d, cn)) (hF' : MFits p L h d' ns' nv')
    (hJ' : RefCounts p L h (d', cn')) (hn : ns = ns') :
    k' = k ∧ shSrc L d'.v k = shSrc L d.v k := by
  obtain ⟨R, bal, hPk, h1, -, -⟩ := sh_band hk hF hJ
  obtain ⟨R', bal', hPk', h1', -, -⟩ := sh_band hk' hF' hJ'
  obtain ⟨rfl, rfl, -⟩ := picked_cta hc hPk hPk'
  have hps : d.v.ps = d'.v.ps := by omega
  obtain ⟨r, w, hQ, -⟩ := hJ
  obtain ⟨r', w', hQ', -⟩ := hJ'
  simp only at hQ hQ'
  rw [hk] at hQ
  rw [hk'] at hQ'
  have hB : Bs p L g d.v = Bs p L h d'.v := by
    obtain ⟨R1, b1, hC1, e1⟩ := bs_ref (pmid_of (by rw [hk]; rfl)) hF
    obtain ⟨R2, b2, hC2, e2⟩ := bs_ref (pmid_of (by rw [hk']; rfl)) hF'
    obtain ⟨rfl, rfl, -⟩ := picked_cta hc hC1.1 hC2.1
    rw [e1, e2]
    unfold refV Bs blocks coords Epilogue.ctaW
    rw [hc]
  obtain ⟨p1, a1, l1, t1, g1⟩ := sh_refQ hQ
  obtain ⟨p2, a2, l2, t2, g2⟩ := sh_refQ hQ'
  clear hQ hQ' hF hF' hPk hPk' h1 h1' hn
  have hkr : k' = k ∧ r' = r := by
    rw [← hB] at l2 t2
    have hv : k'.val = k.val ∧ r' = r := by
      clear g1 g2 hB
      have := k.isLt
      have := k'.isLt
      rw [hps] at p1
      rw [p1] at p2
      unfold shPs at p2
      generalize k.val = x at *
      generalize k'.val = y at *
      generalize Bs p L g d.v = B at *
      split_ifs at p2 <;> omega
    exact ⟨Fin.ext hv.1, hv.2⟩
  obtain ⟨rfl, rfl⟩ := hkr
  refine ⟨rfl, shSrc_eq fun h => ?_⟩
  rw [(g1 h).1, (g2 h).1]

/-- **A pipeline broadcast delivers its own word.** -/
theorem recv_exact (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {a recv : Value}
    {b c : Nat} {mode : ShflMode} {ok : Bool} {d : D} {n : Cls → Nat} {i : Fin 14}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hJ : RefCounts p L g (d, rc n)) (hF : MFits p L g d (n .shfl) (n .vote))
    (IH : GoodUpTo p L X (n .shfl + n .vote)) (hs : d.site = .sh i) :
    recv = .bits 32 (shSrc L d.v i) := by
  have hev := (mfired hp hX he hσ).1
  have hmode : mode = .idx ∧ b = 0 ∧ c = 31 := by
    simp only [Ev, hs, Kind.shfl.injEq] at hev
    obtain ⟨_, _, h1, -, h2, h3, -⟩ := hev
    exact ⟨h1, h2, h3⟩
  obtain ⟨rfl, rfl, rfl⟩ := hmode
  have hsl := Step.shflSource_lt .idx (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hsT, hsW, hsC, -, -⟩ := lane_facts hp hg hw hsl
  obtain ⟨j, pc', b', c', r', o', hj, hG, hcj⟩ := mshfl_src hp hX hg hw he hσ hJ hF IH
  have h3 := mfits_three hF
  obtain ⟨d1, n1, -, hJ1, hF1, hE1, hs1, -⟩ :=
    role_at hp hX hj hG (.inr (.inr ⟨rfl, by omega⟩))
  have hn1 : n1 .shfl = n .shfl := by omega
  rcases msh_cases ((mev_coll hE1).1 rfl) with hb | ⟨i', hi⟩ | hse
  · have h4 := four_of hF (by rw [hs]; rfl)
    have h5 := (early_ns hF1 (by rw [hb]; rfl)).1
    omega
  · simp only [Ev, hi, Kind.shfl.injEq] at hE1
    obtain ⟨_, _, -, hx, -⟩ := hE1
    obtain ⟨rfl, hsr⟩ := sh_same hsC.symm hs hi hF hJ hF1 hJ1 hn1.symm
    rw [hx, hsr]
  · exfalso
    have hd : d.site.msh = true := by rw [hs]; rfl
    obtain ⟨hsite, -⟩ := mshfl_same hsC hF1 hse hF hJ hd hn1
    rw [hs] at hsite
    rw [← hsite] at hse
    simp [Site.epi, Epilogue.Site.shfl] at hse

/-! ### The recorded words -/

/-- The places at which the code still reads the word of broadcast `k`. -/
def kn (s : Site) (k : Fin 14) : Bool :=
  decide ([4, 5, 11, 23, 24, 25, 31, 37, 38, 67, 68, 69, 75, 76].getD k.val 0 ≤ s.ord) &&
    decide (s.ord ≤ [16, 99, 99, 29, 41, 29, 46, 42, 42, 72, 79, 72, 79, 79].getD k.val 0)

/-- A state holds the words of the broadcasts its code still reads. -/
def WOk (L : Launch) (d : D) : Prop := ∀ k, kn d.site k = true → sAt d.v k = shSrc L d.v k

theorem wok_of {d d' : D} (h : WOk L d) (hk : ∀ k, kn d'.site k = true → kn d.site k = true)
    (hs : sAt d'.v = sAt d.v) (hv : d'.v.slot = d.v.slot) : WOk L d' := fun k hk' => by
  rw [hs, h k (hk k hk')]
  exact (shSrc_eq fun _ => hv).symm

theorem kn_late {s : Site} (h : s.ord = 0 ∨ s.ord = 100) (k : Fin 14) : kn s k = false := by
  unfold kn
  rcases h with h | h <;> rw [h] <;> revert k <;> decide

theorem wok_late {d : D} (h : d.site.ord = 0 ∨ d.site.ord = 100) : WOk L d := fun k hk => by
  rw [kn_late h k] at hk; cases hk

theorem kn_wt0 : ∀ k, kn (.wt 0) k = false := by decide
theorem kn_wtNext : ∀ k i, kn (wtNext k) i = true → kn (.wt k) i = true := by decide
theorem kn_shNext : ∀ k i, kn (shNext k) i = true → i = k ∨ kn (.sh k) i = true := by decide
theorem kn_eq : ∀ b i, (kn (.qk b 0) i = true → kn (.eq b) i = true) ∧
    (kn (qkDone b) i = true → kn (.eq b) i = true) := by decide
theorem kn_qk : ∀ b i, kn (qkDone b) i = true → kn (.qk b 7) i = true := by decide
theorem kn_ep : ∀ b i, (kn (.pv b 0) i = true → kn (.ep b) i = true) ∧
    (kn (.mw b false) i = true → kn (.ep b) i = true) := by decide
theorem kn_pv : ∀ b j i, kn (if j.val = 5 then .mw b true else if j.val = 7 then pvDone b
    else .pv b (j + 1)) i = true → kn (.pv b j) i = true := by decide
theorem kn_mw : ∀ b ld i, kn (if ld then .pv b 6 else pvDone b) i = true →
    kn (.mw b ld) i = true := by decide
theorem kn_cm : ∀ c i, kn (.cm c) i = true → kn (.ce c) i = true := by decide
/-- The site after commit `c`, except at the loop's ends and the second pass. -/
def ceNx : Fin 12 → Site
  | 0 => .wt 2 | 1 => .ce 2 | 3 => .wt 6 | 4 => .eq 3 | 5 => .ce 6 | 7 => .ce 8 | 8 => .wt 7
  | 9 => .ce 10 | 10 => .ce 11 | _ => .bar1

theorem kn_ce : ∀ c i, kn (ceNx c) i = true → kn (.ce c) i = true ∧ kn (.cm c) i = true := by
  decide

theorem ceNext_nx (d : D) : ∀ c : Fin 12, c.val ≠ 2 → c.val ≠ 6 → c.val ≠ 11 →
    ceNext p L g d c = { d with site := ceNx c }
  | 0, _, _, _ | 1, _, _, _ | 3, _, _, _ | 4, _, _, _ | 5, _, _, _ | 7, _, _, _ | 8, _, _, _
  | 9, _, _, _ | 10, _, _, _ => rfl
  | 2, h, _, _ => absurd rfl h
  | 6, _, h, _ => absurd rfl h
  | 11, _, _, h => absurd rfl h

theorem sAt_setS (v : V) (x : BitVec 64) (k i : Fin 14) :
    sAt (setS v x k) i = if i = k then x else sAt v i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem kn_loop : ∀ k : Fin 14, kn (.wt 3) k = true ∨ kn (.ce 7) k = true → k = 1 ∨ k = 2 := by
  decide
theorem kn_loop' : ∀ c : Fin 12, c.val = 2 ∨ c.val = 6 → ∀ k : Fin 14, k = 1 ∨ k = 2 →
    kn (.ce c) k = true ∧ kn (.cm c) k = true := by decide

/-- Entering the loop, or a new round: the slot changes, and only constant words stay. -/
theorem wok_loop {d d' : D} (h : WOk L d) {c : Fin 12} (hc : c.val = 2 ∨ c.val = 6)
    (hd : d.site = .ce c ∨ d.site = .cm c) (hd' : d'.site = .wt 3 ∨ d'.site = .ce 7)
    (hs : sAt d'.v = sAt d.v) : WOk L d' := fun k hk => by
  have hk12 := kn_loop k (by rcases hd' with e | e <;> rw [e] at hk <;> simp [hk])
  have h1 := kn_loop' c hc k hk12
  have h2 := h k (by rcases hd with e | e <;> rw [e] <;> simp [h1])
  rw [hs, h2]
  rcases hk12 with rfl | rfl <;> rfl

theorem ord_passStart (late : Bool) (d : D) :
    (passStart p L g late d).site.ord = 0 ∨ (passStart p L g late d).site.ord = 100 := by
  cases late <;> simp only [passStart] <;> split_ifs <;> simp [Site.ord, Epilogue.Scan.late]

theorem wok_ceNext {d : D} (h : WOk L d) (c : Fin 12)
    (hd : d.site = .ce c ∨ d.site = .cm c) : WOk L (ceNext p L g d c) := by
  by_cases h2 : c.val = 2
  · obtain rfl : c = 2 := Fin.ext h2
    simp only [ceNext, enterLoop]
    split
    · exact wok_loop h (.inl rfl) hd (.inr rfl) rfl
    · exact wok_loop h (.inl rfl) hd (.inl rfl) rfl
  by_cases h6 : c.val = 6
  · obtain rfl : c = 6 := Fin.ext h6
    simp only [ceNext, loopEnd]
    split
    · exact wok_loop h (.inr rfl) hd (.inl rfl) rfl
    · exact wok_loop h (.inr rfl) hd (.inr rfl) rfl
  by_cases h11 : c.val = 11
  · obtain rfl : c = 11 := Fin.ext h11
    exact wok_late (ord_passStart true d)
  · rw [ceNext_nx d c h2 h6 h11]
    refine wok_of h (fun k hk' => ?_) rfl rfl
    rcases hd with e | e <;> rw [e]
    · exact (kn_ce c k hk').1
    · exact (kn_ce c k hk').2

theorem ord_afterTotal (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    (afterTotal p L g k d x).site.ord = 0 ∨ (afterTotal p L g k d x).site.ord = 100 := by
  cases k <;> simp only [afterTotal, scanExit, loopHead] <;> split_ifs <;>
    simp [Site.ord, Epilogue.Scan.late, Epilogue.loopOf]

set_option maxHeartbeats 16000000 in
/-- **A step keeps the recorded words.** -/
theorem succ_words {d d' : D} {e : Event} (h : WOk L d)
    (hR : ∀ i, d.site = .sh i → ∀ md a b c r o, e.kind = .shfl md a b c r o →
      r = .bits 32 (shSrc L d.v i))
    (hs : succ p L g d e = some (some d')) : WOk L d' := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case sh k =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    rename_i md a b c r o
    obtain rfl := hR k rfl md a b c r o rfl
    simp only [word32, Option.some.injEq] at hs
    subst hs
    intro i hi
    have hsl : shSrc L { setS v (shSrc L v k) k with ps := v.ps + 1 } i = shSrc L v i :=
      shSrc_eq fun _ => (setS_same (p := p) (L := L) (g := g) v _ k).1
    show sAt (setS v (shSrc L v k) k) i = _
    rw [hsl, sAt_setS]
    split
    · rename_i he; rw [he]
    · rename_i he
      exact h i ((kn_shNext k i hi).resolve_left he)
  case wt k =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    split
    · exact wok_of h (kn_wtNext k) rfl rfl
    · exact h
  case eq b =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    refine wok_of h (fun i hi => ?_) rfl rfl
    simp only at hi
    split at hi
    · exact (kn_eq b i).1 hi
    · exact (kn_eq b i).2 hi
  case qk b j =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    refine wok_of h (fun i hi => ?_) rfl rfl
    simp only at hi
    split at hi
    · exact kn_qk b i hi
    · exact hi
  case ep b =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    refine wok_of h (fun i hi => ?_) rfl rfl
    simp only at hi
    split at hi
    · exact (kn_ep b i).1 hi
    · exact (kn_ep b i).2 hi
  case pv b j =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact wok_of h (kn_pv b j) rfl rfl
  case mw b ld =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    split
    · exact wok_of h (kn_mw b ld) rfl rfl
    · exact h
  case ce c =>
    simp only [succ] at hs
    cases kind <;> simp only [reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    split
    · exact wok_of h (kn_cm c) rfl rfl
    · exact wok_ceNext h c (.inl rfl)
  case cm c =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact wok_ceNext h c (.inr rfl)
  case uk =>
    simp only [succ, word32] at hs
    (repeat' split at hs) <;> simp only [Option.some.injEq, reduceCtorEq] at hs
    subst hs
    exact fun k hk => absurd hk (by rw [kn_wt0 k]; decide)
  all_goals try simp only [succ, word32] at hs
  all_goals (repeat' split at hs)
  all_goals first
    | (cases hs; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at hs; subst hs
       first
         | exact wok_late (ord_passStart _ _)
         | exact wok_late (ord_afterTotal _ _ _)
         | (refine wok_late ?_; simp [Site.ord, Epilogue.Scan.late]; try (split <;> simp); done))
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at hs
       obtain ⟨d0, h0, rfl⟩ := hs
       refine wok_late (.inl ?_)
       dsimp only [afterTiles] at h0
       split_ifs at h0 <;> simp only [Option.some.injEq, reduceCtorEq] at h0 <;> subst h0 <;> rfl)

/-- **Every state of a lane of warp 12 holds the words of its broadcasts.** -/
theorem words (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) {k : Nat} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n))) : WOk L d := by
  refine fact_at hp hX hg h12 (I := WOk L) (wok_late (.inl rfl)) ?_ k d n hσ
  intro k d n e d' he hσ hRC hMF IH hs hI
  refine succ_words hI (fun i hsi md a b c r o hk => ?_) hs
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  exact recv_exact hp hX hg h12 he hσ hRC hMF IH hsi

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
