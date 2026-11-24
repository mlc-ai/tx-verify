-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5WPair
public import Kernels.InklingRelDecode.Proof.Thread.Lk5VBfly

@[expose] public section

/-!
# The scratch word a warp stores is one number (`storeWordB`)

Before the scratch store, each lane takes the minimum of `alpha` over the lanes of its warp by four
butterfly exchanges (offsets 8, 4, 2, 1: `shfl7` to `shfl10`). Level `k` (`lv k`: `shfl7` …
`store10`) holds the word `lval k` (`alpha`, `cm1` … `cm4`). `Lev c i k`: two lanes of a warp
whose positions differ by a mask that `lmask k` divides hold the same word at level `k` of
iteration `i`, and it reads as a number that is not `+inf`:

* level 0: the lane itself (`al_same`: one state at the exchange of the row maximum of the
  iteration) or its partner `^ 16` (`al_pair`);
* level `k + 1`: the lane's word is the minimum of its and its source lane's words of level `k`
  (`bf_next`, the source by the count of shuffles: `sm_shfl_peer_d`); a mask with the offset's bit
  swaps the two, and the minimum is symmetric.

At level 4 every two lanes of the warp agree: `storeWordB`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Lanes -/

theorem xor_low : ∀ T < 256, ∀ m < 32, T ^^^ m = T - T % 32 + ((T % 32) ^^^ m) := by
  decide

/-- The position of the source lane of a butterfly exchange with offset `o < 32`. -/
theorem src_mod_o (hb : L.block = 256) (y : Nat) {o : Nat} (ho : o < 32) :
    shflSrc L y .bfly o 31 % L.block = (y % L.block) ^^^ o := by
  have hl : laneOf L y < 32 := Nat.mod_lt _ (by decide)
  unfold shflSrc
  rw [shflSource_bfly hl ho]
  simp only []
  have hx : (y % 256 % 32 ^^^ o) < 32 := by
    have := Nat.xor_lt_two_pow (n := 5) (x := y % 256 % 32) (y := o) (by omega) (by omega)
    simpa using this
  have h1 : (y - laneOf L y + (laneOf L y ^^^ o)) % L.block =
      y % L.block - laneOf L y + (laneOf L y ^^^ o) := by
    unfold laneOf
    rw [hb]
    omega
  rw [h1, xor_low (y % L.block) (by rw [hb]; omega) o ho]
  unfold laneOf
  rfl

/-- Two threads of a CTA at one position are one thread. -/
theorem thread_eq {y y' : Nat} (hc : y / L.block = y' / L.block)
    (hm : y % L.block = y' % L.block) : y = y' := by
  have e1 := Nat.div_add_mod y L.block
  have e2 := Nat.div_add_mod y' L.block
  rw [hc, hm] at e1
  omega

theorem xor_swap (a m o : Nat) : (a ^^^ m) ^^^ o = (a ^^^ o) ^^^ m := by
  rw [Nat.xor_assoc, Nat.xor_comm m o, ← Nat.xor_assoc]

theorem xor_swap' (a m o : Nat) : a ^^^ m = (a ^^^ o) ^^^ (m ^^^ o) := by
  rw [Nat.xor_assoc, Nat.xor_comm m o, ← Nat.xor_assoc o o m, Nat.xor_self, Nat.zero_xor]

/-! ### The levels -/

/-- The site of level `k`. -/
def lv : Nat → Site
  | 0 => .shfl7
  | 1 => .shfl8
  | 2 => .shfl9
  | 3 => .shfl10
  | _ => .store10

/-- The word of level `k`. -/
def lval : Nat → Sm.D → Value
  | 0, d => d.stg.al
  | 1, d => d.stg.cm1
  | 2, d => d.stg.cm2
  | 3, d => d.stg.cm3
  | _, d => d.stg.cm4

/-- The offset of the exchange at level `k`. -/
def loff : Nat → Nat
  | 0 => 8
  | 1 => 4
  | 2 => 2
  | _ => 1

/-- The masks at level `k` are the multiples of `lmask k`. -/
def lmask : Nat → Nat
  | 0 => 16
  | 1 => 8
  | 2 => 4
  | 3 => 2
  | _ => 1

theorem mask_split {k : Nat} (hk : k < 4) : ∀ m < 32, m % lmask (k + 1) = 0 →
    m % lmask k = 0 ∨ ((m ^^^ loff k) % lmask k = 0 ∧ m ^^^ loff k < 32) := by
  interval_cases k <;> decide

theorem shape_lv {k : Nat} (hk : k < 4) : ShflShape L (lv k) (lval k) (loff k) := by
  intro g d e u hF hs
  interval_cases k
  · exact Sm.shape_shfl7 hF hs
  · exact Sm.shape_shfl8 hF hs
  · exact Sm.shape_shfl9 hF hs
  · exact Sm.shape_shfl10 hF hs

theorem bfNext_lv {k : Nat} (hk : k < 4) {s : Site} (hs : bfSite s = true)
    (hn : bfNext s = lv (k + 1)) : s = lv k := by
  interval_cases k <;> cases s <;> simp_all [bfSite, bfNext, lv]

theorem bfOp_lv {k : Nat} (hk : k < 4) (d : Sm.D) : bfOp (lv k) d = lval k d := by
  interval_cases k <;> rfl

theorem bfRes_lv {k : Nat} (hk : k < 4) (d : Sm.D) : bfRes (lv k) d = lval (k + 1) d := by
  interval_cases k <;> rfl

theorem lv_ne_setMaxReg (k : Nat) : lv k ≠ .setMaxReg := by
  unfold lv; split <;> simp

/-- **Level `k` of iteration `i` in CTA `c`.** -/
def Lev (Q : Params) (L : Launch) (X : Execution) (c i k : Nat) : Prop :=
  ∀ {y y' kk kk' m : Nat} {d d' : Sm.D}, y < L.threads → y' < L.threads → y / L.block = c →
    y' / L.block = c → m < 32 → m % lmask k = 0 → y' % L.block = (y % L.block) ^^^ m →
    St Q L X y kk = some (some (.d (.sm d))) → St Q L X y' kk' = some (some (.d (.sm d'))) →
    d.site = lv k → d'.site = lv k → d.i = i → d'.i = i → kk ≤ (X.tr y).length →
    kk' ≤ (X.tr y').length →
    (k = 0 → (∃ e, X.get (y, kk) = some e) ∧ ∃ e', X.get (y', kk') = some e') →
    lval k d = lval k d' ∧ ∃ x : EReal, x ≠ ⊤ ∧ ReadsAs (lval k d) x ∧
      (k ≠ 0 → lval k d = erealValue .f32 x)

/-- **`alpha` of one thread at two states of one iteration** between the stage's second exchange
and the update. -/
theorem al_same (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k j : Nat} {d d' : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hj : j ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hσ' : St Q L X g j = some (some (.d (.sm d')))) (hl : Late d.site = true)
    (hq : PostU d.site = false) (hl' : Late d'.site = true) (hq' : PostU d'.site = false)
    (hi : d'.i = d.i) : d'.stg.al = d.stg.al := by
  obtain ⟨k0, d0, r, o, -, h1, h2, h3, h4, -, -, h6, -⟩ := (wInv hX hf hg k hk hσ).2.2.1 hl hq
  obtain ⟨j0, d1, r1, o1, -, h1', h2', h3', h4', -, -, h6', -⟩ :=
    (wInv hX hf hg j hj hσ').2.2.1 hl' hq'
  have hu : j0 = k0 := sm_shfl_unique hpre hX hf hg h4' (event_le h4) h1' h1 (by rw [h2']; rfl)
    (h2.trans h2'.symm) (h3.trans (hi.symm.trans h3'.symm))
  subst hu
  have hd : d1 = d0 := by
    have := h1'.symm.trans h1
    simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at this
    exact this
  subst hd
  have hr : r1 = r := by
    have := h4'.symm.trans h4
    simp only [Option.some.injEq, Event.mk.injEq, Kind.shfl.injEq] at this
    exact this.2.2.2.2.2.1
  rw [h6, h6', hr]

theorem lev0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) (c i : Nat) : Lev Q L X c i 0 := by
  intro y y' kk kk' m d d' hy hy' hc hc' hm hmk hp hσ hσ' hs hs' hi hi' hk hk' hev
  obtain ⟨⟨e, he⟩, ⟨e', he'⟩⟩ := hev rfl
  have hl : Late d.site = true := by rw [hs]; rfl
  have hq : PostU d.site = false := by rw [hs]; rfl
  have hl' : Late d'.site = true := by rw [hs']; rfl
  have hq' : PostU d'.site = false := by rw [hs']; rfl
  have hI : Sm.Inv L y d := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  refine ⟨?_, (d.stg.alr : EReal), EReal.coe_ne_top _, hI.four.al,
    fun h => absurd rfl h⟩
  simp only [lmask] at hmk
  rcases (show m = 0 ∨ m = 16 by omega) with rfl | rfl
  · have hyy : y = y' := thread_eq (hc.trans hc'.symm) (by rw [hp]; simp)
    subst hyy
    exact (al_same hpre hX hf hy hk hk' hσ hσ' hl hq hl' hq' (hi'.trans hi.symm)).symm
  · exact (al_pair hpre hX hf hz hy hy' (hc.trans hc'.symm) hp hk hk' hσ hσ' hl hq hl' hq'
      (hi'.trans hi.symm)).1.symm

/-- The predecessor of a state at level `k + 1`: the state at level `k` with its exchange and the
source lane's state. -/
theorem lev_pred (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} (hk4 : k < 4) {y kk : Nat} {d : Sm.D}
    (hy : y < L.threads) (hσ : St Q L X y kk = some (some (.d (.sm d))))
    (hs : d.site = lv (k + 1)) (hk : kk ≤ (X.tr y).length) :
    ∃ (p j : Nat) (dp d2 : Sm.D) (ep e2 : Event),
      X.get (y, p) = some ep ∧ St Q L X y p = some (some (.d (.sm dp))) ∧ p ≤ (X.tr y).length ∧
      dp.site = lv k ∧ dp.i = d.i ∧
      X.get (shflSrc L y .bfly (loff k) 31, j) = some e2 ∧
      St Q L X (shflSrc L y .bfly (loff k) 31) j = some (some (.d (.sm d2))) ∧
      j ≤ (X.tr (shflSrc L y .bfly (loff k) 31)).length ∧
      SameWarp L y (shflSrc L y .bfly (loff k) 31) ∧
      d2.site = lv k ∧ d2.i = d.i ∧
      minE [lval k dp, lval k d2] = .ok (lval (k + 1) d) := by
  have hb : L.block = 256 := hpre.block
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨p, dp, ep, rfl, hep, hσp, hn⟩
  · exact absurd hs.symm (by simp only [SmEntry.d0]; exact (lv_ne_setMaxReg _).symm ∘ Eq.symm)
  have hbs : bfSite dp.site = true ∧ d.site = bfNext dp.site := by
    refine bf_prev hn ?_
    rw [hs]
    interval_cases k <;> simp [lv]
  have hdp : dp.site = lv k := bfNext_lv hk4 hbs.1 (hbs.2.symm.trans hs)
  obtain ⟨-, hi, md, a, b, c, r, o, hkind, hmin⟩ := bf_next hn hbs.1
  have hep' : X.get (y, p) = some ep := hep
  obtain ⟨recv, ok, x, j, d2, he, hw, hx, hσ2, hs2, hi2, hrecv, -, hj, r2, o2, he2⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := lval k) (k := loff k)
      (by rw [hdp]; exact shape_lv hk4) hy hep' hσp
  subst hx
  have hr : r = recv := by
    rw [he] at hkind
    simp only [Kind.shfl.injEq] at hkind
    exact hkind.2.2.2.2.1.symm
  rw [hdp, bfOp_lv hk4, bfRes_lv hk4, hr, hrecv] at hmin
  refine ⟨p, j, dp, d2, ep, _, hep', hσp, by omega, hdp, hi.symm, he2, hσ2, hj, hw,
    hs2.trans hdp, hi2.trans hi.symm, ?_⟩
  exact hmin

/-- **Level `k + 1` from level `k`.** -/
theorem lev_step (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c i k : Nat} (hk4 : k < 4) (H : Lev Q L X c i k) :
    Lev Q L X c i (k + 1) := by
  have hb : L.block = 256 := hpre.block
  intro y y' kk kk' m d d' hy hy' hc hc' hm hmk hp hσ hσ' hs hs' hi hi' hk hk' _
  obtain ⟨p, j, dp, d2, ep, e2, hep, hσp, hpk, hdp, hip, he2, hσ2, hj, hw, hs2, hi2, hmin⟩ :=
    lev_pred hpre hX hf hk4 hy hσ hs hk
  obtain ⟨p', j', dp', d2', ep', e2', hep', hσp', hpk', hdp', hip', he2', hσ2', hj', hw', hs2',
    hi2', hmin'⟩ := lev_pred hpre hX hf hk4 hy' hσ' hs' hk'
  have hoff : loff k < 32 := by interval_cases k <;> decide
  set x := shflSrc L y .bfly (loff k) 31 with hxdef
  set x' := shflSrc L y' .bfly (loff k) 31 with hx'def
  have hxm : x % L.block = (y % L.block) ^^^ loff k := src_mod_o hb y hoff
  have hxm' : x' % L.block = (y' % L.block) ^^^ loff k := src_mod_o hb y' hoff
  have hxc : x / L.block = c := hw.1.2.2.symm.trans hc
  have hxc' : x' / L.block = c := hw'.1.2.2.symm.trans hc'
  have hx : x < L.threads := hw.1.2.1
  have hx' : x' < L.threads := hw'.1.2.1
  have ev : ∀ {z q : Nat} {f : Event}, X.get (z, q) = some f →
      (k = 0 → (∃ e, X.get (z, q) = some e) ∧ ∃ e', X.get (z, q) = some e') := fun h _ =>
    ⟨⟨_, h⟩, ⟨_, h⟩⟩
  have ev2 : ∀ {z q z' q' : Nat} {f f' : Event}, X.get (z, q) = some f →
      X.get (z', q') = some f' →
      (k = 0 → (∃ e, X.get (z, q) = some e) ∧ ∃ e', X.get (z', q') = some e') := fun h h' _ =>
    ⟨⟨_, h⟩, ⟨_, h'⟩⟩
  -- the words of the lane and its source read as numbers
  obtain ⟨-, xa, hxa, hra, -⟩ := H hy hy hc hc (m := 0) (by omega) (by simp) (by simp) hσp hσp
    hdp hdp (hip.trans hi) (hip.trans hi) hpk hpk (ev hep)
  obtain ⟨-, xb, hxb, hrb, -⟩ := H hx hx hxc hxc (m := 0) (by omega) (by simp) (by simp) hσ2 hσ2
    hs2 hs2 (hi2.trans hi) (hi2.trans hi) hj hj (ev he2)
  have hval : lval (k + 1) d = erealValue .f32 (min xa xb) := by
    rw [minE_readsAs hra hrb] at hmin
    exact (Except.ok.inj hmin).symm
  have hne : min xa xb ≠ ⊤ := min_ne_top' hxa
  refine ⟨?_, min xa xb, hne, by rw [hval]; exact ReadsAs.of_erealValue hne, fun _ => hval⟩
  have hmin2 := hmin'
  rcases mask_split hk4 m hm hmk with h0 | ⟨h1, h2⟩
  · -- the same words
    have e1 := (H hy hy' hc hc' hm h0 hp hσp hσp' hdp hdp' (hip.trans hi) (hip'.trans hi') hpk
      hpk' (ev2 hep hep')).1
    have hxx : x' % L.block = (x % L.block) ^^^ m := by rw [hxm', hp, hxm, xor_swap]
    have e2 := (H hx hx' hxc hxc' hm h0 hxx hσ2 hσ2' hs2 hs2' (hi2.trans hi) (hi2'.trans hi') hj
      hj' (ev2 he2 he2')).1
    rw [← e1, ← e2, hmin] at hmin2
    exact Except.ok.inj hmin2
  · -- the words swapped
    have hxx1 : x' % L.block = (y % L.block) ^^^ (m ^^^ loff k) := by
      rw [hxm', hp, Nat.xor_assoc]
    have e1 := (H hy hx' hc hxc' h2 h1 hxx1 hσp hσ2' hdp hs2' (hip.trans hi) (hi2'.trans hi') hpk
      hj' (ev2 hep he2')).1
    have hxx2 : y' % L.block = (x % L.block) ^^^ (m ^^^ loff k) := by
      rw [hp, hxm]; exact xor_swap' _ _ _
    have e2 := (H hx hy' hxc hc' h2 h1 hxx2 hσ2 hσp' hs2 hdp' (hi2.trans hi) (hip'.trans hi') hj
      hpk' (ev2 he2 hep')).1
    rw [← e1, ← e2, minE_readsAs hrb hra] at hmin2
    rw [hval, ← Except.ok.inj hmin2, min_comm]

/-- **Every level of iteration `i` in CTA `c`.** -/
theorem lev_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) (c i : Nat) :
    Lev Q L X c i 4 :=
  lev_step hpre hX hf (by omega) (lev_step hpre hX hf (by omega) (lev_step hpre hX hf (by omega)
    (lev_step hpre hX hf (by omega) (lev0 hpre hX hf hz c i))))

/-- The state at the end of the trace stands for the later ones. -/
theorem st_norm {g k : Nat} {s : TSt} (hσ : St Q L X g k = some (some s)) :
    ∃ k', k' ≤ (X.tr g).length ∧ St Q L X g k' = some (some s) := by
  by_cases hk : k ≤ (X.tr g).length
  · exact ⟨k, hk, hσ⟩
  · refine ⟨_, le_rfl, ?_⟩
    have h1 : Frame.stateAt (code L Q) X g k =
        Frame.stateAt (code L Q) X g (X.tr g).length := Frame.stateAt_of_le (by omega)
    exact h1.symm.trans hσ

/-- Two positions of one warp differ by a mask below 32. -/
theorem warp_mask {T T' : Nat} (hT : T < 256) (_hT' : T' < 256) (h : T / 32 = T' / 32) :
    (T % 32 ^^^ T' % 32) < 32 ∧ T' = T ^^^ (T % 32 ^^^ T' % 32) := by
  have hl : (T % 32 ^^^ T' % 32) < 32 := by
    have := Nat.xor_lt_two_pow (n := 5) (x := T % 32) (y := T' % 32) (by omega) (by omega)
    simpa using this
  refine ⟨hl, ?_⟩
  rw [xor_low T hT _ hl, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  omega

/-- **The lanes of each default warp of CTA `c` store one number at `store10` of iteration
`i`**: the body of `StoreWord`. -/
theorem storeWordB (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) (c i : Nat) :
    ∀ r < 4, ∃ w : EReal, w ≠ ⊤ ∧
      ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c → g % L.block / 32 = r →
        St Q L X g k = some (some (.d (.sm d))) → d.site = .store10 → d.i = i →
        d.stg.cm4 = erealValue .f32 w := by
  have hb : L.block = 256 := hpre.block
  intro r _
  have H : Lev Q L X c i 4 := lev_all hpre hX hf hz c i
  by_cases hex : ∃ (g k : Nat) (d : Sm.D), g < L.threads ∧ g / L.block = c ∧
      g % L.block / 32 = r ∧ k ≤ (X.tr g).length ∧ St Q L X g k = some (some (.d (.sm d))) ∧
      d.site = .store10 ∧ d.i = i
  · obtain ⟨g0, k0, d0, hg0, hc0, hr0, hk0, hσ0, hs0, hi0⟩ := hex
    obtain ⟨-, w, hw, -, hval⟩ := H hg0 hg0 hc0 hc0 (m := 0) (by omega) (by simp [lmask])
      (by simp) hσ0 hσ0 hs0 hs0 hi0 hi0 hk0 hk0 (by intro h; cases h)
    refine ⟨w, hw, fun {g k d} hg hc hr hσ hs hi => ?_⟩
    obtain ⟨k', hk', hσ'⟩ := st_norm hσ
    have hT0 : g0 % L.block < 256 := by rw [hb]; exact Nat.mod_lt _ (by decide)
    have hT : g % L.block < 256 := by rw [hb]; exact Nat.mod_lt _ (by decide)
    obtain ⟨hml, hmeq⟩ := warp_mask hT0 hT (hr0.trans hr.symm)
    have := (H hg0 hg hc0 hc hml (Nat.mod_one _) hmeq hσ0 hσ' hs0 hs hi0 hi hk0 hk'
      (by intro h; cases h)).1
    exact this.symm.trans (hval (by decide))
  · refine ⟨0, EReal.zero_ne_top, fun {g k d} hg hc hr hσ hs hi => ?_⟩
    obtain ⟨k', hk', hσ'⟩ := st_norm hσ
    exact absurd ⟨g, k', d, hg, hc, hr, hk', hσ', hs, hi⟩ hex

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
