-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.Conversion

@[expose] public section

/-!
# B. The carry loads: the carry registers receive the initial state

After the conversion loop a compute thread loads its 128 entries of the FP32 initial state
into the carry registers, with 128 `ld.b32` through swizzled generic pointers (instructions
765 to 1400), each followed by the pointer arithmetic of the next address.

* `carry_read`: the `j`-th carry load returns the four bytes of the binary32 payload of the
  thread's `j`-th entry (`carryElem j tid`) of the initial state.
* `carry_load_ok`: so the loaded bytes rebuild into that payload: the load does not make the
  thread fault because of the data. (What remains for the thread to be followed across the
  site is the condition of the pointer run after the load, which is about addresses only: the
  reference layer's part.)
* `carries_at`: **the base case of the value induction of the tile loop.** A compute thread at
  the `j`-th carry load holds the initial state in its first `j` carries; at the proxy fence
  after the loads (`carrySite 128`, instruction 1401) it holds it in all 128
  (`carries_initial`: `CarriesHold (initState P c) tid d.x`). `Bridge.lean` restates
  `CarriesHold` as the invariant `(tableAt 0).Holds` of the tile loop.

The proof follows the thread from the first load (`CarryRef.first`), one site at a time, with
the generated successor `Gen.carry_step`: the slot of the carry receives the loaded value and
no other data slot changes.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The first `n` carries (in the order of their loads) hold the state `S`. -/
def CarriesTo (S : State) (tid n : ℕ) (val : ℕ → Value) : Prop :=
  ∀ j < n, val (carryReg j) = .float .f32 (entry S (carryElem j tid))

theorem carriesHold_iff {S : State} {tid : ℕ} {val : ℕ → Value} :
    CarriesHold S tid val ↔ CarriesTo S tid 128 val := Iff.rfl

/-- **What the `j`-th carry load returns**: the bytes of the binary32 payload of the thread's
`j`-th entry of the initial state. -/
theorem carry_read (R : CarryRef L X) (hrd : EarlyRead P L X) (hb : L.sharedBase % 32 = 0)
    {g k : ℕ} {d : D} {e : Event} (j : Fin 128) (hg : g % L.block < 128)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = carrySite j.val)
    (he : X.get (g, k) = some e) :
    ∃ a, e = ⟨d.site.pc, .rd a
      (f32Bytes (entry (initState P (g / L.block)) (carryElem j.val (g % L.block))))⟩ := by
  obtain ⟨a, bs, rfl, hsz, hloc, hbar⟩ := R.load g k d e j hg hσ hs he
  have haddr := carry_addr (g % L.block) j.isLt
  have hloc' : a.loc = ⟨.shared, g / L.block,
      swzAddr (L.sharedBase + 32768 + 4 * carryElem j.val (g % L.block))⟩ := by
    rw [hloc]
    congr 2
    omega
  exact ⟨a, by rw [early_elem hrd hb he hbar (carryElem_lt j.isLt hg) hsz hloc']⟩

/-- **A carry load does not fault because of the data**: its bytes load as the payload. -/
theorem carry_load_ok (R : CarryRef L X) (hrd : EarlyRead P L X) (hb : L.sharedBase % 32 = 0)
    {g k : ℕ} {d : D} {e : Event} (j : Fin 128) (hg : g % L.block < 128)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = carrySite j.val)
    (he : X.get (g, k) = some e) :
    ∃ a bs, e = ⟨d.site.pc, .rd a bs⟩ ∧ ldVal .same 32 bs =
      .ok (.float .f32 (entry (initState P (g / L.block)) (carryElem j.val (g % L.block)))) := by
  obtain ⟨a, rfl⟩ := carry_read R hrd hb j hg hσ hs he
  exact ⟨a, _, rfl, ldVal_f32 _⟩

/-- From the first carry load on: `n` positions later the thread is at the `n`-th site and its
first `n` carries hold the initial state. -/
theorem carry_prefix (F : Followed L mem0 X) (R : CarryRef L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {g k0 : ℕ} {d0 : D} (hg : g % L.block < 128)
    (hσ0 : stateAt (code L) X g k0 = some (some d0)) (hs0 : d0.site = carrySite 0) :
    ∀ n ≤ 128, ∀ d, k0 + n ≤ (X.tr g).length → stateAt (code L) X g (k0 + n) = some (some d) →
      d.site = carrySite n ∧ CarriesTo (initState P (g / L.block)) (g % L.block) n d.x := by
  intro n
  induction n with
  | zero =>
    intro _ d _ hσ
    rw [Nat.add_zero, hσ0] at hσ
    cases hσ
    exact ⟨hs0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro hn d' hlen hσ'
    obtain ⟨e, he⟩ := get_of_lt_length (X := X) (g := g) (k := k0 + n) (by omega)
    obtain ⟨d, hσ⟩ := state_before F (lt_threads F he) hσ' (Nat.le_succ (k0 + n))
    obtain ⟨hs, hc⟩ := ih (by omega) d (by omega) hσ
    obtain ⟨a, bs, v, hk, hv, hs', hx⟩ := Gen.carry_step (by omega) hs (next_some he hσ hσ')
    obtain ⟨a', bs', rfl, hok⟩ := carry_load_ok R hrd hb ⟨n, by omega⟩ hg hσ hs he
    cases hk
    rw [hv] at hok
    cases hok
    refine ⟨hs', fun j hj => ?_⟩
    obtain ⟨-, -, -, -, -, -, hlt⟩ := carryRow_ok (j := j) (by omega)
    rw [hx _ hlt]
    by_cases hjn : j = n
    · subst hjn
      simp
    · have hne : carryReg j ≠ carryReg n := fun h =>
        hjn (carryReg_inj j (by omega) n (by omega) h)
      simp only [hne, ↓reduceIte]
      exact hc j (by omega)

/-- **The carries at a carry load**: a compute thread at the `j`-th carry load (at the proxy
fence after the loads for `j = 128`) holds the initial state in its first `j` carries. -/
theorem carries_at (F : Followed L mem0 X) (R : CarryRef L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {g k j : ℕ} {d : D} (hg : g % L.block < 128) (hj : j ≤ 128)
    (hk : k ≤ (X.tr g).length) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = carrySite j) :
    CarriesTo (initState P (g / L.block)) (g % L.block) j d.x := by
  obtain ⟨hjk, d0, hσ0, hs0⟩ := R.first g k d j hg hj hk hσ hs
  have e : k - j + j = k := by omega
  exact (carry_prefix F R hrd hb hg hσ0 hs0 j hj d (by omega) (by rw [e]; exact hσ)).2

/-- **The base case of the tile loop**: after its 128 carry loads (at the proxy fence at
instruction 1401) a compute thread holds, in each carry register, the binary32 payload of its
entry of the initial state of its block. -/
theorem carries_initial (F : Followed L mem0 X) (R : CarryRef L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {g k : ℕ} {d : D} (hg : g % L.block < 128)
    (hk : k ≤ (X.tr g).length) (hσ : stateAt (code L) X g k = some (some d))
    (hs : d.site = .fenceProxy 1) :
    CarriesHold (initState P (g / L.block)) (g % L.block) d.x :=
  carries_at F R hrd hb hg le_rfl hk hσ hs

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
