-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.Gen.Steps

@[expose] public section

/-!
# A. The conversion loop: `state_acc` receives the bfloat16 payloads of the initial state

Before the tile loop every thread of a block converts its share of the 128 × 128 FP32 initial
state: `ld.b32` of an element of the FP32 buffer through a swizzled generic pointer,
`cvt.rn.bf16.f32`, `st.shared.b16` into the bfloat16 copy `state_acc` (ten such triples in the
code, in two loops).

* `conv_alive`: at a conversion load the thread is followed across the load and the
  conversion. The four bytes it reads are those of the binary32 payload of an entry of the
  initial state (`EarlyRead`: the buffer holds what the sixteen tensor loads wrote), so the
  loaded value is that payload and the conversion (assumption `narrow`: a finite number keeps
  its real value) writes the bfloat16 payload of the same number. No data value makes the run
  after the load fault. The successor is at the store, whose source register holds the payload.
* `conv_store_ok`: at that store the source converts to the store's width, so the store is not
  undefined behaviour because of its value.
* `acc_content`: **a write of a byte of `state_acc` with three `bar.sync 0` before it writes
  `accInitByte`**, the byte of the bfloat16 payload of the initial state at that offset. This
  is the hypothesis `hcontent` of the protocol layer's `StateAccFacts.acc_read`, in its exact
  shape (`accInit := accInitByte P (c % N) (c / N)`: block `c` works on sequence `c % N` and
  head `c / N`).

Hypotheses: `Followed` (the thread layer: the machine is sound and follows every thread),
`ConvRef` (the Conversion phase: addresses), `EarlyRead` (protocol layer and startup phase: what
a read of the buffer returns, `Contract.lean: earlyRead`), and that the shared base is a
multiple of 32 (`Pre.sharedAlignment` and `Pre.sharedBase`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before InStateAcc)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What a read of an element of the FP32 buffer returns before the tile loop**: the four
bytes of the binary32 payload of the element's entry of the initial state. -/
theorem early_elem (hrd : EarlyRead P L X) (hb : L.sharedBase % 32 = 0) {g k pc el : ℕ}
    {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hbar : bar0Before X (g, k) ≤ 5) (hel : el < 16384) (hsz : a.size = 4)
    (hloc : a.loc = ⟨.shared, g / L.block, swzAddr (L.sharedBase + 32768 + 4 * el)⟩) :
    bs = f32Bytes (entry (initState P (g / L.block)) el) := by
  obtain ⟨h1, h2⟩ := swzAddr_sub (o := 4 * el) hb
  have h3 := swzAddr_mod (L.sharedBase + 32768 + 4 * el)
  generalize ho : swzAddr (L.sharedBase + 32768 + 4 * el) - (L.sharedBase + 32768) = o at h2
  have hsw : swzAddr (L.sharedBase + 32768 + 4 * el) = L.sharedBase + (32768 + o) := by omega
  have h := hrd g k pc a bs o he hbar (by rw [hloc, hsw]) (by omega)
  have hbyte : ∀ i < 4, initBuf P L (g / L.block) (o + i) =
      some ((Value.float .f32 (entry (initState P (g / L.block)) el)).byteAt i) := by
    intro i hi
    rw [← ho]
    exact bufByte_elem _ hb hel hi
  rw [h, hsz, range_map4, f32Bytes, range_map4, hbyte 0 (by omega), hbyte 1 (by omega),
    hbyte 2 (by omega), hbyte 3 (by omega)]

/-- **A conversion load is followed, and the store after it holds the narrowed entry.** At the
`j`-th load site, with an event, the machine follows the thread to the `j`-th store; the store's
source register holds the bfloat16 payload of the entry of an element `el` of the initial
state; and if the next event is a write, it is the two bytes of element `el` of `state_acc`. -/
theorem conv_alive (R : ConvRef L X) (hrd : EarlyRead P L X) (hb : L.sharedBase % 32 = 0)
    {g k : ℕ} {d : D} {e : Event} (j : Fin 10)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = .load ⟨21 + j.val, by omega⟩)
    (he : X.get (g, k) = some e) :
    ∃ el < 16384, ∃ d', stateAt (code L) X g (k + 1) = some (some d') ∧
      d'.site = .store ⟨j.val, by omega⟩ ∧
      d'.x (convReg j.val) = .float .bf16 (entry (initState P (g / L.block)) el) ∧
      ∀ pc' a' bs', X.get (g, k + 1) = some ⟨pc', .wr a' bs'⟩ →
        a'.size = 2 ∧ a'.loc = ⟨.shared, g / L.block, L.sharedBase + 2 * el⟩ := by
  obtain ⟨el, hel, a, bs, rfl, hsz, hloc, hbar, hnext⟩ := R.load g k d e j hσ hs he
  have hbs := early_elem hrd hb he (by omega) hel hsz hloc
  obtain ⟨d', hn, hs', hx⟩ := Gen.conv_load (L := L) (g := g) j hs (pc := d.site.pc) (a := a)
    (hbs ▸ ldVal_f32 _)
  exact ⟨el, hel, d', (stateAt_step he hσ).trans hn, hs', hx, hnext⟩

/-- **A conversion store is not undefined behaviour because of its value**: at the state after
a conversion load, the source register of the store holds a 16-bit payload, which a 16-bit
store writes as it is. -/
theorem conv_store_ok {d' : D} {j : ℕ} {r : ℝ} (hx : d'.x (convReg j) = .float .bf16 r) :
    storeValue 16 (d'.x (convReg j)) = .ok (.float .bf16 r) := by
  rw [hx]
  exact storeValue_bf16 r

/-- **The content of the conversion stores** (`hcontent` of `StateAccFacts.acc_read`): a write
event that covers a byte `l` of `state_acc` of block `c` and has three `bar.sync 0` before it
writes at `l` the byte `accInitByte` of the bfloat16 payload of the initial state. -/
theorem acc_content (F : Followed L mem0 X) (R : ConvRef L X) (hrd : EarlyRead P L X)
    (hb : L.sharedBase % 32 = 0) {c h i pcw : ℕ} {aw : Acc} {bw : List Byte} {l : Loc}
    (hw : X.get (h, i) = some ⟨pcw, .wr aw bw⟩) (hc : aw.Covers l) (hl : InStateAcc L c l)
    (hbar : bar0Before X (h, i) = 3) :
    wbyte aw bw l = accInitByte P (c % P.sequences) (c / P.sequences) (l.addr - L.sharedBase) := by
  obtain ⟨k0, d, j, rfl, hσ, hs⟩ := R.store h i pcw aw bw hw hbar
  obtain ⟨e, he⟩ := get_of_lt hw (Nat.lt_succ_self k0)
  obtain ⟨el, hel, d', hσ', hs', hx, hnext⟩ := conv_alive R hrd hb j hσ hs he
  obtain ⟨hsz, hloc⟩ := hnext pcw aw bw hw
  obtain ⟨v', hv', rfl⟩ := Gen.conv_wr F j hw hσ' hs'
  have hv : v' = .float .bf16 (entry (initState P (h / L.block)) el) := by
    have := conv_store_ok hx
    unfold convReg at this
    rw [this] at hv'
    exact (Except.ok.inj hv').symm
  subst hv
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [hloc] at h1 h2 h3
  rw [hloc, hsz] at h4
  simp only at h1 h2 h3 h4
  have hcta : c = h / L.block := hl.2.1.symm.trans h2
  obtain ⟨i', hi', hi⟩ : ∃ i', i' < 2 ∧ l.addr = L.sharedBase + 2 * el + i' :=
    ⟨l.addr - (L.sharedBase + 2 * el), by omega, by omega⟩
  have e1 : l.addr - L.sharedBase = 2 * el + i' := by omega
  rw [e1, accInitByte_elem P _ _ hel hi', wbyte, hloc, toBytes_bf16]
  have e2 : l.addr - (L.sharedBase + 2 * el) = i' := by omega
  simp only [e2, hcta, initState]
  interval_cases i' <;> rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
