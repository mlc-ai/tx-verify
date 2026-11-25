-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.CarryLoad
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue

@[expose] public section

/-!
# C. The final stores: the FP32 buffer receives the state after the last token

After the tile loop a compute thread stores its 128 carry registers into the FP32 state buffer
with 128 generic `st.b32` through swizzled pointers (instructions 3132 to 3767); the store
leader then copies the buffer to the final-state array with sixteen tensor stores.

* `final_carries`: the stores do not change the carries: a compute thread at any of the 128
  final store sites holds the final state in its carry registers (`FinalCarries`, the result
  of the tile loop, is the hypothesis at the first of them; `FinalRef.first` and the generated
  successor `Gen.final_step` carry it along).
* `final_store_ok`: so the source of each store is a binary32 payload, which a 32-bit store
  writes as it is: the store is not undefined behaviour because of its value.
* `final_content`: **a write with seven `bar.sync 0` before it writes, at each byte it covers,
  the byte `finalBuf`** of the buffer that holds the final state behind the swizzle.
* `out_final`: **the field `final` of `Protocol.OutContent`** (`Proof/Protocol/ResultGlue.lean`),
  verbatim: the owning compute thread's last epilogue write of the shared byte that a slot of
  a final-state tensor store reads carries the byte of the binary32 payload of the final state
  that the slot writes. With `final_content`, what remains is which shared byte a slot reads:
  the hypothesis `FinalSlots`, proved in `Ref/Assembly/ValuesEnds.lean: finalSlots` from the
  Epilogue phase (the exact `readLoc` of its sixteen stores and the 32-byte swizzle of tensor
  map 9, `Ref/Swizzle.lean: swzAbs_base`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before storeLeader computeThread blockOf FinalLast
  Owners thr_mod thr_div)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- From the first final store on: `n` positions later the thread is at the `n`-th final
store, with the data slots it had at the first. -/
theorem final_prefix (F : Followed L mem0 X) {g k0 : ℕ} {d0 : D}
    (hσ0 : stateAt (code L) X g k0 = some (some d0)) (hs0 : d0.site = finalSite 0) :
    ∀ n, ∀ hn : n < 128, ∀ d, k0 + n ≤ (X.tr g).length →
      stateAt (code L) X g (k0 + n) = some (some d) →
      d.site = finalSite ⟨n, hn⟩ ∧ ∀ r < 2246, d.x r = d0.x r := by
  intro n
  induction n with
  | zero =>
    intro _ d _ hσ
    rw [Nat.add_zero, hσ0] at hσ
    cases hσ
    exact ⟨hs0, fun _ _ => rfl⟩
  | succ n ih =>
    intro hn d' hlen hσ'
    obtain ⟨e, he⟩ := get_of_lt_length (X := X) (g := g) (k := k0 + n) (by omega)
    obtain ⟨d, hσ⟩ := state_before F (lt_threads F he) hσ' (Nat.le_succ (k0 + n))
    obtain ⟨hs, hc⟩ := ih (by omega) d (by omega) hσ
    obtain ⟨hs', hx⟩ := Gen.final_step (j := n) (by omega) hs (next_some he hσ hσ')
    exact ⟨hs', fun r hr => (hx r hr).trans (hc r hr)⟩

/-- **The carries at a final store**: a compute thread at any of the 128 final store sites
holds the state after the last token in its carry registers. -/
theorem final_carries (F : Followed L mem0 X) (R : FinalRef L X) (hfin : FinalCarries P L X)
    {g k : ℕ} {d : D} (j : Fin 128) (hg : g % L.block < 128) (hk : k ≤ (X.tr g).length)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = finalSite j) :
    CarriesHold (finalState P (g / L.block)) (g % L.block) d.x := by
  obtain ⟨hjk, d0, hσ0, hs0⟩ := R.first g k d j hk hσ hs
  have e : k - j.val + j.val = k := by omega
  have h := (final_prefix F hσ0 hs0 j.val j.isLt d (by omega) (by rw [e]; exact hσ)).2
  intro i hi
  obtain ⟨-, -, -, -, -, -, hlt⟩ := carryRow_ok (j := i) hi
  rw [h _ hlt]
  exact hfin g (k - j.val) d0 hg hσ0 hs0 i hi

/-- **A final store is not undefined behaviour because of its value**: its source register
holds a binary32 payload, which a 32-bit store writes as it is. -/
theorem final_store_ok (F : Followed L mem0 X) (R : FinalRef L X) (hfin : FinalCarries P L X)
    {g k : ℕ} {d : D} (j : Fin 128) (hg : g % L.block < 128) (hk : k ≤ (X.tr g).length)
    (hσ : stateAt (code L) X g k = some (some d)) (hs : d.site = finalSite j) :
    storeValue 32 (d.x (carryReg j.val)) = .ok (.float .f32
      (entry (finalState P (g / L.block)) (carryElem j.val (g % L.block)))) := by
  rw [final_carries F R hfin j hg hk hσ hs j.val j.isLt]
  exact storeValue_f32 _

/-- **The content of the final stores**: a write event with seven `bar.sync 0` before it
writes, at each byte `l` it covers, the byte of the FP32 buffer that holds the final state of
the thread's block. -/
theorem final_content (F : Followed L mem0 X) (R : FinalRef L X) (hfin : FinalCarries P L X)
    (hb : L.sharedBase % 32 = 0) {g k pc : ℕ} {aw : Acc} {bw : List Byte} {l : Loc}
    (hw : X.get (g, k) = some ⟨pc, .wr aw bw⟩) (hc : aw.Covers l)
    (hbar : bar0Before X (g, k) = 7) :
    wbyte aw bw l = finalBuf P L (g / L.block) (l.addr - (L.sharedBase + 32768)) := by
  obtain ⟨hg, d, j, hσ, hs⟩ := R.site g k pc aw bw hw hbar
  obtain ⟨hsz, hloc⟩ := R.store g k d pc aw bw j hg hσ hs hw
  have hk : k ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨v', hv', rfl⟩ := Gen.final_wr F j.isLt hw hσ hs
  rw [final_store_ok F R hfin j hg hk hσ hs] at hv'
  cases hv'
  have hel := carryElem_lt j.isLt hg
  have haddr := carry_addr (g % L.block) j.isLt
  have hloc' : aw.loc = ⟨.shared, g / L.block,
      swzAddr (L.sharedBase + 32768 + 4 * carryElem j.val (g % L.block))⟩ := by
    rw [hloc]
    congr 2
    omega
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [hloc'] at h3
  rw [hloc', hsz] at h4
  simp only at h3 h4
  have hge := (swzAddr_sub (o := 4 * carryElem j.val (g % L.block)) hb).1
  obtain ⟨i', hi', hi⟩ : ∃ i', i' < 4 ∧ l.addr =
      swzAddr (L.sharedBase + 32768 + 4 * carryElem j.val (g % L.block)) + i' :=
    ⟨l.addr - swzAddr (L.sharedBase + 32768 + 4 * carryElem j.val (g % L.block)), by omega,
      by omega⟩
  have e1 : l.addr - (L.sharedBase + 32768) =
      swzAddr (L.sharedBase + 32768 + 4 * carryElem j.val (g % L.block)) -
        (L.sharedBase + 32768) + i' := by omega
  have e2 : l.addr - aw.loc.addr = i' := by
    rw [hloc']
    simp only
    omega
  rw [finalBuf, e1, bufByte_elem _ hb hel hi', wbyte, e2, toBytes_f32]
  interval_cases i' <;> rfl

/-- **From the Epilogue phase: the shared byte that a slot of a final-state store reads.** A
tensor store of the store leader of the block of sequence `s` and head `h` whose slot
`(x, y, z)` writes byte `b` of the final-state entry of value channel `v` and key feature `k`
reads, at that slot, byte `b` of the element `elemOf v k` of the FP32 buffer, behind the
swizzle. -/
def FinalSlots (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {s h b i pc al x y z : ℕ} {sp : TensorStore.Spec} {l : Loc} {v k : Fin 128},
    s < P.sequences → h < P.heads → b < 4 →
    X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ →
    TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b) →
    TensorStore.readLoc sp x y z = some l →
    l = ⟨.shared, blockOf P s h,
      swzAddr (L.sharedBase + 32768 + 4 * elemOf v.val k.val) + b⟩

/-- **The field `final` of `Protocol.OutContent`**: the owning compute thread's last write in
the epilogue of the shared byte that a final-state store copies to byte `b` of entry `(v, k)`
carries the byte of the binary32 payload of the state after the last token. -/
theorem out_final (F : Followed L mem0 X) (R : FinalRef L X) (hfin : FinalCarries P L X)
    (hslots : FinalSlots P L X) (hblock : L.block = 192) (hb : L.sharedBase % 32 = 0)
    {O : Owners} {s h b i pc al x y z : ℕ} {sp : TensorStore.Spec} {l : Loc} {v k : Fin 128}
    (hs : s < P.sequences) (hh : h < P.heads) (hb4 : b < 4)
    (hst : X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩)
    (hwl : TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b))
    (hrl : TensorStore.readLoc sp x y z = some l) (ga : Fin 128) (iw : ℕ) (aw : Acc)
    (bw : List Byte) (_hown : O.final l = ga.val)
    (hlast : FinalLast L X (blockOf P s h) ga l iw aw bw) :
    wbyte aw bw l = some ((Value.float .f32 (P.state s h v (P.length s) k)).byteAt b) := by
  obtain ⟨pcw, hw⟩ := hlast.get
  have hdiv : computeThread L (blockOf P s h) ga / L.block = blockOf P s h :=
    thr_div hblock (by have := ga.isLt; omega)
  have hwb := final_content F R hfin hb hw hlast.covers hlast.count
  rw [hdiv, hslots hs hh hb4 hst hwl hrl] at hwb
  have hl := hslots hs hh hb4 hst hwl hrl
  rw [hl, hwb]
  have hel := elemOf_lt v.isLt k.isLt
  have hge := (swzAddr_sub (o := 4 * elemOf v.val k.val) hb).1
  have e1 : swzAddr (L.sharedBase + 32768 + 4 * elemOf v.val k.val) + b -
      (L.sharedBase + 32768) =
      swzAddr (L.sharedBase + 32768 + 4 * elemOf v.val k.val) - (L.sharedBase + 32768) + b := by
    omega
  simp only [finalBuf]
  rw [e1, bufByte_elem _ hb hel hb4, entry_elemOf]
  have e2 : blockOf P s h % P.sequences = s := by
    unfold blockOf
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have e3 : blockOf P s h / P.sequences = h := by
    unfold blockOf
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]
  simp only [finalState, e2, e3]

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
