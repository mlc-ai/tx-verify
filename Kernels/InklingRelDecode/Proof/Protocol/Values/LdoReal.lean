-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdSrc
public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The word an accumulator load of a round returns

The load of round `r` takes its word from the last PV step of ordinal `r` (`ld_o_pv7`): the other
writers of the cell are earlier PV steps, and the rescale stores of earlier rounds, all before it,
or later ones, after the load. The word is the `ResReal` of that step. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- Every accumulator load of a round precedes every rescale store of its round, in a thread. -/
def LdBeforeSt (X : Execution) : Prop :=
  ∀ t kl k a' ov sh' a vals sh,
    X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
    X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
    pollRound 1257 ((X.tr t).take kl) = pollRound 1257 ((X.tr t).take k) → kl < k

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The source of an accumulator load of round `r` is the last PV step of ordinal `r`.** -/
theorem ld_o_src (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (ord : LdBeforeSt X)
    {t k0 a vals sh j r} (he : X.get (t, k0) = some ⟨2260, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1) {src : EvId}
    (hrs : ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j)) :
    ∃ g kR, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧
      pollRound 2510 ((X.tr g).take kR) = r ∧ src = (g, kR) := by
  obtain ⟨g, kR, cy, ⟨d7, s7, a7, m7, gw⟩, ord7, wbw⟩ := ld_o_pv7 hp hX hf hu safe hG base rows
    init he s1
  have ht : t < L.threads := Frame.lt_of_get hX he
  refine ⟨g, kR, cy, ⟨d7, s7, a7, m7, gw⟩, ord7,
    ld_src_pv7 hp hX hf hu hG base (Or.inl rfl) he hj gw cy wbw ?_ ?_ hrs⟩
  · intro k2 j2 d2 s2 a2 m2 he2 hwb
    by_contra big
    have rb := ld_pv_big hp hX hf safe base rows init he s1 he2 cy.symm rfl (by omega)
    have ne : (g, k2) ≠ (t, k0) := fun hh => by
      rw [hh, he] at he2
      simp at he2
    exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep rb ne).trans hwb.tcStep)
  · intro k2 a2 v2 g2'
    have tc : isTcColl ⟨2328, .tc (.st a2 v2 (.s16x32bx2 64))⟩ = true := rfl
    obtain ⟨rs, ws, s1s, -, -, -⟩ := Proof.Export.st_round hp hX hf base g2' tc (.inr rfl)
    by_cases small : rs < r
    · exact .inl (store_pv_before hp hX hf safe base rows init g2' s1s gw cy.symm ord7 small)
    · refine .inr (.inr ⟨TcMma.sameWarp_self ht, .inl (baseCausality_of_tc_po he rfl ?_
        (List.getElem?_eq_some_iff.mp g2').1), ⟨_, _, _, _, he⟩, ⟨_, _, _, _, g2'⟩⟩)
      rcases Nat.lt_or_ge r rs with gt | eq
      · by_contra le
        have mono : pollRound 1257 ((X.tr t).take k2) ≤ pollRound 1257 ((X.tr t).take k0) :=
          (List.take_sublist_take_left (Nat.le_of_not_lt le)).countP_le (p := okPollAt 1257)
        omega
      · exact ord t k0 k2 _ _ _ _ _ _ he g2' (by omega)

/-- **An accumulator load of round `r` returns the real of the last PV step of ordinal `r`.** -/
theorem ld_o_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hws : WritesSafe L X)
    (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    (words : RoleBytes L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) (W : Iface.PWords X)
    {pw : Nat → Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) (ord : LdBeforeSt X)
    {t k0 a vals sh j r} (he : X.get (t, k0) = some ⟨2260, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1)
    (valid : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane)) :
    ∃ g kR r1, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧
      pollRound 2510 ((X.tr g).take kR) = r ∧
      ResReal L X (pvA L X pw) (pvB Q L X) (svOf L X) (g, kR) (tcDataCell L t sh a j) r1 ∧
      vals[j]? = some (.float .f32 r1) :=
  ld_pv_real hp hX hf hu safe hG base rows init hws ht hmd words nub form W P hR (Or.inl rfl) he hj
    (fun hrs => ld_o_src hp hX hf hu safe hG base rows init ord he hj s1 hrs) valid

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
