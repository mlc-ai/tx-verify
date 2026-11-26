-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxPeer
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar9Odd
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Lemmas.Order.ReadLastAll

@[expose] public section


/-! # The exchange load returns the partner's store

The load of a lane of warpgroup 0 at pc 572 (or 1157) after `2 r + 2` barrier-9 events returns the
bytes the partner lane wrote at pc 566 (1155) after `2 r + 1` of its own (`rmax_read_bytes`): that
store is ordered before the load by barrier 9, an earlier round's store of the byte is before it by
program order, a later round's store is after the load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem count_lt_index {l : List Event} {p : Event → Bool} {i j : Nat}
    (h : (l.take i).countP p < (l.take j).countP p) : i < j := by
  by_contra hji
  have h1 : l.take j = (l.take i).take j := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have : (l.take j).countP p ≤ (l.take i).countP p := by
    rw [h1]
    exact (List.take_sublist _ _).countP_le
  omega

/-- **The exchange load returns the partner's store** (valid rows): the load of lane `g` at pc 572
or 1157 after `2 r + 2` barrier-9 events (`r` at most the CTA's block count) returns the bytes
`ws` of the partner's store at pc 566 or 1155 after `2 r + 1` of its own, when every such store of
the partner writes a four-byte word (`hlen`). -/
theorem rmax_read_bytes (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {g k r pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (hw : warp L g < 4) (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hpc : pc = 572 ∨ pc = 1157)
    (hcnt : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2)
    (hrR : r ≤ blocksOf P L (g / L.block)) (hv : W0Below P L X (w0Partner L g) g k)
    (hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → (f.pc = 566 ∨ f.pc = 1155) →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) = 2 * r + 1 →
      ws.length = 4) :
    ∃ j f a' ws, X.get (w0Partner L g, j) = some f ∧ (f.pc = 566 ∨ f.pc = 1155) ∧
      f.kind = .wr a' ws ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) = 2 * r + 1 ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) ∧
      bs = ws.map some := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hs, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  obtain ⟨j, f, hf, hfpc, hcj, htc, huniq⟩ := rmax_peer_store hp hX hFw hR hw he hcnt hrR hv
  generalize hh : w0Partner L g = h at *
  have hat : MbarRow.Wg0At L g pc := ⟨hw, by omega, by omega⟩
  have hath : MbarRow.Wg0At L h f.pc := ⟨hwh, by omega, by omega⟩
  obtain ⟨-, hrd⟩ := wg0_peerPlace hp hX hFw he (fun _ h => by cases h) hat (by dsimp only; omega)
  obtain ⟨hwr, -⟩ := wg0_peerPlace hp hX hFw hf (hv j f hf htc).2 hath (by omega)
  obtain ⟨a1, bs1, hk1, hwa⟩ := hrd (by simpa using hpc)
  cases hk1
  obtain ⟨fpc, fk⟩ := f
  obtain ⟨a', ws, hk', hwa'⟩ := hwr (by simpa using hfpc)
  simp only at hk'
  subst hk'
  simp only at hfpc
  have hb0 : L.block = 384 := by have := hp.block; omega
  have hxor : 4 * (g % L.block) ^^^ 256 = 4 * ((g % L.block) ^^^ 64) := by
    have h1 : 4 * (g % L.block) = (g % L.block) <<< 2 := by simp [Nat.shiftLeft_eq, Nat.mul_comm]
    have h2 : 256 = 64 <<< 2 := by decide
    rw [h1, h2, ← Nat.shiftLeft_xor_distrib]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  have hxh : (L.tidOf h).x = (g % L.block) ^^^ 64 := by rw [tidOf_x_eq hp, ← hmod, hb0]
  have hxg : (L.tidOf g).x = g % L.block := by rw [tidOf_x_eq hp, hb0]
  obtain ⟨hl1, hs1⟩ := id hwa
  obtain ⟨hl2, hs2⟩ := hwa'
  rw [hxg, hxor] at hl1
  rw [hxh] at hl2
  rw [← hdiv] at hl1
  have hloc : a'.loc = a.loc := by rw [hl1, hl2]
  have hsz : a'.size = a.size := by rw [hs1, hs2]
  have hws : ws.length = a.size := by
    rw [hs1]; exact hlen j ⟨fpc, .wr a' ws⟩ a' ws hf hfpc rfl htc hcj
  have hMR : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
  have hMW : X.MemWrites (.thread (h, j)) a' ws := Or.inl ⟨fpc, hf⟩
  have hrow : MemRow.SharedIn L (g / L.block) .rowMax a := by
    have ht := MemRow.wg0_tid hw
    have hx : 4 * (L.tidOf g).x ^^^ 256 < 512 :=
      Nat.xor_lt_two_pow (n := 9) (by omega) (by omega)
    have h4 : (4 * (L.tidOf g).x ^^^ 256) % 2 ^ 2 = 0 := by
      rw [Nat.xor_mod_two_pow]
      simp only [Nat.reducePow, Nat.reduceMod, Nat.mul_mod_right, Nat.xor_self]
    exact MemRow.wsAcc_in hwa (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega)
  have hkk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hnbf := wg0_store_notBar hp hX hFw hf (by simpa using hfpc)
  have hnbr : Execution.isBarId 9 (⟨pc, .rd a bs⟩ : Event) = false := by simp [Execution.isBarId]
  have hcov : ∀ k' < a.size, a'.Covers (a.loc.at k') := fun k' hk' => by
    rw [show a' = { a' with loc := a.loc, size := a.size } by cases a'; simp_all]
    exact Acc.covers_at hk'
  have hAw : X.Access (h, j) a' true := Or.inr (Or.inl ⟨ws, ⟨fpc, hf⟩, rfl⟩)
  have hv : ∀ k' < a.size, ByteCausality L X (a.loc.at k') (.thread (h, j)) (.thread (g, k)) :=
    fun k' _ => .direct (.of_base L (bar9_order hp hX hFw hR hs hwh hf hnbf hkk
      (by rw [hcj, hcnt]; omega) (by rw [hdiv]; omega)))
  have hall : ∀ k' < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k') → w' = .thread (h, j) ∨
        ByteCausality L X (a.loc.at k') w' (.thread (h, j)) ∨
        ByteCausality L X (a.loc.at k') (.thread (g, k)) w' := by
    intro k' hk' w' dst' bytes hMW' hc'
    have hl : MemRow.LocIn L (g / L.block) .rowMax (a.loc.at k') :=
      MemRow.SharedIn.locIn hrow (Acc.covers_at hk')
    obtain ⟨⟨g', k''⟩, rfl⟩ := region_thread hp hX hFw (by simp) (by simp) (by simp)
      hMW'.intent hc' hl
    have hacc : X.Access (g', k'') dst' true := hMW'.intent
    obtain ⟨e', he', -, hnb', hcta, r', hr', hcnt', hidx, hpc'⟩ :=
      rmax_cls hp hX hFw hacc hc' hl
    simp only [ite_true] at hcnt' hpc'
    have hg' : g' = h := by
      have h1 := hidx rfl
      have h2 : (a.loc.at k').addr = L.sharedBase + (221184 + 4 * ((g % L.block) ^^^ 64) + k') := by
        rw [hl1]
        simp only [Loc.at, wsLoc]
        omega
      have h3 : (a.loc.at k').cta = h / L.block := by rw [hl1]; rfl
      have h4 : g' / L.block = h / L.block := by rw [← hcta, h3]
      have h5 : g' % L.block = h % L.block := by rw [h1, h2, hmod]; omega
      calc g' = L.block * (g' / L.block) + g' % L.block := (Nat.div_add_mod _ _).symm
        _ = L.block * (h / L.block) + h % L.block := by rw [h4, h5]
        _ = h := Nat.div_add_mod _ _
    subst hg'
    have hk2 : k'' < (X.tr g').length := (List.getElem?_eq_some_iff.mp he').1
    rcases Nat.lt_trichotomy r' r with hlt | rfl | hgt
    · right; left
      have hlt' : k'' < j := count_lt_index (by rw [hcnt', hcj]; omega)
      exact .direct (.of_base L (.single (.inl
        (po_of_overlap hacc hAw rfl hlt' ⟨_, hc', hcov k' hk'⟩))))
    · left
      rw [huniq k'' e' he' hpc' hcnt']
    · right; right
      exact .direct (.of_base L (bar9_order hp hX hFw hR ⟨hs.2.1, hs.1, hs.2.2.symm⟩ hw he
        hnbr hk2 (by rw [hcnt, hcnt']; omega) (by omega)))
  have := read_of_last_write_ordered hX hMR hMW hloc hsz hws hv hall
  exact ⟨j, ⟨fpc, .wr a' ws⟩, a', ws, hf, hfpc, rfl, hcj, htc, this⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
