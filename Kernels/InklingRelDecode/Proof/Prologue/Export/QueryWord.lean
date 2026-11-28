-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.QueryTile
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Prologue.ValueEvent
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryHalf
import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryHist
import Kernels.InklingRelDecode.Proof.Prologue.QueryAddress
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
public import Kernels.InklingRelDecode.Proof.Lib.QTile
import Kernels.InklingRelDecode.Proof.Prologue.QueryStoreAt
import Kernels.InklingRelDecode.Proof.Prologue.QueryLen
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store
import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Lemmas.Flow.StoreBytes

/-! # A query store writes the pair of the query elements it packs, or zero

The prologue's value machine records the half every query load returns (the element of the query
tensor it reads, `query_half`); at a store the register of a packed word holds the two halves
(`qw_word`), and the store writes the bytes of the register. The word is zero exactly when the
group of the store does not load (`queryOn_iff`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control Data

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem ldq_load : ∀ j : Fin 64,
    Lib.globalLoad (Site.ldq j).pc (2077 + j.val) 16 = true := by decide +kernel

private theorem ldq_site (s : Site) (j : Fin 64) (h : s.pc = 388 + 2 * j.val) : s = .ldq j := by
  cases s with
  | ldq i =>
    have : i.val = j.val := by simp only [Site.pc] at h; omega
    exact congrArg Site.ldq (Fin.ext this)
  | _ => exfalso; revert h; revert j; decide +revert

private theorem store_site (s : Site) (i : Fin 8) : s.pc = 526 + 6 * i.val → ∃ j, s = .stq i j := by
  revert i
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem qw_tag : ∀ (i : Fin 8) (j : Fin 4), Tag.qw i j ∈ tags (.stq i j) := by
  decide +kernel

/-- **The history of the halves along the value states**: a query load is on and returns a
number. -/
private theorem qhist_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {k : Nat} {w : Value} {d : Prologue.Data.D} {n : Cls → Nat}
    (hk : k ≤ (X.tr g).length)
    (hs : Frame.stateAt (threadD Q L) X g k = some (some (proDState w d n)))
    (nub : Frame.NoUbBefore X g k) : QHist Q L g d := by
  refine proD_induct (X := X) (fun _ d => QHist Q L g d) (fun _ => qHist_init Q L g) ?_ hk hs
    nub
  intro k e w' old cnt d' he hu hs' IH hv
  obtain ⟨t, ins, o, ht, inv, hc, fire⟩ :=
    Frame.fired_siteU (fun g h => threadD_sound hp h) hX he hs' hu
  have pc := Frame.event_pcU (fun g h => threadD_sound hp h) hX he hs' hu
  change kernel.code[old.c.site.pc]? = some ins at hc
  change Fires old.c.site.pc (eventTmpl Assumptions.all L g t ins.op) e o at fire
  change e.pc = old.c.site.pc at pc
  refine qHist_next hv IH (fun j hj => ?_) fun j hj => ?_
  · have := inv.1.1
    simpa only [Control.Inv, hj] using this
  · rw [hj] at hc fire pc
    rcases Lib.global_load_kind hc (ldq_load j) fire with ⟨a, bs, hk⟩ | ⟨f, hf⟩
    · obtain ⟨epc, ekind⟩ := e
      change ekind = _ at hk
      subst hk
      change epc = _ at pc
      rw [pc] at he
      exact ⟨a, bs, rfl, query_half hp hX hf he rfl⟩
    · exact absurd hf (hu f)

/-- **A query store writes its word of the packed halves**: the pair of the query elements when
its group loads, zero otherwise, at the lane's word `j` of the tile. -/
public theorem query_word_exact {a bs} {i : Fin 8} {k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨526 + 6 * i.val, .wr a bs⟩) :
    ∃ j : Fin 4, a.loc = ⟨.shared, g / L.block,
      L.sharedBase + Lib.qSwz (g % L.block) + (196608 + 2048 * Lib.qGroup i) + 4 * j.val⟩ ∧
      (Lib.QValid Q L g (i.val / 2) → ∀ z < 2,
        bs[z]? = some ((Value.float .bf16 (Lib.qElem Q L g (8 * i.val + 2 * j.val))).byteAt z) ∧
        bs[2 + z]? = some
          ((Value.float .bf16 (Lib.qElem Q L g (8 * i.val + 2 * j.val + 1))).byteAt z)) ∧
      (¬ Lib.QValid Q L g (i.val / 2) →
        ∀ q < 4, bs[q]? = some (Value.bits 32 (BitVec.ofNat 64 0), q)) := by
  have hi := i.isLt
  have hg := Frame.lt_of_get hX he
  obtain ⟨w, d, n, t, ins, u, hs, ht, pce, hc, fire⟩ :=
    proD_event hp hX he (fun f => by simp) (by simp only; omega) (by simp only; omega)
  obtain ⟨j, site⟩ := store_site d.c.site i pce.symm
  have hm := Frame.stateAt_map (threadD_stepMap (Q := Q) (L := L)) X g k
  rw [hs] at hm
  have hc0 : Frame.stateAt (thread Q L) X g k = some (some (proState w d.c n)) := hm.symm
  have known := pro_known hp hX (List.getElem?_eq_some_iff.mp he).1.le hc0
  obtain ⟨tc, insc, oc, htc, -, hcc, firec⟩ :=
    Frame.fired_siteU (fun g h => thread_sound hp h) hX he hc0 (by simp)
  obtain ⟨addr, -⟩ := (query_store_at hp i j site htc hcc firec).2 a bs rfl
  have hist := qhist_at hp hX hf (List.getElem?_eq_some_iff.mp he).1.le hs
    (Frame.noUbBefore_of_get hX he)
  obtain ⟨hpc, sub, acc, flt, regs⟩ := ht
  obtain ⟨regsC, regsD⟩ := (holds_append _ _ _).mp regs
  rw [site] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans (fetchQueryStore i))
  have live : ∀ i : Fin 8, 746 + 5 * i.val ∈ ctlLive (526 + 6 * i.val) := by decide +kernel
  have found := holds_mem regsC (mem_factsFrom (by rw [site]; exact live i))
  change t.regs (746 + 5 * i.val) = some (valueOf Q L g w d.c (746 + 5 * i.val)) at found
  rw [query_register hp i] at found
  have range := queryAddress_range hp g i
  have room := hp.sharedRange
  change L.sharedBase + 213340 ≤ 2 ^ 18 at room
  have small : queryAddress L g i < 2 ^ 32 := by omega
  have val := holds_mem regsD (List.mem_map.mpr ⟨_, site ▸ qw_tag i j, rfl⟩)
  change t.regs _ = some (Tag.val Q L g d (.qw i j)) at val
  change t.sub = d.c.site.sub at sub
  rw [site] at sub
  change t.sub = j.val at sub
  obtain ⟨v', sv, rfl⟩ := fires_stv32_bytes (A := Assumptions.all) (L := L) (g := g)
    (srcs := srcs i) (ik := .b) found small (r := 747 + 5 * i.val + j.val)
    (by rw [sub]; fin_cases j <;> simp [srcs] <;> omega) val (.inr (.inr rfl)) fire a bs rfl
  have pc' : 526 + 6 * i.val = d.c.site.pc := pce
  have iff := queryOn_iff hp (gp := i.val / 2) (tid := g % L.block)
    (Lib.coordinate_bounds hp hg).2.2 (by omega)
    (qlen_known hp (Lib.coordinate_bounds hp hg).2.2 known (by omega))
  refine ⟨j, addr, fun hv z hz => ?_, fun hv q hq => ?_⟩
  all_goals rcases qw_word (Q := Q) hist site j with ⟨on, h⟩ | ⟨off, h⟩
  · rw [h, storeValue_of_bytes (by simp [Value.bytes, FloatFmt.bytes])] at sv
    obtain rfl := Except.ok.inj sv
    refine ⟨?_, ?_⟩ <;>
      simp only [Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.getElem?_map,
        List.getElem?_range (by omega : z < 4), List.getElem?_range (by omega : 2 + z < 4),
        Option.map_some]
    · simp [show z ≤ 1 by omega]
    · simp [show ¬ 2 + z ≤ 1 by omega]
  · exact absurd (iff.mpr hv) (by simp [off])
  · exact absurd (iff.mp on) hv
  · rw [h, storeValue_of_bytes (by simp [Value.bytes])] at sv
    obtain rfl := Except.ok.inj sv
    simp [Value.toBytes, Value.byteAt, Value.bytes, hq]

/-- **A query store writes two bf16 numbers or the zero word.** -/
public theorem query_word {a bs} {i : Fin 8} {k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g, k) = some ⟨526 + 6 * i.val, .wr a bs⟩) : Iface.QueryWord bs := by
  obtain ⟨j, -, pair, zero⟩ := query_word_exact hp hX hf he
  by_cases h : Lib.QValid Q L g (i.val / 2)
  · exact .inl ⟨_, _, pair h⟩
  · exact .inr (zero h)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
