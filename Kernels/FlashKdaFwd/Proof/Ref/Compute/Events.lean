-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Control
public import Kernels.FlashKdaFwd.Flow.Code
public import Lemmas.Flow.TcTmpl
public import Lemmas.Flow.Step.ShapeTc

@[expose] public section

/-! # The control events of the Compute phase, in closed form

The seven events of the phase that are not memory accesses or matrix events, each as an
equation for the event, from the invariant's facts at the position (`Tile`), the concrete state
of the thread (`Code.AtD`: the registers hold the values of the machine's file) and the firing
fact of the site's instruction (`Fires`); these three are what `Frame.fired_site` gives for an
event at a followed state.

| position | instruction | event |
|---|---|---|
| entry | 1402 `bar.sync 0` | `.bar 0 none .sync` |
| 0 | 2144 `mbarrier.try_wait.parity` | a poll of `storeEmpty (t % 2)`, parity `(t / 2 + 1) % 2` |
| 1 | 2186 `mbarrier.try_wait.parity` | a poll of `loadFull (t % 3)` with parity `t / 3 % 2` |
| 264 | 2913 `bar.sync %r1615, %r1616` | `.bar 8 (some 128) .sync` |
| 265 | 2914 `fence.proxy.async.shared::cta` | `.fenceProxy (.async (some (.shared .cta))) none` |
| 266 | 2920 `mbarrier.arrive.shared::cta` | one release arrival on `storeFull (t % 2)` |
| 267 | 2928 `mbarrier.arrive.shared::cluster` | one release arrival on `loadEmpty (t % 3)` |

None of them is an undefined-behaviour event: each closed form is exact (the addresses are
aligned and in range, the barrier id is below 16 and its count 128 is a multiple of 32 other
than the block size, the pointer `mapa` returned names the thread's own block).

Then the **ledger of each event** (`ledEv`), as a closed form in the tile (`dPollE`, `dPollF`,
`dBar8`, `dArrF`, `dArrE`; zero for the fence), and the equations between the ledgers of
consecutive positions (`led_*`).

`stage2 t`, `stage3 t`: the output stage `t % 2` and the input stage `t % 3` of tile `t`, as
indices of the mbarriers of `Protocol.Bar`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g t : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {tt : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- The output stage of tile `t`. -/
abbrev stage2 (t : Nat) : Fin 2 := ⟨t % 2, Nat.mod_lt _ (by decide)⟩

/-- The input stage of tile `t`. -/
abbrev stage3 (t : Nat) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩

/-- No assumption of the kernel widens the scope of an mbarrier instruction. -/
theorem noWiden (pc : Nat) : Assumptions.all.any (·.clusterScopeMbar pc) = false := rfl

/-! ### The locations of the four mbarriers of a tile -/

theorem loc_storeEmpty (hpre : Pre P L mem0) (t : Nat) :
    (⟨.shared, g / L.block, P.sharedBase + 8 * (t % 2) + 98368⟩ : Loc) =
      (Bar.storeEmpty (stage2 t)).loc L (g / L.block) := by
  simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and]
  omega

theorem loc_loadFull (hpre : Pre P L mem0) (t : Nat) :
    (⟨.shared, g / L.block, P.sharedBase + 8 * (t % 3) + 98304⟩ : Loc) =
      (Bar.loadFull (stage3 t)).loc L (g / L.block) := by
  simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and]
  omega

theorem loc_storeFull (hpre : Pre P L mem0) (t : Nat) :
    (⟨.shared, g / L.block, P.sharedBase + 8 * (t % 2) + 98352⟩ : Loc) =
      (Bar.storeFull (stage2 t)).loc L (g / L.block) := by
  simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and]
  omega

theorem loc_loadEmpty (hpre : Pre P L mem0) (t : Nat) :
    (⟨.shared, g / L.block, P.sharedBase + 8 * (t % 3) + 98328⟩ : Loc) =
      (Bar.loadEmpty (stage3 t)).loc L (g / L.block) := by
  simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and]
  omega

/-- The parity a poll reads from a register that holds 0 or 1. -/
theorem par_toNat {n : Nat} (h : n < 2) : (BitVec.ofNat 64 n).toNat % 2 = n := by
  rw [BitVec.toNat_ofNat]
  omega

/-! ### The events -/

/-- **The entry**: the sixth `bar.sync 0` of the thread. -/
theorem ev_entry (hc : kernel.code[(Site.bar 5).pc]? = some ins)
    (hf : Fires (Site.bar 5).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    e = ⟨1402, .bar 0 none .sync⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  exact shape_barSync (P := fun e' => e' = ⟨1402, .bar 0 none .sync⟩) hf (by decide) rfl

/-- **The first poll**: of the "empty" mbarrier of the tile's output stage. -/
theorem ev_pollE (hpre : Pre P L mem0) (h : Tile P L g t 0 w p x)
    (hat : (code L g).AtD ⟨.mbarWait 7, w, p, x⟩ tt)
    (hc : kernel.code[(Site.mbarWait 7).pc]? = some ins)
    (hf : Fires (Site.mbarWait 7).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    ∃ ok, e = ⟨2144, .wait ((Bar.storeEmpty (stage2 t)).loc L (g / L.block))
      ((t / 2 + 1) % 2) ok true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1151) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 2109) (by lit_mem) (n := 32) rfl
  dsimp only at r1 r2
  rw [show w 1151 = W (P.sharedBase + 8 * (t % 2) + 98368) from h.regs 1151 (by decide)] at r1
  rw [show w 2109 = W ((t / 2 + 1) % 2) from h.regs 2109 (by decide)] at r2
  have hm := mbarLoc_b32 (L := L) (g := g) r1 (by omega) (by omega)
  rw [loc_storeEmpty hpre t] at hm
  exact shape_wait (P := fun e' => ∃ ok, e' = ⟨2144, .wait
      ((Bar.storeEmpty (stage2 t)).loc L (g / L.block)) ((t / 2 + 1) % 2) ok true .cta⟩) hf
    (noWiden _) (readBits_b32 r2 (by omega)) hm
    (fun ok => ⟨ok, by rw [par_toNat (by omega)]; rfl⟩)

/-- **The second poll**: of the "full" mbarrier of the tile's input stage. -/
theorem ev_pollF (hpre : Pre P L mem0) (h : Tile P L g t 1 w p x)
    (hat : (code L g).AtD ⟨.mbarWait 8, w, p, x⟩ tt)
    (hc : kernel.code[(Site.mbarWait 8).pc]? = some ins)
    (hf : Fires (Site.mbarWait 8).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    ∃ ok, e = ⟨2186, .wait ((Bar.loadFull (stage3 t)).loc L (g / L.block))
      (t / 3 % 2) ok true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1156) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 2107) (by lit_mem) (n := 32) rfl
  dsimp only at r1 r2
  rw [show w 1156 = W (P.sharedBase + 8 * (t % 3) + 98304) from h.regs 1156 (by decide)] at r1
  rw [show w 2107 = W (t / 3 % 2) from h.regs 2107 (by decide)] at r2
  have hm := mbarLoc_b32 (L := L) (g := g) r1 (by omega) (by omega)
  rw [loc_loadFull hpre t] at hm
  exact shape_wait (P := fun e' => ∃ ok, e' = ⟨2186, .wait
      ((Bar.loadFull (stage3 t)).loc L (g / L.block)) (t / 3 % 2) ok true .cta⟩) hf
    (noWiden _) (readBits_b32 r2 (by omega)) hm
    (fun ok => ⟨ok, by rw [par_toNat (by omega)]; rfl⟩)

/-- **The named barrier**: barrier 8 with thread count 128. -/
theorem ev_bar8 (hpre : Pre P L mem0) (h : Tile P L g t 264 w p x)
    (hat : (code L g).AtD ⟨.bar 6, w, p, x⟩ tt)
    (hc : kernel.code[(Site.bar 6).pc]? = some ins)
    (hf : Fires (Site.bar 6).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    e = ⟨2913, .bar 8 (some 128) .sync⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 1921) (by lit_mem) (n := 32) rfl
  have r2 := reg_w hat (r := 1922) (by lit_mem) (n := 32) rfl
  dsimp only at r1 r2
  rw [show w 1921 = W 8 from h.regs 1921 (by decide)] at r1
  rw [show w 1922 = W 128 from h.regs 1922 (by decide)] at r2
  have hb : (BitVec.ofNat 64 128).toNat ≠ L.block := by rw [hpre.block]; decide
  exact shape_barSyncNR (P := fun e' => e' = ⟨2913, .bar 8 (some 128) .sync⟩) hf
    (readBits_b32 r1 (by decide)) (by decide) (readBits_b32 r2 (by decide)) (by decide)
    (by decide) hb rfl

/-- **The proxy fence.** -/
theorem ev_fence (hc : kernel.code[(Site.fenceProxy 2).pc]? = some ins)
    (hf : Fires (Site.fenceProxy 2).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    e = ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  exact shape_fenceProxy
    (P := fun e' => e' = ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩) hf rfl

/-- **The first arrival**: on the "full" mbarrier of the tile's output stage. -/
theorem ev_arriveF (hpre : Pre P L mem0) (h : Tile P L g t 266 w p x)
    (hat : (code L g).AtD ⟨.mbarArrive 4, w, p, x⟩ tt)
    (hc : kernel.code[(Site.mbarArrive 4).pc]? = some ins)
    (hf : Fires (Site.mbarArrive 4).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    e = ⟨2920, .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_w hat (r := 2031) (by lit_mem) (n := 32) rfl
  dsimp only at r1
  rw [show w 2031 = W (P.sharedBase + 8 * (t % 2) + 98352) from h.regs 2031 (by decide)] at r1
  have hm := mbarLoc_b32 (L := L) (g := g) r1 (by omega) (by omega)
  rw [loc_storeFull hpre t] at hm
  exact shape_arrive (P := fun e' => e' = ⟨2920, .arrive
    ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true .cta⟩) hf (noWiden _) rfl rfl hm rfl

/-- An arrival through a `shared::cluster` address (the form of instruction 2928), at a site
where no assumption widens its scope: the object the address names, with the instruction's
byte count, arrival count, release flag and scope. -/
theorem fires_arrive_cluster {base pc : Nat} {off : Int} {tx count : Opnd} {rel : Bool}
    {sc : MbarScope} {st : Option Nat} {m : Loc} {b n : BitVec 64}
    (hm : mbarClusterLoc L g tt base off = .ok m) (hb : readBits L g tt 32 tx = .ok b)
    (hn : readBits L g tt 32 count = .ok n)
    (hf : Fires pc (eventTmpl Assumptions.all L g tt
      (.mbarArrive base off tx count true rel sc st)) e o) :
    e = ⟨pc, .arrive m b.toNat n.toNat rel sc⟩ := by
  simp only [eventTmpl, widenMbarScope, noWiden, Bool.false_eq_true, ↓reduceIte, tmaTmpl, hm, hb,
    hn, bind, Except.bind, pure, Except.pure, ofExec] at hf
  simp only [Fires] at hf
  exact hf.1

/-- An opaque register that is live at a state's site holds the file's slot. -/
theorem reg_x {d : D} (hat : (code L g).AtD d tt) {r : Nat} (hr : r ∈ Flow.live d.site.pc)
    (hk : isOpaque r = true) : tt.regs r = some (d.x r) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h, valueOf_opaque hk]

/-- **The second arrival**: on the "empty" mbarrier of the tile's input stage, through the
pointer that `mapa` returned. -/
theorem ev_arriveE (hpre : Pre P L mem0) (hg : g < L.threads) (h : Tile P L g t 267 w p x)
    (hat : (code L g).AtD ⟨.mbarArrive 5, w, p, x⟩ tt)
    (hc : kernel.code[(Site.mbarArrive 5).pc]? = some ins)
    (hf : Fires (Site.mbarArrive 5).pc (eventTmpl Assumptions.all L g tt ins.op) e o) :
    e = ⟨2928, .arrive ((Bar.loadEmpty (stage3 t)).loc L (g / L.block)) 0 1 true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have r1 := reg_x hat (r := 3434) (by lit_mem) rfl
  dsimp only at r1
  rw [h.rem rfl] at r1
  have hcta : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := tt) (base := 3434) (cta := g / L.block)
    (a := P.sharedBase + 8 * (t % 3) + 98328) r1 hg hcta rfl (by omega) (by omega)
  rw [loc_loadEmpty hpre t] at hm
  exact fires_arrive_cluster (b := truncBits 32 (BitVec.ofInt 64 0))
    (n := truncBits 32 (BitVec.ofInt 64 1)) hm rfl rfl hf

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
