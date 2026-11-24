-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.Fire
public import Lemmas.Flow.Final
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.Next
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Events
public import Lemmas.Flow.TmemOperands
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.RoleTemplates
public import Lemmas.Flow.Async
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # Inversion lemmas for more instruction classes (`site_shape`)

A proof tool. Inversion lemmas in the form `site_shape` applies (`P e` from `P` of the event the
instruction fires, given its operands' values), for classes beyond those of `SiteShape.lean`:

* `shape_barSync` (`bar.sync id` with an immediate id), `shape_barSyncN` and `shape_barArrive`
  (`bar.sync`/`bar.arrive id, n` with immediates);
* `shape_warpBar` (`bar.warp.sync -1`) and `shape_elect` (`elect.sync` with any mask: an election
  of the mask's members, or undefined behaviour);
* `shape_mbInit` (`mbarrier.init` of the shared object its address register names);
* `shape_fenceProxy` (a proxy fence without an address);
* `shape_tcCommit` (`tcgen05.commit` with a mask, at a resolved target);
* `shape_cpTensor` (a TMA tensor copy: its issue event, or undefined behaviour);
* `shape_store` (any store element: a write, or undefined behaviour; the fallback);
* `shape_st` (a weak store located by its address register: the write's address, byte count and
  bytes, from the source's value) and `shape_ldNc` (a `.nc` load so located);
* `shape_accessLd`, `shape_accessSt` (an access that `memTmpl` gives to `accessTmpl`: a `.local`
  access, a `.shared` variable);
* `shape_tcCommitOne` (`tcgen05.commit` without a mask);
* `shape_tcAlloc`, `shape_tcAllocWr` (the request and the address store of `tcgen05.alloc` into
  a 32-bit shared address) and `shape_tcRelinquish` (from Inkling's `Proof/Lib/Shape.lean`; through
  the hook `shape_inv`, since the sub-step selects the lemma);
* `mbarLoc_b32_ok` (the aligned mbarrier location of a register holding a 32-bit shared address,
  a side condition of `shape_wait` and `shape_arrive`), and `OrUb S` (a shape table with
  undefined behaviour admitted at every site) with `OrUb.of_some`;
* `shape_cont`: the event of an instruction that is not an exit, from its continuing events,
  or undefined behaviour.

`site_shape` (`Step/SiteShape.lean`) tries these by the instruction's class, and any class
beyond them through its hook `shape_inv hf`. The Inkling lemmas `fires_elect_full`,
`fires_warpBar_full`, `fires_barSync1` (`fires_barSync_imm`) and `fires_mbInit_at` are special
cases of the first lemmas. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState} {P : Event → Prop}

/-- From an equation that names the event. -/
theorem shape_of_eq {E : Event} (h : e = E) (hP : P E) : P e := h ▸ hP

/-- `bar.sync id` with an immediate id, no count. -/
theorem shape_barSync {id : Nat} {al : Bool}
    (hf : Fires pc (eventTmpl A L g t (.barSync (.imm id) al)) e o) (hid : id < 16)
    (hP : P ⟨pc, .bar id none .sync⟩) : P e := by
  have himm : readBits L g t 32 (Opnd.imm (id : Int)) = .ok (BitVec.ofNat 64 id) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, himm, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), show ¬ 16 ≤ id by omega, ↓reduceIte] at hf
  rw [hf.1]
  exact hP

/-- `bar.sync id, n` with immediates. -/
theorem shape_barSyncN {id n : Nat} {al : Bool}
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al)) e o) (hid : id < 16)
    (hn : n < 2 ^ 32) (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hP : P ⟨pc, .bar id (some n) .sync⟩) : P e :=
  shape_of_eq (fires_barSyncN_imm hid hn hn32 hn0 hnb hf) hP

/-- `bar.warp.sync -1`: the full-mask warp barrier, or undefined behaviour (a lane outside the
mask, which the full mask excludes). -/
theorem shape_warpBar
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩)) e o)
    (hP : ∀ inst, P ⟨pc, .warpBar 4294967295 inst⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  simp only [eventTmpl, warpTmpl_barWarp, warpBarTmpl, readBits, pure, Except.pure] at hf
  have h1 : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 := by decide
  rw [h1] at hf
  by_cases hm : electMember 4294967295 (laneOf L g)
  · simp only [hm, ↓reduceIte, Fires] at hf
    obtain ⟨inst, he, -⟩ := hf
    rw [he]; exact hP inst
  · simp only [hm, ↓reduceIte, Fires] at hf
    rw [hf.1]; exact hub _

/-- `elect.sync` whose mask reads as `bits`: an election of the mask's members, or undefined
behaviour. -/
theorem shape_elect {dst : Option Nat} {p : Nat} {mask : Opnd} {bits : BitVec 64}
    {ty : Option DType}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) e o)
    (hm : readBits L g t 32 mask = .ok bits)
    (hP : ∀ inst leader, P ⟨pc, .elect bits.toNat inst leader⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) :
    P e := by
  rcases fires_elect_mask hm hf with ⟨inst, leader, rfl⟩ | ⟨f, rfl⟩
  · exact hP inst leader
  · exact hub f

/-- `mbarrier.init` of the shared object its address register names, with an immediate count. -/
theorem shape_mbInit {r a n : Nat}
    (hf : Fires pc (eventTmpl A L g t (.mbarInit r 0 (.imm n))) e o)
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hn : 0 < n) (hn' : n < 2 ^ 20)
    (hal : a % 8 = 0) (hP : P ⟨pc, .mbInit ⟨.shared, g / L.block, a⟩ n⟩) : P e := by
  have hi := tma_mbarInit (L := L) (g := g) (t := t) hr ha hal hn hn'
  simp only [eventTmpl, hi, widenMbarScope] at hf
  split_ifs at hf <;> (rw [hf.1]; exact hP)

/-- `mbarrier.init` with the count in a register (tml-fa4's startup, FlashMLA's G6): an
initialization of the aligned object at the address register with the register's count. -/
theorem shape_mbInitR {r c a n : Nat}
    (hf : Fires pc (eventTmpl A L g t (.mbarInit r 0 (.reg c))) e o)
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hc : t.regs c = some (b32 n))
    (hn : 0 < n) (hn' : n < 2 ^ 20) (hal : a % 8 = 0)
    (hP : P ⟨pc, .mbInit ⟨.shared, g / L.block, a⟩ n⟩) : P e := by
  have hi : tmaTmpl L g t (.mbarInit r 0 (.reg c)) =
      .mbInit ⟨.shared, g / L.block, a⟩ n (next t) := by
    simp only [tmaTmpl, Flow.mbarLoc_b32 hr ha hal, readBits_b32 hc (by omega), bind,
      Except.bind, Proof.toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
    have h20 : n < 1048576 := by simpa using hn'
    simp [ofExec, hn, h20, pure, Except.pure]
  simp only [eventTmpl, hi, widenMbarScope] at hf
  split_ifs at hf <;> (rw [hf.1]; exact hP)

/-- `mbarrier.init` with any count operand and address (promoted from the tml-fa4 startup's
`Proof2/Lib/ShapeInit.lean`): an initialization of some object with some count, or undefined
behaviour. `site_shape` tries it when `shape_mbInit` (an immediate count and an aligned address
read from the site's facts) does not apply. -/
theorem shape_mbInitAny {b : Nat} {off : Int} {c : Opnd}
    (hf : Fires pc (eventTmpl A L g t (.mbarInit b off c)) e o)
    (hP : ∀ l n, P ⟨pc, .mbInit l n⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t) (.mbarInit b off c) with
    ⟨f, h⟩ | ⟨l, n, t', h⟩ <;> rw [h] at hf <;> simp only [Fires] at hf <;> rw [hf.1]
  · exact hub f
  · exact hP l n

/-- A proxy fence without an address. -/
theorem shape_fenceProxy {k : ProxyFence} {scope : Option MbarScope}
    (hf : Fires pc (.fenceProxy k scope (PTX.next t)) e o) (hP : P ⟨pc, .fenceProxy k scope⟩) :
    P e :=
  shape_of_eq (fires_fenceProxy hf).1 hP

/-- `tcgen05.commit` with a mask, at the target it resolves to. -/
theorem shape_tcCommit {group : CtaGroup} {base : Nat} {off : Int} {mk : Opnd} {m : Loc}
    {k : BitVec 64} {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off (some mk))) e o)
    (hg : g < L.threads) (hm : mbarClusterLoc L g t base off = .ok m)
    (hk : readBits L g t 16 mk = .ok k)
    (hs : TcCommit.resolve L group (g / L.block) m (BitVec.ofNat 16 k.toNat) = some s)
    (hP : P ⟨pc, .tc (.commit s)⟩) : P e :=
  shape_of_eq (fires_tcCommit_at hg hm hk hs hf).1 hP

/-- The event of an instruction other than an exit: one that continues the thread, or undefined
behaviour. -/
theorem shape_cont {op : Op} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hop : op ≠ .ret ∧ op ≠ .exit) (hs : ∀ u, Fires pc (eventTmpl A L g t op) e (some u) → P e)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  cases o with
  | some u => exact hs u hf
  | none =>
    have hpc := fires_pc hf
    rcases fires_none_ends hf with ⟨f, hk⟩ | hk
    · obtain ⟨epc, k⟩ := e
      simp only at hk hpc
      subst hk hpc
      exact hub f
    · rcases fires_exit_op hf hk with h | h
      · exact absurd h hop.1
      · exact absurd h hop.2

/-- A TMA tensor copy (no multicast): its issue event on the barrier its operands name, or
undefined behaviour. -/
theorem shape_cpTensor {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e o)
    (hP : ∀ a s, (if ca then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff) =
      .ok s.mbar → P ⟨pc, .tensorIssue a s⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨a, s, rfl, -, hm⟩ := fires_cpTensor_issue hf'
    exact hP a s hm) hub

/-- An element of a store: a write, or undefined behaviour. -/
theorem shape_store {a : MemAccess}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) (hk : a.kind = .store)
    (hP : ∀ r bs, P ⟨pc, .wr r bs⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨r, bs, rfl, -⟩ := fires_st hk hf'
    exact hP r bs) hub

/-- A `cp.async` copy whose addresses and source size read as `d`, `s` and `n`: its copy event of
the non-bulk asynchronous group, or undefined behaviour (a misaligned address, a cache policy that
does not read). -/
theorem shape_cpAsync {db sb size n : Nat} {doff soff : Int} {source : CpAsyncSource}
    {policy : Option Opnd} {d s : Loc}
    (hf : Fires pc (eventTmpl A L g t (.cpAsync db doff sb soff size source policy)) e o)
    (hd : effAddr L g t .shared db doff = .ok d) (hs : effAddr L g t .global sb soff = .ok s)
    (hn : cpAsyncSourceSize L g t size source = .ok n)
    (hP : P ⟨pc, .copy ⟨{ loc := s, size := n }, { loc := d, size := size }, .asyncGroup, .whole,
      none, true, none⟩⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  simp only [eventTmpl, cpAsyncTmpl, hd, hs, hn, bind, Except.bind] at hf
  repeat' split at hf
  all_goals first
    | (simp only [ofExec, Fires] at hf; rw [hf.1]; exact hub _)
    | (simp only [ofExec, Fires, pure, Except.pure] at hf; rw [hf.1]; exact hP)

/-- `cp.async.commit_group`. -/
theorem shape_cpAsyncCommit (hf : Fires pc (eventTmpl A L g t .cpAsyncCommit) e o)
    (hP : P ⟨pc, .asyncCommit⟩) : P e := by
  simp only [eventTmpl, cpAsyncTmpl, Fires] at hf
  rw [hf.1]
  exact hP

/-- `cp.async.mbarrier.arrive` on a `.shared` address (not generic) that reads as `m`: its
arrival, or undefined behaviour. -/
theorem shape_cpAsyncArrive {noinc : Bool} {base : Nat} {off : Int} {m : Loc}
    (hf : Fires pc (eventTmpl A L g t (.cpAsyncArrive noinc base off false)) e o)
    (hm : mbarLoc L g t base off = .ok m) (hP : P ⟨pc, .asyncArrive m noinc⟩) : P e := by
  simp only [eventTmpl, cpAsyncTmpl, hm, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
    pure, Except.pure, ofExec, Fires] at hf
  rw [hf.1]
  exact hP

/-- A load that `memTmpl` gives to `accessTmpl` (`hT`, which is `rfl` for a literal access: one
that no direct location rule covers, as a `.local` access or a `.shared` variable, or a direct
one of another semantics than weak, acquire or release), without `.nc`, whose footprint reads as
`acc`: a read of `acc` of `acc.size` bytes. -/
theorem shape_accessLd {a : MemAccess} {acc : Acc}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) (hT : memTmpl A L g t a = accessTmpl A L g t a)
    (hk : a.kind = .load) (hnc : a.nc = false) (hacc : accessAcc L g t a = .ok acc)
    (hP : ∀ bs : List (Option Byte), bs.length = acc.size → P ⟨pc, .rd acc bs⟩) : P e := by
  have hA : accessTmpl A L g t a = .read acc (afterAccessLoad t a.ext a.elem.width a.regs) := by
    simp [accessTmpl, hk, hacc, hnc]
  have hE : eventTmpl A L g t (.mem a) = memTmpl A L g t a := rfl
  rw [hE, hT, hA] at hf
  obtain ⟨bs, hl, rfl, -⟩ := hf
  exact hP bs hl

/-- A store element that `memTmpl` gives to `accessTmpl`, whose footprint reads as `acc` and
whose source (element `j`, the sub-step) reads as `v`: a write of `acc` with the bytes of
`storeValue` of `v`, or undefined behaviour. -/
theorem shape_accessSt {a : MemAccess} {acc : Acc} {j : Nat} {src : Opnd} {v : Value}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) (hT : memTmpl A L g t a = accessTmpl A L g t a)
    (hk : a.kind = .store) (hacc : accessAcc L g t a = .ok acc) (hs : t.sub = j)
    (hsrc : a.srcs[j]? = some src) (hv : readValue L g t a.elem.width src = .ok v)
    (hP : ∀ v', storeValue a.elem.width v = .ok v' → P ⟨pc, .wr acc v'.toBytes⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  have hE : eventTmpl A L g t (.mem a) = memTmpl A L g t a := rfl
  rw [hE, hT] at hf
  subst hs
  simp only [accessTmpl, hk, hacc, hsrc, hv, bind, Except.bind] at hf
  split at hf
  · rw [hf.1]; exact hub _
  · rename_i v' hv'
    rw [hf.1]; exact hP v' hv'

/-- An element of a weak store located by its address register (`storeTmpl`): a write of the
element's `w / 8` bytes at the effective address, whose bytes are `storeValue` of the value its
source reads, or undefined behaviour (a misaligned address, a source of the wrong size). -/
theorem shape_st {sp : Space} {w base j : Nat} {off : Int} {srcs : List Opnd} {loc : Loc}
    {src : Opnd} {v : Value} (hf : Fires pc (storeTmpl L g t sp w base off srcs) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j) (hsrc : srcs[j]? = some src)
    (hv : readValue L g t w src = .ok v)
    (hwr : ∀ v', storeValue w v = .ok v' →
      P ⟨pc, .wr { loc := loc.at (w / 8 * j), size := w / 8, elem := j } v'.toBytes⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  subst hs
  simp only [storeTmpl, hea, elemAcc, bind, Except.bind] at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    rw [hf.1]; exact hub _
  · simp only [pure, Except.pure, hsrc, hv] at hf
    split at hf
    · rw [hf.1]; exact hub _
    · rename_i v' hv'
      rw [hf.1]; exact hwr v' hv'

/-- `shape_st` with the conditions of its undefined behaviour kept: the element's write, or
undefined behaviour only when the access is misaligned (Core's `elemAcc`) or the source value does
not convert to the store's width (`storeValue`). A role whose reference invariant gives the
alignment and the value's width discharges its `ref_safe` at the site. -/
theorem shape_stM {sp : Space} {w base j : Nat} {off : Int} {srcs : List Opnd} {loc : Loc}
    {src : Opnd} {v : Value} (hf : Fires pc (storeTmpl L g t sp w base off srcs) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j) (hsrc : srcs[j]? = some src)
    (hv : readValue L g t w src = .ok v)
    (hwr : ∀ v', storeValue w v = .ok v' →
      P ⟨pc, .wr { loc := loc.at (w / 8 * j), size := w / 8, elem := j } v'.toBytes⟩)
    (hmis : w / 8 = 0 ∨ loc.addr % (w / 8 * srcs.length) ≠ 0 → P ⟨pc, .ub .misaligned⟩)
    (hval : ∀ f, storeValue w v = .error f → P ⟨pc, .ub f⟩) : P e := by
  subst hs
  simp only [storeTmpl, hea, elemAcc, bind, Except.bind] at hf
  split_ifs at hf with hm
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    rw [hf.1]; exact hmis hm
  · simp only [pure, Except.pure, hsrc, hv] at hf
    split at hf
    · rename_i f hf'
      rw [hf.1]; exact hval f hf'
    · rename_i v' hv'
      rw [hf.1]; exact hwr v' hv'

/-- An element of a `.nc` load located by its address register: a non-coherent read of the
element's `w / 8` bytes at the effective address when an assumption admits `.nc` at the
instruction, or undefined behaviour. -/
theorem shape_ldNc {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {loc : Loc}
    {j : Nat} (hf : Fires pc (loadTmpl A L g t sp true w ds base off) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j)
    (hrd : ∀ bs : List (Option Byte), bs.length = w / 8 →
      P ⟨pc, .nc { loc := loc.at (w / 8 * j), size := w / 8, elem := j } bs⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  subst hs
  simp only [loadTmpl, hea, elemAcc, bind, Except.bind, ↓reduceIte] at hf
  split_ifs at hf
  all_goals simp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, Fires] at hf
  all_goals first
    | (obtain ⟨bs, hl, rfl, -⟩ := hf; exact hrd bs hl)
    | (rw [hf.1]; exact hub _)

/-- An element of a `.nc` load located by its address register, with the condition of its
undefined behaviour kept (`shape_ldNc` in `shape_stM`'s form; FlashMLA request G25): where the
instruction has the `.nc` rule, the non-coherent read, or a misaligned access. -/
theorem shape_ldNcM {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {loc : Loc}
    {j : Nat} (hf : Fires pc (loadTmpl A L g t sp true w ds base off) e o)
    (hea : effAddr L g t sp base off = .ok loc) (hs : t.sub = j)
    (hnc : sp = .global ∧ A.any (·.ncLoads t.pc) = true)
    (hrd : ∀ bs : List (Option Byte), bs.length = w / 8 →
      P ⟨pc, .nc { loc := loc.at (w / 8 * j), size := w / 8, elem := j } bs⟩)
    (hmis : w / 8 = 0 ∨ loc.addr % (w / 8 * ds.length) ≠ 0 → P ⟨pc, .ub .misaligned⟩) :
    P e := by
  subst hs
  obtain ⟨rfl, hn⟩ := hnc
  simp only [loadTmpl, hea, elemAcc, bind, Except.bind, hn, and_self, ↓reduceIte] at hf
  split_ifs at hf with hm
  all_goals simp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, Fires] at hf
  · rw [hf.1]; exact hmis hm
  · obtain ⟨bs, hl, rfl, -⟩ := hf; exact hrd bs hl

/-- `tcgen05.commit` without a mask: the commit to the addressed CTA alone, at the target it
resolves to. -/
theorem shape_tcCommitOne {group : CtaGroup} {base : Nat} {off : Int} {m : Loc}
    {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off none)) e o)
    (hg : g < L.threads) (hm : mbarClusterLoc L g t base off = .ok m)
    (hs : TcCommit.resolve L group (g / L.block) m (BitVec.ofNat 16 (2 ^ L.rankOfCta m.cta)) =
      some s)
    (hP : P ⟨pc, .tc (.commit s)⟩) : P e := by
  simp only [eventTmpl, tcCommitTmpl, hg, ↓reduceIte, hm, hs, bind, Except.bind, pure,
    Except.pure, ofExec, Fires] at hf
  rw [hf.1]
  exact hP

/-- A shape table with undefined behaviour admitted at every site. -/
def OrUb {D : Type} (S : D → Event → Prop) (d : D) (e : Event) : Prop :=
  S d e ∨ ∃ f, e.kind = .ub f

/-- At an event that continues, a shape of `OrUb S` is one of `S`. -/
theorem OrUb.of_some {D : Type} {S : D → Event → Prop} {d : D} {m : Tmpl} {u : TState}
    (h : OrUb S d e) (hf : Fires pc m e (some u)) : S d e := by
  rcases h with h | ⟨f, hk⟩
  · exact h
  · obtain rfl := fires_ub hf hk
    exact absurd hf.2 (by simp)

/-- The allocation request of `tcgen05.alloc` (sub-step 0) into the shared word at register `r`. -/
theorem shape_tcAlloc {group : CtaGroup} {r a : Nat} {nc : Opnd} {n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group r 0 nc)) e o) (hs : t.sub = 0)
    (hr : t.regs r = some (b32 a)) (hn : readBits L g t 32 nc = .ok n)
    (hb : L.block % 32 = 0) (ha : a < 2 ^ 32) (hal : a % 4 = 0)
    (hv : Tmem.validColumns n.toNat = true)
    (hP : P ⟨pc, .tc (.resource group (some ⟨.shared, g / L.block, a⟩) (.alloc n.toNat))⟩) :
    P e := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, hn, hb, hal, hv, hs, bind, Except.bind,
    pure, Except.pure, ofExec] at hf
  simp only [↓reduceIte, Fires] at hf
  rw [hf.1]
  exact hP

/-- The store of the allocated address (sub-step 1 of `tcgen05.alloc`): four bytes of a 32-bit
word below `2 ^ 16` at the shared word of register `r`. -/
theorem shape_tcAllocWr {group : CtaGroup} {r a : Nat} {nc : Opnd} {n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group r 0 nc)) e o) (hs : t.sub = 1)
    (hr : t.regs r = some (b32 a)) (hn : readBits L g t 32 nc = .ok n)
    (hb : L.block % 32 = 0) (ha : a < 2 ^ 32) (hal : a % 4 = 0)
    (hv : Tmem.validColumns n.toNat = true)
    (hP : ∀ col, col < 2 ^ 16 →
      P ⟨pc, .wr { loc := ⟨.shared, g / L.block, a⟩, size := 4 } (b32 col).toBytes⟩) :
    P e := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, hn, hb, hal, hv, hs, bind, Except.bind,
    pure, Except.pure, ofExec] at hf
  simp only [↓reduceIte, Nat.one_ne_zero, Fires] at hf
  obtain ⟨col, hcol, he, -⟩ := hf
  rw [he]
  exact hP col hcol

/-- `tcgen05.relinquish_alloc_permit`. -/
theorem shape_tcRelinquish {group : CtaGroup}
    (hf : Fires pc (eventTmpl A L g t (.tcRelinquish group)) e o) (hb : L.block % 32 = 0)
    (hP : P ⟨pc, .tc (.resource group none .relinquish)⟩) : P e := by
  simp only [eventTmpl, tcTmpl, hb, pure, Except.pure, ofExec, ↓reduceIte, Fires] at hf
  rw [hf.1]
  exact hP

/-- The aligned mbarrier location of a register holding a 32-bit shared address. -/
theorem mbarLoc_b32_ok {r a : Nat} (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32)
    (hal : a % 8 = 0) : mbarLoc L g t r 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  simp [mbarLoc, effAddr_b32 hr ha, hal, bind, Except.bind, pure, Except.pure]

end

end PTX.Flow
