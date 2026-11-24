-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TmplOkSync
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.Events
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # Further instructions whose event is not undefined behaviour

A proof tool, beside `UbStop` and `TmplOkSync`: a named barrier with an immediate or register id
below 16 and an immediate count that is a nonzero multiple of the warp size (`bar_ok`,
`barReg_ok`); a poll whose barrier and parity evaluate (`wait_loc_ok`); an arrival whose barrier,
byte count and count evaluate (`arrive_loc_ok`); a scalar shared store of a 4-byte register to an
aligned address (`st_ok`); a `tcgen05.st` of a supported address whose sources hold 4-byte values
(`tcSt_ok`, with `mapM_regs_ok` for the sources); and the implicit wait after a `tcgen05.ld`
(`tcLdWait_ok`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- A named barrier with immediates `id < 16` and a nonzero count multiple of 32. -/
theorem bar_ok {id n : Nat} {al : Bool} (hid : id < 16) (hn : n < 2 ^ 31) (hn32 : n % 32 = 0)
    (hn0 : n ≠ 0) (f : Fault) :
    eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al) ≠ .ub f ∧
      eventTmpl A L g t (.barArrive (.imm id) (.imm n) al) ≠ .ub f := by
  have hid' : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp [truncBits]; omega
  have hn' : (truncBits 32 (BitVec.ofInt 64 (n : Int))).toNat = n := by
    simp [truncBits]; omega
  constructor <;>
  · simp only [eventTmpl, barTmpl, readBits, pure, Except.pure, hid', hn']
    simp [show ¬ 16 ≤ id by omega, hn32, hn0]

/-- A named barrier arrival with the id in a register (below 16) and an immediate nonzero count
multiple of 32. -/
theorem barReg_ok {r id n : Nat} {al : Bool} (hr : t.regs r = some (b32 id)) (hid : id < 16)
    (hn : n < 2 ^ 31) (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (f : Fault) :
    eventTmpl A L g t (.barArrive (.reg r) (.imm n) al) ≠ .ub f := by
  simp only [eventTmpl, barTmpl, readBits_b32' hr]
  simp only [readBits, pure, Except.pure, truncBits, BitVec.toNat_ofNat]
  split_ifs <;> simp_all <;> omega

/-- A poll whose barrier and parity evaluate. -/
theorem wait_loc_ok {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    {m : Loc} {q : BitVec 64} (hm : mbarLoc L g t base off = .ok m)
    (hq : readBits L g t 32 par = .ok q) (f : Fault) :
    eventTmpl A L g t (.mbarWait p base off par acq sc) ≠ .ub f :=
  not_ub_of_fires (pc := 0) (fun f hf => by
    obtain ⟨_, _, _, he, -⟩ := fires_wait_at hm hq hf
    cases he) f

/-- An arrival whose barrier, byte count and count evaluate. -/
theorem arrive_loc_ok {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool}
    {sc : MbarScope} {m : Loc} {bytes n : BitVec 64}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hb : readBits L g t 32 tx = .ok bytes) (hn : readBits L g t 32 count = .ok n) (f : Fault) :
    eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc none) ≠ .ub f :=
  not_ub_of_fires (pc := 0) (fun f hf => by
    obtain ⟨_, _, he⟩ := fires_arrive_state_at hm hb hn hf
    cases he) f

/-- A scalar shared store of a 4-byte register to an aligned address, at its first element. -/
theorem st_ok {base a off r : Nat} {v : Value} {ik : IType} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (hal : (a + off) % 4 = 0) (hs : t.sub = 0)
    (hv : t.regs r = some v) (hb : v.bytes = 4) (f : Fault) :
    eventTmpl A L g t (.mem { kind := .store, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, addr := ⟨.reg base 32, (off : Int)⟩,
                              srcs := [.reg r] }) ≠ .ub f := by
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl)
    rfl rfl rfl (by simp)]
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind, elemAcc, hs]
  simp [hal, readValue, readReg, hv, storeValue_of_bytes (w := 32) (by simpa using hb), pure,
    Except.pure]

/-- A `tcgen05.st` of 16 sources at a supported address, every source holding a 4-byte value. -/
theorem tcSt_ok {ta a : Nat} {ss : List Opnd} {sh : TcShape} {vals : List Value}
    (hb : L.block % 32 = 0) (hn : sh.countOk ss.length = true) (hr : t.regs ta = some (b32 a))
    (ha : a < 2 ^ 32) (hs : tcDataAddressOk L g sh a = true)
    (hv : ss.mapM (readValue L g t 32) = .ok vals) (h4 : vals.all (·.bytes = 4) = true)
    (f : Fault) : eventTmpl A L g t (.tcSt ta ss sh) ≠ .ub f := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  have hstore (u : TState) (hu : u.regs = t.regs) : tcTmpl L g u (.tcSt ta ss sh) ≠ .ub f := by
    have hru : u.regs ta = some (b32 a) := by rw [hu, hr]
    have her : readValue L g u 32 = readValue L g t 32 := by
      funext o
      cases o <;> simp only [readValue, readBits, readReg, hu]
    have hvu : ss.mapM (readValue L g u 32) = .ok vals := by rw [her, hv]
    cases sh with
    | packed16 s =>
      have hn' : s.countOk ss.length = true := by
        simpa [TcShape.countOk, TcShape.regs] using hn
      simp only [tcTmpl]
      rw [hn']
      simp [hb, readBits_b32' hru, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
        Nat.mod_eq_of_lt h64, hs, hvu, h4, ofExec, bind, Except.bind, pure, Except.pure]
    | _ =>
      simp only [tcTmpl]
      rw [hn]
      simp [hb, readBits_b32' hru, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
        Nat.mod_eq_of_lt h64, hs, hvu, h4, ofExec, bind, Except.bind, pure, Except.pure]

  simp only [eventTmpl, tcStTmpl]
  split
  · split
    · simp
    · exact hstore _ rfl
  · exact hstore _ rfl

/-- The implicit wait after a `tcgen05.ld`, at its second sub-step. -/
theorem tcLdWait_ok {ds : List Nat} {ta : Nat} {sh : TcShape} (hw : A.any (·.tcLdWait t.pc) = true)
    (hs : t.sub ≠ 0) (f : Fault) : eventTmpl A L g t (.tcLd ds ta sh) ≠ .ub f := by
  simp [eventTmpl, tcLdTmpl, hw, hs]

/-- Sources that are registers, each holding a 4-byte value, read as values of 4 bytes. -/
theorem mapM_regs_ok :
    ∀ {ss : List Opnd}, (∀ p < ss.length, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = 4) →
      ∃ vals, ss.mapM (readValue L g t 32) = .ok vals ∧ vals.all (·.bytes = 4) = true
  | [], _ => ⟨[], rfl, rfl⟩
  | o :: ss, h => by
    obtain ⟨r, v, h0, hv, hb⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    obtain ⟨vals, hm, ha⟩ := mapM_regs_ok (ss := ss) fun p hp => by
      obtain ⟨r', v', h1, h2, h3⟩ := h (p + 1) (by simp; omega)
      exact ⟨r', v', by simpa using h1, h2, h3⟩
    refine ⟨v :: vals, ?_, ?_⟩
    · simp [List.mapM_cons, readValue, readReg, hv, hm, bind, Except.bind, pure, Except.pure]
    · simp [hb, ha]

end
end PTX.Flow
