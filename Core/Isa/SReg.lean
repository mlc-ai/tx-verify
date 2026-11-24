-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Isa.Grammar
public import Core.Isa.Rule

@[expose] public section

/-!
# Special registers

The predefined read-only registers of §10, by name and component.
-/

namespace PTX

/-! ## PROG-ISA-SREG — special registers
Statement: A special register operand is one of the predefined registers of §10, with its component
  `.x`, `.y` or `.z` for the vector registers, and it has the width of its declared type. Any other
  name is an ordinary register name.

Defs: Dim, SRegName, SReg, SReg.width, SReg.table, SReg.bytesEq, SReg.lookup, SReg.ofName?,
  SRegKind, SReg.kind, SReg.varying, SReg.perCtaMemory, SReg.rule

Source:
- §10 (Special Registers): "Syntax (predefined) .sreg .v4 .u32 %tid; // thread id vector .sreg .u32
    %tid.x, %tid.y, %tid.z; // thread id components"
- §10 (Special Registers): ".sreg .pred %is_explicit_cluster;"
- §10 (Special Registers): ".sreg .u64 %clock64;"
- §10 (Special Registers): ".sreg .u64 %globaltimer;"
- §10 (Special Registers): ".sreg .u64 %gridid;"
- §10 (Special Registers): ".sreg .u64 %current_graph_exec;"
- §10 (Special Registers): ".sreg .u64 %perctamemoryoffset;"
- §10 (Special Registers): ".sreg .b32 %envreg<32>;"

Direction: representation

Applies: Every special register operand of a decoded instruction

Premises: The name is spelled as in §10.

Effect: Representation; `SReg.kind` says how THREAD-SREG gives a register its value, and
  `SReg.rule` names THREAD-SREG exactly for the registers that have a kind. A `%perctamemory`
  register decodes only in a kernel with a `.minperctamemory` directive (PROG-DECODE).
-/

/-- A component of a vector special register. -/
inductive Dim where
  | x | y | z
  deriving DecidableEq, Repr

/-- The special registers of §10. -/
inductive SRegName where
  | tid | ntid | laneid | warpid | nwarpid | ctaid | nctaid | smid | nsmid | gridid
  | isExplicitCluster | clusterid | nclusterid | clusterCtaid | clusterNctaid | clusterCtarank
  | clusterNctarank | lanemaskEq | lanemaskLe | lanemaskLt | lanemaskGe | lanemaskGt
  | clock | clockHi | clock64 | pm (i : Nat) | pm64 (i : Nat) | envreg (i : Nat)
  | globaltimer | globaltimerLo | globaltimerHi | reservedSmemOffsetBegin
  | reservedSmemOffsetEnd | reservedSmemOffsetCap | reservedSmemOffset (i : Nat)
  | totalSmemSize | aggrSmemSize | dynamicSmemSize | currentGraphExec | perctamemoryoffset
  | perctamemorysize | localityDomainId | localityDomainSupplementalSm
  deriving DecidableEq, Repr

/-- A special register operand: its name and, for a vector register, the component. -/
structure SReg where
  name : SRegName
  dim : Option Dim := none
  deriving DecidableEq, Repr

/-- The width of the declared type of a special register (§10). -/
def SReg.width (s : SReg) : Nat :=
  match s.name with
  | .isExplicitCluster => 1
  | .clock64 | .pm64 _ | .globaltimer | .gridid | .currentGraphExec | .perctamemoryoffset => 64
  | _ => 32

/-- The spellings of the special registers: the bytes after the leading `%`. -/
def SReg.table : List (List Nat × SReg) := [
  -- %tid.x,
  ([116,105,100,46,120], ⟨.tid, some .x⟩),
  -- %tid.y,
  ([116,105,100,46,121], ⟨.tid, some .y⟩),
  -- %tid.z,
  ([116,105,100,46,122], ⟨.tid, some .z⟩),
  -- %ntid.x,
  ([110,116,105,100,46,120], ⟨.ntid, some .x⟩),
  -- %ntid.y,
  ([110,116,105,100,46,121], ⟨.ntid, some .y⟩),
  -- %ntid.z,
  ([110,116,105,100,46,122], ⟨.ntid, some .z⟩),
  -- %ctaid.x,
  ([99,116,97,105,100,46,120], ⟨.ctaid, some .x⟩),
  -- %ctaid.y,
  ([99,116,97,105,100,46,121], ⟨.ctaid, some .y⟩),
  -- %ctaid.z,
  ([99,116,97,105,100,46,122], ⟨.ctaid, some .z⟩),
  -- %nctaid.x,
  ([110,99,116,97,105,100,46,120], ⟨.nctaid, some .x⟩),
  -- %nctaid.y,
  ([110,99,116,97,105,100,46,121], ⟨.nctaid, some .y⟩),
  -- %nctaid.z,
  ([110,99,116,97,105,100,46,122], ⟨.nctaid, some .z⟩),
  -- %clusterid.x,
  ([99,108,117,115,116,101,114,105,100,46,120], ⟨.clusterid, some .x⟩),
  -- %clusterid.y,
  ([99,108,117,115,116,101,114,105,100,46,121], ⟨.clusterid, some .y⟩),
  -- %clusterid.z,
  ([99,108,117,115,116,101,114,105,100,46,122], ⟨.clusterid, some .z⟩),
  -- %nclusterid.x,
  ([110,99,108,117,115,116,101,114,105,100,46,120], ⟨.nclusterid, some .x⟩),
  -- %nclusterid.y,
  ([110,99,108,117,115,116,101,114,105,100,46,121], ⟨.nclusterid, some .y⟩),
  -- %nclusterid.z,
  ([110,99,108,117,115,116,101,114,105,100,46,122], ⟨.nclusterid, some .z⟩),
  -- %cluster_ctaid.x,
  ([99,108,117,115,116,101,114,95,99,116,97,105,100,46,120], ⟨.clusterCtaid, some .x⟩),
  -- %cluster_ctaid.y,
  ([99,108,117,115,116,101,114,95,99,116,97,105,100,46,121], ⟨.clusterCtaid, some .y⟩),
  -- %cluster_ctaid.z,
  ([99,108,117,115,116,101,114,95,99,116,97,105,100,46,122], ⟨.clusterCtaid, some .z⟩),
  -- %cluster_nctaid.x,
  ([99,108,117,115,116,101,114,95,110,99,116,97,105,100,46,120], ⟨.clusterNctaid, some .x⟩),
  -- %cluster_nctaid.y,
  ([99,108,117,115,116,101,114,95,110,99,116,97,105,100,46,121], ⟨.clusterNctaid, some .y⟩),
  -- %cluster_nctaid.z,
  ([99,108,117,115,116,101,114,95,110,99,116,97,105,100,46,122], ⟨.clusterNctaid, some .z⟩),
  -- %laneid,
  ([108,97,110,101,105,100], ⟨.laneid, none⟩),
  -- %warpid,
  ([119,97,114,112,105,100], ⟨.warpid, none⟩),
  -- %nwarpid,
  ([110,119,97,114,112,105,100], ⟨.nwarpid, none⟩),
  -- %smid,
  ([115,109,105,100], ⟨.smid, none⟩),
  -- %nsmid,
  ([110,115,109,105,100], ⟨.nsmid, none⟩),
  -- %gridid,
  ([103,114,105,100,105,100], ⟨.gridid, none⟩),
  -- %is_explicit_cluster,
  ([105, 115, 95, 101, 120, 112, 108, 105, 99, 105, 116, 95, 99, 108, 117, 115, 116, 101, 114],
    ⟨.isExplicitCluster, none⟩),
  -- %cluster_ctarank,
  ([99,108,117,115,116,101,114,95,99,116,97,114,97,110,107], ⟨.clusterCtarank, none⟩),
  -- %cluster_nctarank,
  ([99,108,117,115,116,101,114,95,110,99,116,97,114,97,110,107], ⟨.clusterNctarank, none⟩),
  -- %lanemask_eq,
  ([108,97,110,101,109,97,115,107,95,101,113], ⟨.lanemaskEq, none⟩),
  -- %lanemask_le,
  ([108,97,110,101,109,97,115,107,95,108,101], ⟨.lanemaskLe, none⟩),
  -- %lanemask_lt,
  ([108,97,110,101,109,97,115,107,95,108,116], ⟨.lanemaskLt, none⟩),
  -- %lanemask_ge,
  ([108,97,110,101,109,97,115,107,95,103,101], ⟨.lanemaskGe, none⟩),
  -- %lanemask_gt,
  ([108,97,110,101,109,97,115,107,95,103,116], ⟨.lanemaskGt, none⟩),
  -- %clock,
  ([99,108,111,99,107], ⟨.clock, none⟩),
  -- %clock_hi,
  ([99,108,111,99,107,95,104,105], ⟨.clockHi, none⟩),
  -- %clock64,
  ([99,108,111,99,107,54,52], ⟨.clock64, none⟩),
  -- %globaltimer,
  ([103,108,111,98,97,108,116,105,109,101,114], ⟨.globaltimer, none⟩),
  -- %globaltimer_lo,
  ([103,108,111,98,97,108,116,105,109,101,114,95,108,111], ⟨.globaltimerLo, none⟩),
  -- %globaltimer_hi,
  ([103,108,111,98,97,108,116,105,109,101,114,95,104,105], ⟨.globaltimerHi, none⟩),
  -- %reserved_smem_offset_begin,
  ([114, 101, 115, 101, 114, 118, 101, 100, 95, 115, 109, 101, 109, 95, 111, 102, 102, 115, 101,
    116, 95, 98, 101, 103, 105, 110], ⟨.reservedSmemOffsetBegin, none⟩),
  -- %reserved_smem_offset_end,
  ([114, 101, 115, 101, 114, 118, 101, 100, 95, 115, 109, 101, 109, 95, 111, 102, 102, 115, 101,
    116, 95, 101, 110, 100], ⟨.reservedSmemOffsetEnd, none⟩),
  -- %reserved_smem_offset_cap,
  ([114, 101, 115, 101, 114, 118, 101, 100, 95, 115, 109, 101, 109, 95, 111, 102, 102, 115, 101,
    116, 95, 99, 97, 112], ⟨.reservedSmemOffsetCap, none⟩),
  -- %total_smem_size,
  ([116,111,116,97,108,95,115,109,101,109,95,115,105,122,101], ⟨.totalSmemSize, none⟩),
  -- %aggr_smem_size,
  ([97,103,103,114,95,115,109,101,109,95,115,105,122,101], ⟨.aggrSmemSize, none⟩),
  -- %dynamic_smem_size,
  ([100,121,110,97,109,105,99,95,115,109,101,109,95,115,105,122,101], ⟨.dynamicSmemSize, none⟩),
  -- %current_graph_exec,
  ([99,117,114,114,101,110,116,95,103,114,97,112,104,95,101,120,101,99], ⟨.currentGraphExec, none⟩),
  -- %perctamemoryoffset,
  ([112, 101, 114, 99, 116, 97, 109, 101, 109, 111, 114, 121, 111, 102, 102, 115, 101, 116],
    ⟨.perctamemoryoffset, none⟩),
  -- %perctamemorysize,
  ([112,101,114,99,116,97,109,101,109,111,114,121,115,105,122,101], ⟨.perctamemorysize, none⟩),
  -- %locality_domain_id,
  ([108,111,99,97,108,105,116,121,95,100,111,109,97,105,110,95,105,100], ⟨.localityDomainId, none⟩),
  -- %locality_domain_supplemental_sm,
  ([108, 111, 99, 97, 108, 105, 116, 121, 95, 100, 111, 109, 97, 105, 110, 95, 115, 117, 112, 112,
    108, 101, 109, 101, 110, 116, 97, 108, 95, 115, 109], ⟨.localityDomainSupplementalSm, none⟩),
  -- %pm0,
  ([112,109,48], ⟨.pm 0, none⟩),
  -- %pm1,
  ([112,109,49], ⟨.pm 1, none⟩),
  -- %pm2,
  ([112,109,50], ⟨.pm 2, none⟩),
  -- %pm3,
  ([112,109,51], ⟨.pm 3, none⟩),
  -- %pm4,
  ([112,109,52], ⟨.pm 4, none⟩),
  -- %pm5,
  ([112,109,53], ⟨.pm 5, none⟩),
  -- %pm6,
  ([112,109,54], ⟨.pm 6, none⟩),
  -- %pm7,
  ([112,109,55], ⟨.pm 7, none⟩),
  -- %pm0_64,
  ([112,109,48,95,54,52], ⟨.pm64 0, none⟩),
  -- %pm1_64,
  ([112,109,49,95,54,52], ⟨.pm64 1, none⟩),
  -- %pm2_64,
  ([112,109,50,95,54,52], ⟨.pm64 2, none⟩),
  -- %pm3_64,
  ([112,109,51,95,54,52], ⟨.pm64 3, none⟩),
  -- %pm4_64,
  ([112,109,52,95,54,52], ⟨.pm64 4, none⟩),
  -- %pm5_64,
  ([112,109,53,95,54,52], ⟨.pm64 5, none⟩),
  -- %pm6_64,
  ([112,109,54,95,54,52], ⟨.pm64 6, none⟩),
  -- %pm7_64,
  ([112,109,55,95,54,52], ⟨.pm64 7, none⟩),
  -- %envreg0,
  ([101,110,118,114,101,103,48], ⟨.envreg 0, none⟩),
  -- %envreg1,
  ([101,110,118,114,101,103,49], ⟨.envreg 1, none⟩),
  -- %envreg2,
  ([101,110,118,114,101,103,50], ⟨.envreg 2, none⟩),
  -- %envreg3,
  ([101,110,118,114,101,103,51], ⟨.envreg 3, none⟩),
  -- %envreg4,
  ([101,110,118,114,101,103,52], ⟨.envreg 4, none⟩),
  -- %envreg5,
  ([101,110,118,114,101,103,53], ⟨.envreg 5, none⟩),
  -- %envreg6,
  ([101,110,118,114,101,103,54], ⟨.envreg 6, none⟩),
  -- %envreg7,
  ([101,110,118,114,101,103,55], ⟨.envreg 7, none⟩),
  -- %envreg8,
  ([101,110,118,114,101,103,56], ⟨.envreg 8, none⟩),
  -- %envreg9,
  ([101,110,118,114,101,103,57], ⟨.envreg 9, none⟩),
  -- %envreg10,
  ([101,110,118,114,101,103,49,48], ⟨.envreg 10, none⟩),
  -- %envreg11,
  ([101,110,118,114,101,103,49,49], ⟨.envreg 11, none⟩),
  -- %envreg12,
  ([101,110,118,114,101,103,49,50], ⟨.envreg 12, none⟩),
  -- %envreg13,
  ([101,110,118,114,101,103,49,51], ⟨.envreg 13, none⟩),
  -- %envreg14,
  ([101,110,118,114,101,103,49,52], ⟨.envreg 14, none⟩),
  -- %envreg15,
  ([101,110,118,114,101,103,49,53], ⟨.envreg 15, none⟩),
  -- %envreg16,
  ([101,110,118,114,101,103,49,54], ⟨.envreg 16, none⟩),
  -- %envreg17,
  ([101,110,118,114,101,103,49,55], ⟨.envreg 17, none⟩),
  -- %envreg18,
  ([101,110,118,114,101,103,49,56], ⟨.envreg 18, none⟩),
  -- %envreg19,
  ([101,110,118,114,101,103,49,57], ⟨.envreg 19, none⟩),
  -- %envreg20,
  ([101,110,118,114,101,103,50,48], ⟨.envreg 20, none⟩),
  -- %envreg21,
  ([101,110,118,114,101,103,50,49], ⟨.envreg 21, none⟩),
  -- %envreg22,
  ([101,110,118,114,101,103,50,50], ⟨.envreg 22, none⟩),
  -- %envreg23,
  ([101,110,118,114,101,103,50,51], ⟨.envreg 23, none⟩),
  -- %envreg24,
  ([101,110,118,114,101,103,50,52], ⟨.envreg 24, none⟩),
  -- %envreg25,
  ([101,110,118,114,101,103,50,53], ⟨.envreg 25, none⟩),
  -- %envreg26,
  ([101,110,118,114,101,103,50,54], ⟨.envreg 26, none⟩),
  -- %envreg27,
  ([101,110,118,114,101,103,50,55], ⟨.envreg 27, none⟩),
  -- %envreg28,
  ([101,110,118,114,101,103,50,56], ⟨.envreg 28, none⟩),
  -- %envreg29,
  ([101,110,118,114,101,103,50,57], ⟨.envreg 29, none⟩),
  -- %envreg30,
  ([101,110,118,114,101,103,51,48], ⟨.envreg 30, none⟩),
  -- %envreg31,
  ([101,110,118,114,101,103,51,49], ⟨.envreg 31, none⟩),
  -- %reserved_smem_offset_0,
  ([114, 101, 115, 101, 114, 118, 101, 100, 95, 115, 109, 101, 109, 95, 111, 102, 102, 115, 101,
    116, 95, 48], ⟨.reservedSmemOffset 0, none⟩),
  -- %reserved_smem_offset_1]
  ([114, 101, 115, 101, 114, 118, 101, 100, 95, 115, 109, 101, 109, 95, 111, 102, 102, 115, 101,
    116, 95, 49], ⟨.reservedSmemOffset 1, none⟩)]

/-- Equality of byte strings, element by element. -/
def SReg.bytesEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && SReg.bytesEq as bs
  | _, _ => false

/-- The special register spelled by the bytes `n`. -/
def SReg.lookup (n : List Nat) : List (List Nat × SReg) → Option SReg
  | [] => none
  | (s, r) :: rest => bif SReg.bytesEq s n then some r else SReg.lookup n rest

/-- The special register a name spells, if any. Names that do not start with `%` are none. -/
def SReg.ofName? (name : String) : Option SReg :=
  match Isa.bytes name with
  | 37 :: n => SReg.lookup n SReg.table
  | _ => none

/-- How THREAD-SREG gives a special register its value: from the launch geometry, from the lane
of the thread in its warp, as a value fixed before the thread starts that the model leaves
unconstrained, or as a value that each read observes anew (`varying`). -/
inductive SRegKind where
  | launch | lane | initial | varying
  deriving DecidableEq, Repr

/-- How THREAD-SREG determines the value of a special register, or none when the model gives it
no value: `%tid`, `%ntid`, `%ctaid`, `%nctaid`, the cluster registers and `%is_explicit_cluster`
come from the launch; `%laneid` and the lane masks from the lane; the registers that the driver
or the machine fixes before launch are left unconstrained; the registers whose value changes
during execution are read by an event; the performance counters have none. -/
def SReg.kind (s : SReg) : Option SRegKind :=
  match s.name, s.dim with
  | .tid, some _ | .ntid, some _ | .ctaid, some _ | .nctaid, some _ | .clusterid, some _
  | .nclusterid, some _ | .clusterCtaid, some _ | .clusterNctaid, some _ => some .launch
  | .clusterCtarank, none | .clusterNctarank, none | .isExplicitCluster, none => some .launch
  | .laneid, none | .lanemaskEq, none | .lanemaskLe, none | .lanemaskLt, none
  | .lanemaskGe, none | .lanemaskGt, none => some .lane
  | .nwarpid, none | .nsmid, none | .gridid, none | .envreg _, none
  | .reservedSmemOffsetBegin, none | .reservedSmemOffsetEnd, none | .reservedSmemOffsetCap, none
  | .reservedSmemOffset _, none | .totalSmemSize, none | .aggrSmemSize, none
  | .dynamicSmemSize, none | .currentGraphExec, none | .localityDomainId, none
  | .localityDomainSupplementalSm, none | .perctamemoryoffset, none
  | .perctamemorysize, none => some .initial
  | .warpid, none | .smid, none | .clock, none | .clockHi, none | .clock64, none
  | .globaltimer, none | .globaltimerLo, none | .globaltimerHi, none => some .varying
  | _, _ => none

/-- The register's value changes while the thread runs, so each read observes it anew
(THREAD-SREG). -/
def SReg.varying (s : SReg) : Bool := s.kind == some .varying

/-- The `%perctamemory` registers, valid only in a kernel with `.minperctamemory` (§10.34,
§10.35). -/
def SReg.perCtaMemory (s : SReg) : Bool :=
  match s.name with
  | .perctamemoryoffset | .perctamemorysize => true
  | _ => false

/-- The rule of a special register read: THREAD-SREG when the register has a kind, none
otherwise. -/
def SReg.rule (s : SReg) : Option RuleId :=
  match s.kind with
  | some _ => some .threadSreg
  | none => none

end PTX
