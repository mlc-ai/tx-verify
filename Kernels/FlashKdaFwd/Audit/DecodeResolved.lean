-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeNames
public import Kernels.FlashKdaFwd.Audit.DecodeScope00
public import Kernels.FlashKdaFwd.Audit.DecodeScope13
public import Kernels.FlashKdaFwd.Audit.DecodeScope15
public import Kernels.FlashKdaFwd.Audit.DecodeScope16
public import Kernels.FlashKdaFwd.Audit.DecodeScope17
public import Kernels.FlashKdaFwd.Audit.DecodeScope19
public import Kernels.FlashKdaFwd.Audit.DecodeScope21
public import Kernels.FlashKdaFwd.Audit.DecodeScope23
public import Kernels.FlashKdaFwd.Audit.DecodeScope25
public import Kernels.FlashKdaFwd.Audit.DecodeScope26
public import Kernels.FlashKdaFwd.Audit.DecodeScope29
public import Kernels.FlashKdaFwd.Audit.DecodeScope30
public import Kernels.FlashKdaFwd.Audit.DecodeScope32

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000
set_option Elab.async false

/-- The statements of the body from part 32 on. -/
def rawFrom32 : List Statement := raw32

/-- What the statements from part 32 on resolve to. -/
def resolvedFrom32 : List Statement := resolved32

private theorem resolved_tail_32 :
    resolveScopePart (resolveScopes rootFuel) rawFrom32 rootBindings "" 3797 =
      .ok resolvedFrom32 :=
  resolved_32

/-- The statements of the body from part 31 on. -/
def rawFrom31 : List Statement := raw31 ++ rawFrom32

/-- What the statements from part 31 on resolve to. -/
def resolvedFrom31 : List Statement := resolved31 ++ resolvedFrom32

private theorem resolved_tail_31 :
    resolveScopePart (resolveScopes rootFuel) rawFrom31 rootBindings "" 3796 =
      .ok resolvedFrom31 :=
  resolveScopePart_append resolved_31 resolved_tail_32

/-- The statements of the body from part 30 on. -/
def rawFrom30 : List Statement := raw30 ++ rawFrom31

/-- What the statements from part 30 on resolve to. -/
def resolvedFrom30 : List Statement := resolved30 ++ resolvedFrom31

private theorem resolved_tail_30 :
    resolveScopePart (resolveScopes rootFuel) rawFrom30 rootBindings "" 3521 =
      .ok resolvedFrom30 :=
  resolveScopePart_append resolved_30 resolved_tail_31

/-- The statements of the body from part 29 on. -/
def rawFrom29 : List Statement := raw29 ++ rawFrom30

/-- What the statements from part 29 on resolve to. -/
def resolvedFrom29 : List Statement := resolved29 ++ resolvedFrom30

private theorem resolved_tail_29 :
    resolveScopePart (resolveScopes rootFuel) rawFrom29 rootBindings "" 3012 =
      .ok resolvedFrom29 :=
  resolveScopePart_append resolved_29 resolved_tail_30

/-- The statements of the body from part 28 on. -/
def rawFrom28 : List Statement := raw28 ++ rawFrom29

/-- What the statements from part 28 on resolve to. -/
def resolvedFrom28 : List Statement := resolved28 ++ resolvedFrom29

private theorem resolved_tail_28 :
    resolveScopePart (resolveScopes rootFuel) rawFrom28 rootBindings "" 3011 =
      .ok resolvedFrom28 :=
  resolveScopePart_append resolved_28 resolved_tail_29

/-- The statements of the body from part 27 on. -/
def rawFrom27 : List Statement := raw27 ++ rawFrom28

/-- What the statements from part 27 on resolve to. -/
def resolvedFrom27 : List Statement := resolved27 ++ resolvedFrom28

private theorem resolved_tail_27 :
    resolveScopePart (resolveScopes rootFuel) rawFrom27 rootBindings "" 3010 =
      .ok resolvedFrom27 :=
  resolveScopePart_append resolved_27 resolved_tail_28

/-- The statements of the body from part 26 on. -/
def rawFrom26 : List Statement := raw26 ++ rawFrom27

/-- What the statements from part 26 on resolve to. -/
def resolvedFrom26 : List Statement := resolved26 ++ resolvedFrom27

private theorem resolved_tail_26 :
    resolveScopePart (resolveScopes rootFuel) rawFrom26 rootBindings "" 2628 =
      .ok resolvedFrom26 :=
  resolveScopePart_append resolved_26 resolved_tail_27

/-- The statements of the body from part 25 on. -/
def rawFrom25 : List Statement := raw25 ++ rawFrom26

/-- What the statements from part 25 on resolve to. -/
def resolvedFrom25 : List Statement := resolved25 ++ resolvedFrom26

private theorem resolved_tail_25 :
    resolveScopePart (resolveScopes rootFuel) rawFrom25 rootBindings "" 2128 =
      .ok resolvedFrom25 :=
  resolveScopePart_append resolved_25 resolved_tail_26

/-- The statements of the body from part 24 on. -/
def rawFrom24 : List Statement := raw24 ++ rawFrom25

/-- What the statements from part 24 on resolve to. -/
def resolvedFrom24 : List Statement := resolved24 ++ resolvedFrom25

private theorem resolved_tail_24 :
    resolveScopePart (resolveScopes rootFuel) rawFrom24 rootBindings "" 2127 =
      .ok resolvedFrom24 :=
  resolveScopePart_append resolved_24 resolved_tail_25

/-- The statements of the body from part 23 on. -/
def rawFrom23 : List Statement := raw23 ++ rawFrom24

/-- What the statements from part 23 on resolve to. -/
def resolvedFrom23 : List Statement := resolved23 ++ resolvedFrom24

private theorem resolved_tail_23 :
    resolveScopePart (resolveScopes rootFuel) rawFrom23 rootBindings "" 1897 =
      .ok resolvedFrom23 :=
  resolveScopePart_append resolved_23 resolved_tail_24

/-- The statements of the body from part 22 on. -/
def rawFrom22 : List Statement := raw22 ++ rawFrom23

/-- What the statements from part 22 on resolve to. -/
def resolvedFrom22 : List Statement := resolved22 ++ resolvedFrom23

private theorem resolved_tail_22 :
    resolveScopePart (resolveScopes rootFuel) rawFrom22 rootBindings "" 1896 =
      .ok resolvedFrom22 :=
  resolveScopePart_append resolved_22 resolved_tail_23

/-- The statements of the body from part 21 on. -/
def rawFrom21 : List Statement := raw21 ++ rawFrom22

/-- What the statements from part 21 on resolve to. -/
def resolvedFrom21 : List Statement := resolved21 ++ resolvedFrom22

private theorem resolved_tail_21 :
    resolveScopePart (resolveScopes rootFuel) rawFrom21 rootBindings "" 1445 =
      .ok resolvedFrom21 :=
  resolveScopePart_append resolved_21 resolved_tail_22

/-- The statements of the body from part 20 on. -/
def rawFrom20 : List Statement := raw20 ++ rawFrom21

/-- What the statements from part 20 on resolve to. -/
def resolvedFrom20 : List Statement := resolved20 ++ resolvedFrom21

private theorem resolved_tail_20 :
    resolveScopePart (resolveScopes rootFuel) rawFrom20 rootBindings "" 1444 =
      .ok resolvedFrom20 :=
  resolveScopePart_append resolved_20 resolved_tail_21

/-- The statements of the body from part 19 on. -/
def rawFrom19 : List Statement := raw19 ++ rawFrom20

/-- What the statements from part 19 on resolve to. -/
def resolvedFrom19 : List Statement := resolved19 ++ resolvedFrom20

private theorem resolved_tail_19 :
    resolveScopePart (resolveScopes rootFuel) rawFrom19 rootBindings "" 1421 =
      .ok resolvedFrom19 :=
  resolveScopePart_append resolved_19 resolved_tail_20

/-- The statements of the body from part 18 on. -/
def rawFrom18 : List Statement := raw18 ++ rawFrom19

/-- What the statements from part 18 on resolve to. -/
def resolvedFrom18 : List Statement := resolved18 ++ resolvedFrom19

private theorem resolved_tail_18 :
    resolveScopePart (resolveScopes rootFuel) rawFrom18 rootBindings "" 1420 =
      .ok resolvedFrom18 :=
  resolveScopePart_append resolved_18 resolved_tail_19

/-- The statements of the body from part 17 on. -/
def rawFrom17 : List Statement := raw17 ++ rawFrom18

/-- What the statements from part 17 on resolve to. -/
def resolvedFrom17 : List Statement := resolved17 ++ resolvedFrom18

private theorem resolved_tail_17 :
    resolveScopePart (resolveScopes rootFuel) rawFrom17 rootBindings "" 1340 =
      .ok resolvedFrom17 :=
  resolveScopePart_append resolved_17 resolved_tail_18

/-- The statements of the body from part 16 on. -/
def rawFrom16 : List Statement := raw16 ++ rawFrom17

/-- What the statements from part 16 on resolve to. -/
def resolvedFrom16 : List Statement := resolved16 ++ resolvedFrom17

private theorem resolved_tail_16 :
    resolveScopePart (resolveScopes rootFuel) rawFrom16 rootBindings "" 828 =
      .ok resolvedFrom16 :=
  resolveScopePart_append resolved_16 resolved_tail_17

/-- The statements of the body from part 15 on. -/
def rawFrom15 : List Statement := raw15 ++ rawFrom16

/-- What the statements from part 15 on resolve to. -/
def resolvedFrom15 : List Statement := resolved15 ++ resolvedFrom16

private theorem resolved_tail_15 :
    resolveScopePart (resolveScopes rootFuel) rawFrom15 rootBindings "" 326 =
      .ok resolvedFrom15 :=
  resolveScopePart_append resolved_15 resolved_tail_16

/-- The statements of the body from part 14 on. -/
def rawFrom14 : List Statement := raw14 ++ rawFrom15

/-- What the statements from part 14 on resolve to. -/
def resolvedFrom14 : List Statement := resolved14 ++ resolvedFrom15

private theorem resolved_tail_14 :
    resolveScopePart (resolveScopes rootFuel) rawFrom14 rootBindings "" 325 =
      .ok resolvedFrom14 :=
  resolveScopePart_append resolved_14 resolved_tail_15

/-- The statements of the body from part 13 on. -/
def rawFrom13 : List Statement := raw13 ++ rawFrom14

/-- What the statements from part 13 on resolve to. -/
def resolvedFrom13 : List Statement := resolved13 ++ resolvedFrom14

private theorem resolved_tail_13 :
    resolveScopePart (resolveScopes rootFuel) rawFrom13 rootBindings "" 16 =
      .ok resolvedFrom13 :=
  resolveScopePart_append resolved_13 resolved_tail_14

/-- The statements of the body from part 12 on. -/
def rawFrom12 : List Statement := raw12 ++ rawFrom13

/-- What the statements from part 12 on resolve to. -/
def resolvedFrom12 : List Statement := resolved12 ++ resolvedFrom13

private theorem resolved_tail_12 :
    resolveScopePart (resolveScopes rootFuel) rawFrom12 rootBindings "" 15 =
      .ok resolvedFrom12 :=
  resolveScopePart_append resolved_12 resolved_tail_13

/-- The statements of the body from part 11 on. -/
def rawFrom11 : List Statement := raw11 ++ rawFrom12

/-- What the statements from part 11 on resolve to. -/
def resolvedFrom11 : List Statement := resolved11 ++ resolvedFrom12

private theorem resolved_tail_11 :
    resolveScopePart (resolveScopes rootFuel) rawFrom11 rootBindings "" 14 =
      .ok resolvedFrom11 :=
  resolveScopePart_append resolved_11 resolved_tail_12

/-- The statements of the body from part 10 on. -/
def rawFrom10 : List Statement := raw10 ++ rawFrom11

/-- What the statements from part 10 on resolve to. -/
def resolvedFrom10 : List Statement := resolved10 ++ resolvedFrom11

private theorem resolved_tail_10 :
    resolveScopePart (resolveScopes rootFuel) rawFrom10 rootBindings "" 13 =
      .ok resolvedFrom10 :=
  resolveScopePart_append resolved_10 resolved_tail_11

/-- The statements of the body from part 9 on. -/
def rawFrom9 : List Statement := raw9 ++ rawFrom10

/-- What the statements from part 9 on resolve to. -/
def resolvedFrom9 : List Statement := resolved9 ++ resolvedFrom10

private theorem resolved_tail_9 :
    resolveScopePart (resolveScopes rootFuel) rawFrom9 rootBindings "" 12 =
      .ok resolvedFrom9 :=
  resolveScopePart_append resolved_9 resolved_tail_10

/-- The statements of the body from part 8 on. -/
def rawFrom8 : List Statement := raw8 ++ rawFrom9

/-- What the statements from part 8 on resolve to. -/
def resolvedFrom8 : List Statement := resolved8 ++ resolvedFrom9

private theorem resolved_tail_8 :
    resolveScopePart (resolveScopes rootFuel) rawFrom8 rootBindings "" 11 =
      .ok resolvedFrom8 :=
  resolveScopePart_append resolved_8 resolved_tail_9

/-- The statements of the body from part 7 on. -/
def rawFrom7 : List Statement := raw7 ++ rawFrom8

/-- What the statements from part 7 on resolve to. -/
def resolvedFrom7 : List Statement := resolved7 ++ resolvedFrom8

private theorem resolved_tail_7 :
    resolveScopePart (resolveScopes rootFuel) rawFrom7 rootBindings "" 10 =
      .ok resolvedFrom7 :=
  resolveScopePart_append resolved_7 resolved_tail_8

/-- The statements of the body from part 6 on. -/
def rawFrom6 : List Statement := raw6 ++ rawFrom7

/-- What the statements from part 6 on resolve to. -/
def resolvedFrom6 : List Statement := resolved6 ++ resolvedFrom7

private theorem resolved_tail_6 :
    resolveScopePart (resolveScopes rootFuel) rawFrom6 rootBindings "" 9 =
      .ok resolvedFrom6 :=
  resolveScopePart_append resolved_6 resolved_tail_7

/-- The statements of the body from part 5 on. -/
def rawFrom5 : List Statement := raw5 ++ rawFrom6

/-- What the statements from part 5 on resolve to. -/
def resolvedFrom5 : List Statement := resolved5 ++ resolvedFrom6

private theorem resolved_tail_5 :
    resolveScopePart (resolveScopes rootFuel) rawFrom5 rootBindings "" 8 =
      .ok resolvedFrom5 :=
  resolveScopePart_append resolved_5 resolved_tail_6

/-- The statements of the body from part 4 on. -/
def rawFrom4 : List Statement := raw4 ++ rawFrom5

/-- What the statements from part 4 on resolve to. -/
def resolvedFrom4 : List Statement := resolved4 ++ resolvedFrom5

private theorem resolved_tail_4 :
    resolveScopePart (resolveScopes rootFuel) rawFrom4 rootBindings "" 7 =
      .ok resolvedFrom4 :=
  resolveScopePart_append resolved_4 resolved_tail_5

/-- The statements of the body from part 3 on. -/
def rawFrom3 : List Statement := raw3 ++ rawFrom4

/-- What the statements from part 3 on resolve to. -/
def resolvedFrom3 : List Statement := resolved3 ++ resolvedFrom4

private theorem resolved_tail_3 :
    resolveScopePart (resolveScopes rootFuel) rawFrom3 rootBindings "" 6 =
      .ok resolvedFrom3 :=
  resolveScopePart_append resolved_3 resolved_tail_4

/-- The statements of the body from part 2 on. -/
def rawFrom2 : List Statement := raw2 ++ rawFrom3

/-- What the statements from part 2 on resolve to. -/
def resolvedFrom2 : List Statement := resolved2 ++ resolvedFrom3

private theorem resolved_tail_2 :
    resolveScopePart (resolveScopes rootFuel) rawFrom2 rootBindings "" 5 =
      .ok resolvedFrom2 :=
  resolveScopePart_append resolved_2 resolved_tail_3

/-- The statements of the body from part 1 on. -/
def rawFrom1 : List Statement := raw1 ++ rawFrom2

/-- What the statements from part 1 on resolve to. -/
def resolvedFrom1 : List Statement := resolved1 ++ resolvedFrom2

private theorem resolved_tail_1 :
    resolveScopePart (resolveScopes rootFuel) rawFrom1 rootBindings "" 4 =
      .ok resolvedFrom1 :=
  resolveScopePart_append resolved_1 resolved_tail_2

/-- The statements of the body from part 0 on. -/
def rawFrom0 : List Statement := raw0 ++ rawFrom1

/-- What the statements from part 0 on resolve to. -/
def resolvedFrom0 : List Statement := resolved0 ++ resolvedFrom1

private theorem resolved_tail_0 :
    resolveScopePart (resolveScopes rootFuel) rawFrom0 rootBindings "" 0 =
      .ok resolvedFrom0 :=
  resolveScopePart_append resolved_0 resolved_tail_1

/-- The scope-resolved body. -/
def resolved : List Statement := resolvedFrom0

private theorem source_body : source.body = rawFrom0 := by
  kernel_rfl

private theorem source_depth : scopeDepth source.body = rootFuel + 1 := by
  kernel_rfl

private theorem source_resolved :
    resolveScopes (scopeDepth source.body) source.body [] "" = .ok resolved := by
  apply resolveScopes_of_part source_depth rootBindings_eq
  have h := congrArg (fun body =>
    resolveScopePart (resolveScopes rootFuel) body rootBindings "" 0 = .ok resolved)
    source_body
  exact Eq.mpr h resolved_tail_0

theorem prepare_eq :
    prepare Generated.FlashKdaFwd.module.globals source =
      prepareResolved Generated.FlashKdaFwd.module.globals source resolved :=
  prepare_of_resolved (by kernel_rfl) (by kernel_rfl) source_resolved

end PTX.Kernels.FlashKdaFwd.DecodeAudit
