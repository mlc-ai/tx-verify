# SPDX-License-Identifier: Apache-2.0
"""Layering of each proof tree (Tools/layers.py): the counters' definitions and ceilings."""

import layers

P = "Kernels.K.Proof2."


def counts(tree):
    return {k: len(v) for k, v in layers.counters(tree).items()}


def test_definitions(make_tree):
    tree = make_tree(
        {
            "Top/X.lean": (
                f"module\nimport {P}A.Ref\nimport {P}A.Export.Bar\nimport all {P}Top.Y\n"
                "import Kernels.K.Proof.Old\n/- stateInv -/\nrw [stateInv]\n"
                "cases σ.role with\n-- RefA\n"
                "@[expose] public section\ntheorem t (h : stateAt X = 1) : RefA X := by\n"
                "  exact stateAt\n"
            ),
            "Top/Y.lean": "module\n",
            "A/Ref.lean": "module\n",
            "A/Export/Bar.lean": (
                f"module\nimport {P}A.Ref\n"
                "theorem priv (h : stateAt X) : True := trivial\n"
                "public section\ntheorem pub (h : Site) : True := trivial\nend\n"
                "public theorem pub2 : True := by\n  exact Site\n"
            ),
            "B/M.lean": f"module\nimport {P}A.Ref\nmatch x.role with\n",
            "Common/Roles.lean": "match x.role with\n",
            "Gen/S.lean": f"module\nimport {P}A.Ref\n",
        },
        roles={"A": [], "B": []},
    )
    assert counts(tree) == {
        "upper imports of role internals": 1,
        "imports between roles": 1,
        "upper import all": 1,
        "upper names of role invariants": 2,
        "upper case splits on the role": 1,
        "imports of old roots": 1,
        "state names in public statements": 3,
        "role matches outside Common": 2,
        "role internals rebuilding upper modules": 1,
    }


def test_allowed_role_imports(make_tree):
    tree = make_tree(
        {"B/M.lean": f"import {P}A.Ref\n", "A/Ref.lean": ""}, roles={"A": [], "B": ["A"]}
    )
    assert counts(tree)["imports between roles"] == 0


def test_rebuild_through_public_imports_only(make_tree):
    """A role internal reaches an upper file through a public import of its export, not through a
    private one; the common `Export` counts, the common `Table` does not."""
    tree = make_tree(
        {
            "A/Ref.lean": "module\n",
            "A/Export/Pub.lean": f"module\npublic import {P}A.Ref\n",
            "A/Export/Priv.lean": f"module\nimport {P}A.Ref\n",
            "Protocol/X.lean": f"module\npublic import {P}A.Export.Priv\n",
            "Protocol/Y.lean": f"module\nimport {P}A.Export.Pub\n",
            "Common/Export/E.lean": f"module\npublic import {P}A.Export.Pub\n",
            "Common/Table.lean": f"module\nimport {P}A.Export.Pub\n",
        }
    )
    assert layers.counters(tree)["role internals rebuilding upper modules"] == [
        f"Common/Export/E.lean: {P}A.Ref",
        f"Protocol/Y.lean: {P}A.Ref",
    ]


def test_boundary_files_count_their_public_closure_only(make_tree):
    """`Common/Follow` and `Common/Export*` read role internals privately by design: only a role
    internal in their public closure counts. An upper file counts its private imports too."""
    tree = make_tree(
        {
            "A/Ref.lean": "module\n",
            "A/Table.lean": f"module\npublic import {P}A.Ref\n",
            "Common/Table.lean": f"module\npublic import {P}A.Table\n",
            "Common/Follow.lean": f"module\nimport {P}Common.Table\n",
            "Common/Export/Priv.lean": f"module\nimport {P}A.Ref\n",
            "Common/Export/Leak.lean": f"module\npublic import {P}Common.Table\n",
            "Top/Priv.lean": f"module\nimport {P}Common.Table\n",
            "Top/Clean.lean": f"module\npublic import {P}Common.Follow\n",
        }
    )
    assert layers.counters(tree)["role internals rebuilding upper modules"] == [
        f"Common/Export/Leak.lean: {P}A.Ref",
        f"Common/Export/Leak.lean: {P}A.Table",
        f"Top/Priv.lean: {P}A.Ref",
        f"Top/Priv.lean: {P}A.Table",
    ]


def test_signature_stops_at_the_proof():
    code = "theorem t (h : P) : Q := by\n  exact stateAt\n\ndef f : Nat := stateAt\n"
    assert [s for _, s in layers.public_signatures(code, False)] == [
        "theorem t (h : P) : Q ",
        "def f : Nat ",
    ]


def test_counters_under_their_ceilings(tree):
    assert not tree.ceiling_violations(counts(tree))
