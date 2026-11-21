from hashlib import sha256
import json
from pathlib import Path
import re


WORKSPACE = Path("/home/admin-wsl/Coq/abc/prove2me_workspace")
DRAFT = Path(__file__).resolve().parent
IUT = "07cb1da58f6d428a670dbb5dd6093d428bcbcdd8"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
SOURCE = f"https://github.com/lana-agents/iut/blob/{IUT}/Iut/Tripod"
TRIPOD = "Def_AbcAdaptation_Reference_Iut_Tripod_"
ARCHIVE = WORKSPACE / ".local/adaptation/b1-height-platform-20261120"
FIELD_ARCHIVE = WORKSPACE / ".local/adaptation/b1-tripod-height-correspondence-20261121/platform/receipts"
LICENSE = """ /-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
""".lstrip()

input_files = set()


def read(path):
    input_files.add(path)
    return path.read_text()


def write(name, body):
    (DRAFT / name).write_text(body.rstrip() + "\n")


def dump(name, data):
    write(name, json.dumps(data, indent=2, ensure_ascii=False))


def definition(suffix):
    return read(WORKSPACE / "Definitions" / f"{TRIPOD}{suffix}.lean")


def solution(name):
    return read(WORKSPACE / "Solutions" / f"Source_Tripod{name}.lean")


def extract(body, start, stop=None):
    _, boundary, rest = body.partition(start)
    if not boundary:
        raise ValueError(f"Missing declaration boundary {start!r}")
    if stop is None:
        return (boundary + rest).rstrip()
    selected, boundary_end, _ = rest.partition(stop)
    if not boundary_end:
        raise ValueError(f"Missing declaration boundary {stop!r}")
    return (boundary + selected).rstrip()


def published(path):
    item = json.loads(read(path / "published-item.json"))
    assert item["mathlib_rev"] == MATHLIB and item["visibility"] == "private", path
    return item


def import_lines(body):
    return [line for line in body.splitlines() if line.startswith("import ")]


def ordered_unique(lines):
    return "\n".join(dict.fromkeys(lines))


def section(name, body):
    return f"section {name}\n\n{body.rstrip()}\n\nend {name}"


def qualify_residue_char(code):
    return re.sub(
        r"(?:\bTripod\.)?\bresidueChar\b",
        "AbcAdaptation.Reference.Iut.residueChar",
        code,
    )


provider = published(ARCHIVE / "provider-height")
assert provider["definition"] == definition("CurveProviderHeight")
for name in ("FieldTransport", "FieldLegendreFacts"):
    assert published(FIELD_ARCHIVE / name)["definition"] == definition(name)

height_parts_file = WORKSPACE / "Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean"
height_parts = read(height_parts_file)
height_eq_command = extract(
    height_parts,
    "/-- The part of",
    "\n\n/-- The part of",
)
height_eq = (
    "namespace AbcAdaptation.Reference.Iut.LocalHeightData\n\n"
    "open Finset Real\n\nvariable (L : LocalHeightData)\n\n"
    f"{height_eq_command}\n\n"
    "end AbcAdaptation.Reference.Iut.LocalHeightData"
)
bound_hyp = extract(definition("TwoAdicBoundHyp"), "namespace AbcAdaptation.Tripod")
assert bound_hyp.endswith("end AbcAdaptation.Tripod")
definition_name = "AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp"
package_import = f"import Definitions.Def_{provider['definition_name']}"
package_body = "\n\n".join((height_eq, bound_hyp))
package = f"{LICENSE}{package_import}\n\n{package_body}\n"
write(f"Def_{definition_name}.lean", package)
dump("definition.payload.json", {
    "definition_name": definition_name,
    "definition_title": "Height from places above a rational prime",
    "definition": package,
    "natural_language_statement": (
        r"For a rational prime $p$, restrict the supplied curve's local height sum to the "
        r"places with residue characteristic $p$. Each summand is the order of the Tate "
        r"parameter times the residue degree and $\log p$. Divide the sum by the degree "
        r"of the curve's field over $\mathbb Q$. For a compactly bounded subset $K$, "
        r"$\mathrm{TwoAdicBoundHyp}(P,K,B)$ asserts that this contribution for $p=2$ "
        r"is at most $B$ at every point in $K$."
    ),
    "source": f"{SOURCE}/CurveFacts.lean#L409",
    "tags": ["number-theory", "arithmetic-geometry"],
    "env": MATHLIB,
    "private": True,
})

provider_packages = (
    ("InertiaDegree", "inertia-degree"),
    ("PlaceUnder", "place-under"),
    ("RelativeValuation", "relative-valuation"),
    ("FinitePlaceArithmetic", "absolute-place-arithmetic"),
    ("RelativeDegreeTower", "relative-degree-tower"),
    ("FinitePlaceMapEquiv", "finite-place-map-equiv"),
)
archives = [(name, published(ARCHIVE / folder)) for name, folder in provider_packages]
inlined_platform_modules = {"Definitions.Def_" + item["definition_name"] for _, item in archives}
platform_sections = []
platform_review_imports = [package_import]
for name, item in archives:
    body = item["definition"]
    imports = import_lines(body)
    platform_review_imports.extend(line for line in imports if line.split()[1] not in inlined_platform_modules)
    for line in imports:
        body = body.replace(f"{line}\n", "", 1)
    if name == "RelativeDegreeTower":
        # Preserve the residue-characteristic name from this module's import scope.
        old_type = "lemma residueChar_eq_of_liesOver : residueChar v = residueChar w := by"
        new_type = (
            "lemma residueChar_eq_of_liesOver :\n"
            "    AbcAdaptation.Reference.Iut.residueChar v = AbcAdaptation.Reference.Iut.residueChar w := by"
        )
        assert body.count(old_type) == 1
        body = body.replace(old_type, new_type)
    platform_sections.append(section(name, body.strip()))

imports = [
    f"import Definitions.Def_{definition_name}",
    f"import Definitions.{TRIPOD}FieldTransport",
    f"import Definitions.{TRIPOD}FieldLegendreFacts",
    "import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceMapEquiv",
    "import Definitions.Def_AbcAdaptation_Tripod_PlaceUnder",
    "import Definitions.Def_AbcAdaptation_Tripod_RelativeDegreeTower",
    "import Mathlib.Algebra.Order.GroupWithZero.Canonical",
    "import Mathlib.RingTheory.Valuation.Basic",
    "import Mathlib.Tactic.GCongr",
    "import Mathlib.Tactic.Linarith",
    "import Mathlib.Tactic.Positivity",
    "import Mathlib.Tactic.SplitIfs",
]
base_sections = []
for name, namespace in (
    ("FinitePlaceResidueTransport", "AbcAdaptation.Reference.Iut"),
    ("TripodalPlaceTransport", "AbcAdaptation.Tripod"),
    ("TripodalCompactValuation", "AbcAdaptation.Tripod"),
    ("TwoAdicLegendreValuation", "AbcAdaptation.Tripod"),
    ("TatePoleOrder", "AbcAdaptation.Reference.TateCurvesTheta.TateParameter"),
):
    start = f"namespace {namespace}\n"
    body = (
        extract(definition(name), start, "\n\nnamespace AbcAdaptation.Tripod\n")
        if name == "TatePoleOrder" else extract(definition(name), start)
    )
    body = qualify_residue_char(body)
    if name == "TripodalCompactValuation":
        old_proof = "  have hb := hx.1 (tpdPlace P x 𝔭) (by rwa [residueChar_tpdPlace])"
        new_proof = (
            "  have hmem : AbcAdaptation.Reference.Iut.residueChar (tpdPlace P x 𝔭) ∈ K.V :=\n"
            "    (residueChar_tpdPlace P x 𝔭).symm ▸ h𝔭\n"
            "  have hb := hx.1 (tpdPlace P x 𝔭) hmem"
        )
        assert body.count(old_proof) == 1
        body = body.replace(old_proof, new_proof)
    base_sections.append(section(name, body))

c_nonneg = extract(
    read(WORKSPACE / "Definitions/Def_TripodLegendreHeightBasics.lean"),
    "theorem CompactlyBounded.c_nonneg ",
    "\n\ntheorem gen_ne_one",
)
base_sections.append(section("CompactBound", f"""namespace AbcAdaptation.Tripod

open NumberField

{c_nonneg}

end AbcAdaptation.Tripod"""))

valuation_256 = extract(
    solution("FinitePlaceArithmetic"), "theorem valuation_256_le_one ", "\nsection\n"
)
local_degree_sum = extract(
    solution("FinitePrimeCounting"),
    "section\n",
    "\n\n/-- " + chr(96) + "∑_{w ∈ S, p_w = q} f_w",
)
base_sections.append(section("LocalDegrees", qualify_residue_char(f"""set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

{valuation_256}

{local_degree_sum}

end

end AbcAdaptation.Tripod""")))

name = "TwoAdicLocalTerm"
body = qualify_residue_char(extract(definition(name), "namespace AbcAdaptation.Tripod\n"))
old_proof = (
    "  have h𝔭2 : AbcAdaptation.Reference.Iut.residueChar 𝔭 = 2 := by "
    "rw [← residueChar_eq_of_liesOver hw𝔭, hw2]"
)
new_proof = (
    "  have h𝔭2 : AbcAdaptation.Reference.Iut.residueChar 𝔭 = 2 :=\n"
    "    (residueChar_eq_of_liesOver hw𝔭).symm.trans hw2"
)
assert body.count(old_proof) == 1
base_sections.append(section(name, body.replace(old_proof, new_proof)))

bound = definition("TwoAdicBound")
bound_prime = extract(bound, "namespace AbcAdaptation.Tripod\n", "\n\n/-- **The ")
base_sections.append(section("TwoAdicBound", f"{qualify_residue_char(bound_prime)}\n\nend AbcAdaptation.Tripod"))
theorem_command = extract(bound, "theorem twoAdicBound (", "\n\nend AbcAdaptation.Tripod")
_, assign, proof = theorem_command.partition(" :=\n")
assert assign

statement = (
    "(P : CurveProviders) (K : CompactlyBounded) :\n"
    "    TwoAdicBoundHyp P K (max (4 * K.c) 0)"
)
base_sections.append(section("TwoAdicSolution", f"""set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution {statement} :=
{proof}"""))
solution_body = "\n\n".join(base_sections)
write("solution.lean", f"{LICENSE}{ordered_unique(imports)}\n\n{solution_body}")
review_imports = platform_review_imports + [
    line for line in imports
    if line.split()[1] not in inlined_platform_modules
    and line != f"import Definitions.Def_{definition_name}"
]
review_sections = [
    *platform_sections,
    section("TwoAdicHypothesis", package_body),
    solution_body,
    """section TwoAdicPlatformStatement

open AbcAdaptation.Tripod

theorem AbcAdaptation.Tripod.twoAdicBound (P : CurveProviders) (K : CompactlyBounded) :
    TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  solution P K

#print axioms AbcAdaptation.Reference.Iut.LocalHeightData.heightEq
#print axioms TwoAdicBoundHyp
#print axioms twoAdicBound'
#print axioms twoAdicBound
#print axioms solution

end TwoAdicPlatformStatement""",
]
write("ReviewPlatformTwoAdic.lean", f"{LICENSE}{ordered_unique(review_imports)}\n\n" + "\n\n".join(review_sections))

preamble = (
    f"import Definitions.Def_{definition_name}\n\n"
    "set_option autoImplicit false\n\nopen AbcAdaptation.Tripod"
)
formal_statement = f"theorem AbcAdaptation.Tripod.twoAdicBound {statement} := by sorry"
write("formal-statement.lean", f"{preamble}\n\n{formal_statement}")
dump("twoAdicBound.problem.json", {
    "problems": [{
        "theorem_name": "AbcAdaptation.Tripod.twoAdicBound",
        "theorem_title": "Bound for the height from places above 2 on the tripod",
        "formal_statement": formal_statement,
        "preamble": preamble,
        "natural_language_statement": (
            r"Let $K$ be a compactly bounded subset of the tripod with logarithmic bound $c$. "
            r"The bounds on $\lambda$ and $\lambda-1$ apply at the finite places of "
            r"$\mathbb Q(\lambda)$ above $2$. Let $P$ be a tripod curve provider. "
            r"For each point $x$ in $K$, write $F_x$ for the field of its supplied curve. "
            r"At a place $w$ of multiplicative reduction above $2$, let $m_w$ be the "
            r"order of the Tate parameter and let $f_w$ be the residue degree over $2$."
            "\n\nProve that for every $x$ in $K$,\n\n"
            r"$$\frac{1}{[F_x:\mathbb Q]}"
            r"\sum_{\substack{w\mid 2\\w\ \text{of multiplicative reduction}}}"
            r" m_w f_w\log 2\ \le\ \max(4c,0).$$"
        ),
        "source": f"{SOURCE}/TwoAdic.lean#L595",
    }],
    "env": MATHLIB,
    "private": True,
})

inline_modules = {
    item["definition_name"]: {
        "definition_id": item["definition_id"],
        "definition_sha256": sha256(item["definition"].encode()).hexdigest(),
    } for _, item in archives
}
dump("inputs.json", {
    "source_revision": IUT,
    "lean": "leanprover/lean4:v4.33.1",
    "mathlib_revision": MATHLIB,
    "review_inlined_definitions": inline_modules,
    "review_inlining_qualifications": {
        "AbcAdaptation_Tripod_RelativeDegreeTower":
            "Qualify residueChar to preserve the archived module's import scope.",
    },
    "source_inputs": {
        str(path.relative_to(WORKSPACE)): sha256(path.read_bytes()).hexdigest()
        for path in sorted(input_files)
    },
    "artifacts": {
        name: sha256((DRAFT / name).read_bytes()).hexdigest()
        for name in (
            f"Def_{definition_name}.lean", "definition.payload.json", "formal-statement.lean",
            "twoAdicBound.problem.json", "solution.lean", "explanation.md", "ReviewPlatformTwoAdic.lean",
        )
    },
})
