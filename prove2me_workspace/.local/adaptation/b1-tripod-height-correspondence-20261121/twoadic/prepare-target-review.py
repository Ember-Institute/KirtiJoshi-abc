from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path


SCHEMA = "tripod-twoadic-source-correspondence/v1"
CURVE_FACTS = "Iut/Tripod/CurveFacts.lean"
TWO_ADIC = "Iut/Tripod/TwoAdic.lean"
SOURCE_TRIPOD = "Iut.Tripod."
TARGET_TRIPOD = "AbcAdaptation.Tripod."
HYP_OWNER = "Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp"
BOUND_OWNER = "Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBound"
FIELD_OWNER = "Solutions.Source_TripodCurveInputsTwoAdicField"
FIELD_REPLAY = "source-constructor-field-rhs-replay"

PAIRS = (
    ("TwoAdicBoundHyp", TARGET_TRIPOD + "TwoAdicBoundHyp", HYP_OWNER,
     "definition", CURVE_FACTS, 409, "verbatim-source-definition-replay"),
    ("twoAdicBound'", TARGET_TRIPOD + "twoAdicBound'", BOUND_OWNER,
     "theorem", TWO_ADIC, 568, "source-theorem-replay-explicit-nat-sum-cast"),
    ("twoAdicBound", TARGET_TRIPOD + "twoAdicBound", BOUND_OWNER,
     "theorem", TWO_ADIC, 595, "verbatim-source-theorem-replay"),
    ("curveInputsBNonnegFieldReplay", TARGET_TRIPOD + "curveInputs_B_nonneg", FIELD_OWNER,
     "theorem", CURVE_FACTS, 511, FIELD_REPLAY),
    ("curveInputsHeightEqTwoFieldReplay", "TwoAdicConstructorFieldAudit.heightEq_two_le_from_hB",
     None, "theorem", CURVE_FACTS, 512, FIELD_REPLAY),
    ("curveInputsHeightEqTwoSpecializedReplay", TARGET_TRIPOD + "curveInputs_heightEq_two_le",
     FIELD_OWNER, "theorem", CURVE_FACTS, 512,
     "source-constructor-field-rhs-specialized-with-twoAdicBound"),
)

# Finite Extension Scaling audited the arithmetic declarations in this namespace.
TRIPOD_ARITHMETIC = {"inertDeg", "localDeg", "ramIdx", "sum_localDeg_filter_le"}


def name_components(encoded):
    if not encoded:
        return ()
    parent, constructor, value = encoded
    return name_components(parent) + ((constructor, value),)


def named_path(*parts):
    return tuple(("str", part) for part in parts)


def encode_name(components):
    encoded = []
    for constructor, value in components:
        encoded = [encoded, constructor, value]
    return encoded


def module_name(source):
    if source.is_absolute() or source.suffix != ".lean" or ".." in source.parts:
        raise ValueError(f"Expected a workspace-relative Lean source path: {source}")
    return named_path(*source.with_suffix("").parts)


def expression_names(expr):
    if isinstance(expr, dict):
        if expr.get("kind") in {"const", "proj"}:
            yield name_components(expr["name"])
        for value in expr.values():
            yield from expression_names(value)
    elif isinstance(expr, list):
        for value in expr:
            yield from expression_names(value)


# Lean 4.35 renamed these dependent conditional reductions in Init.Core.
LEAN_CORE_RENAMES = {
    named_path("dite_eq_left"): named_path("dif_pos"),
    named_path("dite_eq_right"): named_path("dif_neg"),
}


def target_name(name):
    if name in LEAN_CORE_RENAMES:
        return LEAN_CORE_RENAMES[name]
    if name[:2] == named_path("Iut", "Tripod"):
        return named_path("AbcAdaptation", "Tripod") + name[2:]
    if (len(name) == 2 and name[0] == ("str", "Iut") and
            name[1][0] == "str" and name[1][1] in TRIPOD_ARITHMETIC):
        return named_path("AbcAdaptation", "Tripod") + name[1:]
    if name[:1] in (named_path("Iut"), named_path("Genl"), named_path("TateCurvesTheta")):
        return named_path("AbcAdaptation", "Reference") + name
    if name[:1] in (named_path("_private"), named_path("AbcAdaptation")):
        raise ValueError(f"Source constant requires an explicit relocation: {name}")
    return name


def check_record(row, source_name, source_owner, kind, file, line, provenance):
    if (
        name_components(row["nameExpr"]) != source_name
        or name_components(row["ownerNameExpr"]) != source_owner
        or row["record"] != "fullActualFact"
        or row["kind"] != kind
        or row["referenceFile"] != file
        or row["referenceLine"] != line
        or row["provenance"] != provenance
        or row["isProposition"] != (kind == "theorem")
        or not row["valueRead"]
        or not row["kernelValueTypeMatchesActualTYPE"]
        or row["hasSorryAx"]
    ):
        raise ValueError(f"Unexpected source record: {row['name']}")


def main():
    parser = ArgumentParser()
    parser.add_argument("source_facts", type=Path)
    parser.add_argument("output_config", type=Path)
    parser.add_argument("--source-query", type=Path, required=True,
                        help="Scheduler-relative path of QueryTripodTwoAdicSource.lean")
    parser.add_argument("--target-query", type=Path, required=True,
                        help="Scheduler-relative path of AuditTripodTwoAdicSourceCorrespondence.lean")
    args = parser.parse_args()
    facts_path = args.source_facts.resolve()
    config_path = args.output_config.resolve()
    source_owner = module_name(args.source_query)
    target_query_owner = module_name(args.target_query)
    records = [json.loads(line) for line in facts_path.read_text().splitlines()]
    if len(records) != len(PAIRS):
        raise ValueError(f"Expected six source records, found {len(records)}")

    relocations = {}
    pairs = []
    for row, (source, target, owner, kind, file, line, provenance) in zip(records, PAIRS):
        source_name = named_path(*(SOURCE_TRIPOD + source).split("."))
        check_record(row, source_name, source_owner, kind, file, line, provenance)
        target = named_path(*target.split("."))
        relocations[source_name] = target
        pairs.append({
            "source": encode_name(source_name),
            "sourceOwner": encode_name(source_owner),
            "target": encode_name(target),
            "targetOwner": encode_name(named_path(*owner.split(".")) if owner else target_query_owner),
            "kind": kind,
            "provenance": provenance,
            "referenceFile": file,
            "referenceLine": line,
        })

    for row in records:
        for key in ("actualTypeExpr", "actualValueExpr"):
            for source_name in expression_names(row[key]):
                if source_name in relocations:
                    continue
                target = target_name(source_name)
                if target != source_name:
                    relocations[source_name] = target

    config = {
        "schema": SCHEMA,
        "pairs": pairs,
        "maps": [
            {"source": encode_name(source), "target": encode_name(target)}
            for source, target in sorted(relocations.items())
        ],
        "sourceFactsFile": str(facts_path),
        "evidenceFile": str(config_path.with_name("cross-version-expressions.jsonl")),
        "resultFile": str(config_path.with_name("cross-version-result.json")),
    }
    with config_path.open("w") as output:
        json.dump(config, output, ensure_ascii=False, indent=2)
        output.write("\n")
    for path in (facts_path, config_path):
        print(sha256(path.read_bytes()).hexdigest(), path)


if __name__ == "__main__":
    main()
