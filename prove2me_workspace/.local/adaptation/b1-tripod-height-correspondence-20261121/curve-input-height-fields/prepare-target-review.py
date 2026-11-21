from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path

TRIPOD = (("str", "Iut"), ("str", "Tripod"))
TARGET_TRIPOD = (("str", "AbcAdaptation"), ("str", "Tripod"))
TARGET_STRUCTURE = (("str", "AbcAdaptation"), ("str", "Reference"), ("str", "Iut"), ("str", "CurveInputs"))
SOURCE_FIELDS = (
    ("curveInputsHeightEqReplay", "height_eq", 503),
    ("curveInputsHtCanEquivReplay", "htCan_equiv", 508),
    ("curveInputsNorthcottReplay", "northcott", 509),
)
SCHEMA = "tripod-height-field-source-correspondence/v1"
PROVENANCE = "source-constructor-field-rhs-replay"


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


def expression_names(expr):
    if isinstance(expr, dict):
        if expr.get("kind") in {"const", "proj"}:
            yield name_components(expr["name"])
        for value in expr.values():
            yield from expression_names(value)
    elif isinstance(expr, list):
        for value in expr:
            yield from expression_names(value)


def project_name(name):
    prefix, suffix = name[:1], name[1:]
    if name in (named_path("DiscrepancyEquiv"), named_path("DiscrepancyLE")):
        return named_path("AbcAdaptation", "Reference") + name
    if name[:2] == TRIPOD:
        return TARGET_TRIPOD + name[2:]
    if prefix in (named_path("Iut"), named_path("Genl"), named_path("TateCurvesTheta")):
        return named_path("AbcAdaptation", "Reference") + prefix + suffix
    if prefix == named_path("_private") or prefix == named_path("AbcAdaptation"):
        raise ValueError(f"Source constant requires an explicit relocation: {name}")
    return name


def read_facts(path, expected_owner):
    records = [json.loads(line) for line in path.read_text().splitlines()]
    if len(records) != len(SOURCE_FIELDS):
        raise ValueError(f"Expected three field records, found {len(records)}")
    for row, (source, _, line) in zip(records, SOURCE_FIELDS):
        if (
            name_components(row["nameExpr"]) != TRIPOD + named_path(source)
            or name_components(row["ownerNameExpr"]) != expected_owner
            or row["record"] != "fullActualFact"
            or row["kind"] != "theorem"
            or row["referenceFile"] != "Iut/Tripod/CurveFacts.lean"
            or row["referenceLine"] != line
            or row["provenance"] != PROVENANCE
            or not row["valueRead"]
            or not row["kernelValueTypeMatchesActualTYPE"]
            or row["hasSorryAx"]
        ):
            raise ValueError(f"Unexpected source theorem record: {row['name']}")
    return records


def main():
    parser = ArgumentParser()
    parser.add_argument("source_facts", type=Path)
    parser.add_argument("output_config", type=Path)
    args = parser.parse_args()
    source_facts = args.source_facts.resolve()
    config_path = args.output_config.resolve()
    output_dir = config_path.parent
    query_info = json.loads(Path(__file__).with_name("source-environment.json").read_text())
    owner = named_path(*Path(query_info["source"]).with_suffix("").parts)
    records = read_facts(source_facts, owner)
    constructor_owner = named_path("Solutions", "Source_TripodCurveInputs")
    relocations = {}
    pairs = []
    for source, target, line in SOURCE_FIELDS:
        source_name = TRIPOD + named_path(source)
        target_name = TARGET_STRUCTURE + named_path(target)
        relocations[source_name] = target_name
        pairs.append(
            {
                "source": encode_name(source_name),
                "sourceOwner": encode_name(owner),
                "target": encode_name(target_name),
                "targetOwner": encode_name(constructor_owner),
                "kind": "theorem",
                "provenance": PROVENANCE,
                "referenceLine": line,
            }
        )
    for row in records:
        for key in ("actualTypeExpr", "actualValueExpr"):
            for source_name in expression_names(row[key]):
                if source_name in relocations:
                    continue
                target_name = project_name(source_name)
                if target_name != source_name:
                    relocations[source_name] = target_name
    config = {
        "schema": SCHEMA,
        "pairs": pairs,
        "maps": [
            {"source": encode_name(source), "target": encode_name(target)}
            for source, target in sorted(relocations.items())
        ],
        "sourceFactsFile": str(source_facts),
        "evidenceFile": str(output_dir / "cross-version-expressions.jsonl"),
        "resultFile": str(output_dir / "cross-version-result.json"),
    }
    with config_path.open("w") as output:
        json.dump(config, output, ensure_ascii=False, indent=2)
        output.write("\n")
    for pin in (source_facts, config_path):
        print(sha256(pin.read_bytes()).hexdigest(), pin)


if __name__ == "__main__":
    main()
