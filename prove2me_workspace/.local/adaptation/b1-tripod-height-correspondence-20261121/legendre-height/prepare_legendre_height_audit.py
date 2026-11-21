import argparse
import json
from pathlib import Path


SOURCE_TRIPOD = "Iut.Tripod."
TARGET_TRIPOD = "AbcAdaptation.Tripod."
LEGENDRE_HEIGHT_OWNER = "Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeight"
GENERIC_ZERO_J = "pow_six_eq_one_of_legendreJ_eq_zero"
ROOTS = (
    ("LegendreHeightHyp", "definition", LEGENDRE_HEIGHT_OWNER + "Hyp"),
    ("legendreHeight", "theorem", LEGENDRE_HEIGHT_OWNER),
)
ALIASES = (
    "finHeight_legendreJ_le",
    "finHeight_legendreJ_ge",
    "logHeight₁_le_finHeight_add",
)


def lean_name(*components):
    name = []
    for component in components:
        name = [name, "num" if isinstance(component, int) else "str", component]
    return name


def dotted_name(name):
    return lean_name(*name.split("."))


def pair(source, target):
    return {"source": dotted_name(source), "target": dotted_name(target)}


def make_config(source_file, normalization_config, config_path):
    source_file = source_file.resolve()
    dependencies_file = source_file.with_name(source_file.name + ".dependencies.json")
    previous = json.loads(normalization_config.read_text())
    mappings = previous["maps"] + [
        pair(SOURCE_TRIPOD + name, TARGET_TRIPOD + name)
        for name in (
            "CompactlyBounded",
            "CompactlyBounded.V",
            "CompactlyBounded.c",
            "CompactlyBounded.c_nonneg",
            "CompactlyBounded.set",
            "deg_eq_finrank",
            "gen_ne_one",
            "gen_ne_zero",
            "htCan",
            "htCan._proof_1",
            "htCan.eq_1",
            "LegendreHeightHyp._proof_1",
        )
    ]
    mappings += [
        pair("DiscrepancyLE", "AbcAdaptation.Reference.DiscrepancyLE"),
        pair("DiscrepancyEquiv", "AbcAdaptation.Reference.DiscrepancyEquiv"),
        pair("Iut.finHeight_le_logHeight₁", TARGET_TRIPOD + "finHeight_le_logHeight₁"),
        pair("Iut.finHeight_zero", TARGET_TRIPOD + "finHeight_zero"),
    ]
    with source_file.open() as records:
        roots = [json.loads(line) for line in records]
    pairs = []
    for (name, kind, owner), row in zip(ROOTS, roots, strict=True):
        mapping = pair(SOURCE_TRIPOD + name, TARGET_TRIPOD + name)
        if row["nameExpr"] != mapping["source"] or row["kind"] != kind:
            raise ValueError(f"Unexpected source export for {name}")
        pairs.append(
            {
                **mapping,
                "kind": kind,
                "sourceOwner": row["ownerNameExpr"],
                "targetOwner": dotted_name(owner),
            }
        )
        mappings.append(mapping)

    dependencies = []
    for alias in ALIASES:
        source = dotted_name(SOURCE_TRIPOD + alias)
        target = lean_name(
            "_private", *LEGENDRE_HEIGHT_OWNER.split("."), 0, "AbcAdaptation", "Tripod", alias
        )
        dependencies.append(
            {"source": source, "target": target, "targetOwner": dotted_name(LEGENDRE_HEIGHT_OWNER)}
        )
    dependencies.append(
        {
            **pair("Iut." + GENERIC_ZERO_J, "TripodLegendreHeightSourceCorrespondence." + GENERIC_ZERO_J),
            "targetOwner": None,
        }
    )
    for spec, row in zip(dependencies, json.loads(dependencies_file.read_text()), strict=True):
        if spec["source"] != row["nameExpr"]:
            raise ValueError(f"Unexpected source dependency {row['name']}")
        mappings.append({"source": spec["source"], "target": spec["target"]})

    output_dir = config_path.resolve().parent
    return {
        "schema": "b1-tripod-legendre-height-source-correspondence/v1",
        "pairs": pairs,
        "maps": mappings,
        "dependencies": dependencies,
        "sourceFactsFile": str(source_file),
        "sourceDependenciesFile": str(dependencies_file),
        "evidenceFile": str(output_dir / "cross-version-expressions.jsonl"),
        "resultFile": str(output_dir / "cross-version-result.json"),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source_facts", type=Path, help="JSONL from QueryTripodLegendreHeightSource")
    parser.add_argument("normalization_config", type=Path, help="The accepted review-config-v2.json")
    parser.add_argument("target_config", type=Path, help="Output JSON configuration")
    args = parser.parse_args()
    config = make_config(args.source_facts, args.normalization_config, args.target_config)
    args.target_config.write_text(json.dumps(config, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
