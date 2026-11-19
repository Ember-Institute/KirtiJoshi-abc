import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def pair_key(decl, name_key, owner_key):
    return json.dumps([decl[name_key], decl[owner_key]], ensure_ascii=False, separators=(",", ":"))


def validated_rows(path):
    with path.open("rb") as stream:
        for raw in stream:
            row = json.loads(raw)
            if not (
                row["record"] == "fullActualFact"
                and row["valueRead"]
                and row["kernelValueTypeMatchesActualTYPE"]
                and row["actualTypeExpr"]
                and row["actualValueExpr"]
                and row["kernelInferredValueTypeExpr"]
                and not row["hasSorryAx"]
                and all(set(row[key]) <= AXIOMS for key in ("axioms", "typeAxioms", "valueAxioms"))
            ):
                raise ValueError(f"{path.name}: incomplete or nonstandard compiler fact for {row['name']}")
            yield row, raw


def main():
    review = json.loads((ROOT / "review-config.json").read_bytes())
    export = json.loads((ROOT / "source-export-config.json").read_bytes())
    supplement = (ROOT / "source-facts-supplement.jsonl")
    expected_supplement = {
        pair_key(item, "name", "owner") for item in export["declarations"]
    }
    gathered = {}
    supplement_keys = set()
    for path in (ROOT / "source-facts-existing.jsonl", supplement):
        for row, raw in validated_rows(path):
            key = pair_key(row, "nameExpr", "ownerNameExpr")
            if key in gathered:
                raise ValueError(f"Duplicate compiler fact for {row['name']}")
            gathered[key] = raw
            if path == supplement:
                supplement_keys.add(key)
    if supplement_keys != expected_supplement:
        raise ValueError("Source supplement differs from the configured declaration and owner list")
    basis = [{
        "source": review["bridgeSource"],
        "sourceOwner": export["declarations"][-1]["owner"],
    }] + review["pairs"]
    ordered = [pair_key(item, "source", "sourceOwner") for item in basis]
    if set(ordered) != set(gathered):
        raise ValueError("Full source evidence differs from the configured review coverage")
    output = ROOT / "source-facts.jsonl"
    output.write_bytes(b"".join(gathered[key] for key in ordered))


if __name__ == "__main__":
    main()
