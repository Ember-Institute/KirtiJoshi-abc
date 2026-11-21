"""Bind the remaining Tate supply certificates to the completed support audits."""

import argparse
import hashlib
import json
from pathlib import Path


SOURCE_PREFIX = "Iut.EllipticCurveData."
TARGET_PREFIX = "AbcAdaptation.Reference." + SOURCE_PREFIX
NORM_PROOF = SOURCE_PREFIX + "one_lt_norm_j"
PARAMETER_PROOF = SOURCE_PREFIX + "tateParameter._proof_1"
UNIFORMIZER_PROOF = SOURCE_PREFIX + "tateInputs._proof_1"
UNIFORMIZER_CERTIFICATE = SOURCE_PREFIX + "tateInputs._proof_2"
DECLARATIONS = {
    SOURCE_PREFIX + "tateParameter": ("definition", ("default", "implicit")),
    SOURCE_PREFIX + "tateParameter_tateJ": ("theorem", ("default", "implicit")),
    SOURCE_PREFIX + "tateInputs": ("definition", ("default", "default")),
}


def load(path):
    return json.loads(path.read_text())


def describe(path):
    sha256 = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            sha256.update(chunk)
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": sha256.hexdigest(),
    }


def encode_name(name):
    result = []
    for component in name.split("."):
        result = [result, "str", component]
    return result


def decode_name(encoded):
    if not encoded:
        return ""
    parent, _, component = encoded
    return ".".join(filter(None, (decode_name(parent), str(component))))


def project_references(expression):
    if isinstance(expression, dict):
        if expression.get("kind") in ("const", "proj"):
            name = decode_name(expression["name"])
            if name.partition(".")[0] in ("Iut", "TateCurvesTheta", "AbcAdaptation", "_private", "Genl"):
                yield name
        for child in expression.values():
            yield from project_references(child)
    elif isinstance(expression, list):
        for child in expression:
            yield from project_references(child)


def support_record(report, source):
    if report["source"] != source:
        raise ValueError(f"Unexpected support declaration {report['source']}")
    target = report["target"]
    parameter_target_prefix = TARGET_PREFIX + "tateParameter._proof_"
    if source == PARAMETER_PROOF:
        if not target.startswith(parameter_target_prefix):
            raise ValueError(f"Expected the generated target parameter proof, received {target}")
    elif target != "AbcAdaptation.Reference." + source:
        raise ValueError(f"Unexpected target for {source}: {target}")
    if not all(report[field]["completeExprKernelDefEq"] for field in ("type", "value")):
        raise ValueError(f"Support proof lacks a complete comparison: {source}")
    return {
        "source": encode_name(source),
        "target": encode_name(target),
        "targetType": report["type"]["nativeExpr"],
        "targetValue": report["value"]["nativeExpr"],
    }


def accepted_receipt(path, expected_job=None):
    receipt = load(path)
    if expected_job is not None and receipt["job_id"] != expected_job:
        raise ValueError(f"Unexpected receipt job: {path}")
    result = receipt["result"]
    if (
        receipt["status"] != "succeeded"
        or result["exit_code"] != 0
        or not result["review"]["passed"]
        or not result["review"]["checks"]["no_sorryAx"]
        or result["snapshot"]["workspace_mode"] != "exclusive_worktree"
        or result["snapshot"]["snapshot_id"] is not None
    ):
        raise ValueError(f"Support proof audit has not passed: {path}")
    return receipt["job_id"]


def selected_certificates(drafts):
    pack = load(drafts / "source-common-core-certificates.json")
    if not pack["sourceCompleteKernelNormalizationChecked"]:
        raise ValueError("Expected successful source kernel normalization")
    original = {}
    with (drafts / "source-facts.jsonl").open() as facts:
        for line in facts:
            row = json.loads(line)
            if row.get("name") in DECLARATIONS:
                original[row["name"]] = row
    rows = {}
    for record in pack["sourceRecords"]:
        name = record["name"]
        if name in DECLARATIONS:
            if record != original[name] or record["kind"] != DECLARATIONS[name][0]:
                raise ValueError(f"Source export differs at {name}")
            rows[name] = {"sourceRecord": record}
    references = set()
    for certificate in pack["normalizationCertificates"]:
        name = certificate["name"]
        if name not in rows:
            continue
        label = certificate["label"]
        certificate_field, raw_field = {
            "TYPE": ("typeCertificate", "actualTypeExpr"),
            "value": ("valueCertificate", "actualValueExpr"),
        }[label]
        if certificate["rawExpression"] != rows[name]["sourceRecord"][raw_field]:
            raise ValueError(f"Source raw expression differs at {name} {label}")
        if certificate_field in rows[name]:
            raise ValueError(f"Duplicate source certificate at {name} {label}")
        template = certificate["samePropCompatibilityTemplateCertificate"]
        proof_count = 0 if name.endswith(".tateInputs") and label == "TYPE" else 1
        sites = template["actualSourceProofArguments"]
        if len(sites) != proof_count or template["certificateOnlyProofFunctionCount"] != proof_count:
            raise ValueError(f"Unexpected local completion proof count at {name} {label}")
        for site in sites:
            if (
                site["originalContextDependencyIndices"] != [0, 1]
                or tuple(site["originalContextBinderInfo"]) != DECLARATIONS[name][1]
            ):
                raise ValueError(f"Local completion proof binders changed at {name} {label}")
            references.update(project_references(site["proofFunctionType"]))
        references.update(project_references(template["completeProofFunctionTemplate"]))
        rows[name][certificate_field] = {
            key: certificate[key]
            for key in (
                "nameExpr",
                "label",
                "rawExpression",
                "samePropCompatibilityTemplateCertificate",
                "sourceCompleteKernelNormalizationChecked",
            )
        }
    return [rows[name] for name in DECLARATIONS], references


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--drafts", type=Path, required=True)
    parser.add_argument("--parameter-config", type=Path, required=True)
    parser.add_argument("--parameter-report", type=Path, required=True)
    parser.add_argument("--parameter-receipt", type=Path, required=True)
    parser.add_argument("--output-file", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    args = parser.parse_args()

    parameter_job = accepted_receipt(args.parameter_receipt)
    parameter_config = load(args.parameter_config)
    parameter_report = load(args.parameter_report)
    if not parameter_report["kernelCorrespondencePassed"]:
        raise ValueError("Expected a complete comparison of the auxiliary existence proof")
    choice_use = parameter_report["nativeChoiceProofUse"]
    if (
        choice_use["definition"] != TARGET_PREFIX + "tateParameter"
        or choice_use["consumer"] != "Exists.choose"
        or choice_use["argumentIndex"] != 2
        or not choice_use["argumentTypeMatchesDeclaration"]
    ):
        raise ValueError("Expected the kernel-checked actual proof argument to Exists.choose")
    parameter_support = support_record(parameter_report["comparison"], PARAMETER_PROOF)
    chosen = parameter_report["actualNativeChoiceProofDeclaration"]
    if (
        chosen["name"] != decode_name(parameter_support["target"])
        or chosen["name"] != decode_name(parameter_report["targetNameExpr"])
        or chosen["actualTypeExpr"] != parameter_support["targetType"]
        or chosen["actualValueExpr"] != parameter_support["targetValue"]
    ):
        raise ValueError("Compared proof differs from the actual proof argument to Exists.choose")
    parameter_support["target"] = parameter_report["targetNameExpr"]

    norm_report_path = args.drafts / "parameter-norm/parameter-norm-review-v2.result.json"
    norm_report = load(norm_report_path)
    norm_record, = (row for row in norm_report["comparisons"] if row["source"] == NORM_PROOF)
    norm_support = support_record(norm_record, NORM_PROOF)
    for field in ("targetType", "targetValue"):
        if norm_support[field] != parameter_config["normSupport"][field]:
            raise ValueError("The existence proof audited a different native norm proof")
    accepted_support = [norm_support, parameter_support]
    prior_reviews = (
        ("uniformizer-proof", "ci-026263-81548b47", UNIFORMIZER_PROOF),
        ("uniformizer-proof-2", "ci-026283-d6fd14d8", UNIFORMIZER_CERTIFICATE),
    )
    uniformizer_inputs = []
    for stage, job, source in prior_reviews:
        receipt_path = args.drafts / stage / f"{job}.result.json"
        report_path = args.drafts / stage / f"{stage}-review.result.json"
        accepted_receipt(receipt_path, job)
        report = load(report_path)
        if not report["completeKernelCorrespondencePassed"]:
            raise ValueError(f"Expected uniformizer correspondence for {source}")
        accepted_support.append(support_record(report, source))
        uniformizer_inputs.append(
            {"job": job, "receipt": describe(receipt_path), "report": describe(report_path)}
        )

    rows, used_names = selected_certificates(args.drafts)
    used_names.update(DECLARATIONS)
    support_names = {
        decode_name(record["source"]): record["target"] for record in accepted_support
    }
    used_names.update(support_names)
    used_names.update(decode_name(record["source"]) for record in parameter_config["qOrderSupport"])
    used_names.add(decode_name(parameter_config["jExistenceSupport"]["source"]))
    candidates = load(args.drafts / "target-candidates.json")
    maps = []
    for row in candidates["maps"]:
        source = decode_name(row["source"])
        if source in used_names:
            maps.append({"source": row["source"], "target": support_names.get(source, row["target"])})
    if {decode_name(record["source"]) for record in maps} != used_names:
        missing = sorted(used_names - {decode_name(record["source"]) for record in maps})
        raise ValueError(f"Missing explicit source names: {missing}")

    config = {
        "schema": "b1-tate-supply-remaining-review/v1",
        "outputFile": str(args.output_file.resolve()),
        "maps": maps,
        "pairs": rows,
        "qOrderSupport": parameter_config["qOrderSupport"],
        "jExistenceSupport": parameter_config["jExistenceSupport"],
        "acceptedSupplyProofs": accepted_support,
        "provenance": {
            **parameter_config["provenance"],
            "parameterProofJob": parameter_job,
            "parameterProofReceipt": describe(args.parameter_receipt),
            "parameterProofReport": describe(args.parameter_report),
            "parameterProofConfig": describe(args.parameter_config),
            "normProofReport": describe(norm_report_path),
            "uniformizerProofs": uniformizer_inputs,
        },
    }
    args.config.write_text(
        json.dumps(config, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    )
    print(json.dumps(describe(args.config), ensure_ascii=False))


if __name__ == "__main__":
    main()
