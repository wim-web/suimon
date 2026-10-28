#!/usr/bin/env python3
"""Cross-check the Lean schema interpreter against python-jsonschema (draft 2020-12)."""
import json
import subprocess
import tempfile
from decimal import Decimal
from pathlib import Path

from jsonschema import Draft202012Validator, validators
from referencing import Registry
from referencing.jsonschema import DRAFT202012

ROOT = Path(__file__).resolve().parents[1]


def integer(_checker, value):
    # JSON's integer type concerns the value, not its spelling. Decimal avoids
    # rounding 2^64-1 or underflowing 1e-1000000000 before validation.
    # https://python-jsonschema.readthedocs.io/en/v4.25.1/validate/#type-checking
    return (isinstance(value, int) and not isinstance(value, bool)) or (
        isinstance(value, Decimal) and value.is_finite() and value == value.to_integral_value()
    )


ExactValidator = validators.extend(
    Draft202012Validator,
    type_checker=Draft202012Validator.TYPE_CHECKER.redefine("integer", integer),
)


def for_validation(schema):
    # The dialect is selected explicitly above; retaining $schema on referenced
    # roots makes jsonschema.evolve switch back to its float-oriented class.
    return {k: v for k, v in schema.items() if k != "$schema"} if isinstance(schema, dict) else schema


def main():
    groups = []
    count = 0

    def group(label, schema, cases, documents=()):
        nonlocal count
        Draft202012Validator.check_schema(schema)
        registry = Registry().with_resources(
            (document["$id"], DRAFT202012.create_resource(for_validation(document)))
            for _name, document in documents
        )
        validator = ExactValidator(for_validation(schema), registry=registry)
        corpus = []
        for name, text, expected in cases:
            actual = validator.is_valid(json.loads(text, parse_float=Decimal))
            if actual != expected:
                raise AssertionError(f"external oracle {label}/{name}: expected {expected}, got {actual}")
            corpus.append({"label": f"{label}/{name}", "text": text, "valid": actual})
        groups.append({"schema": schema, "documents": [{"name": n, "schema": s} for n, s in documents], "cases": corpus})
        count += len(corpus)

    # Both outcomes for the keywords used by the shipped schemas. These fixed
    # expectations also stop an accidentally permissive external adapter passing.
    samples = ["{}", "[]", '"x"', "2", "2.0", "0.2e1", "1.5", "true", "null"]
    accepts = {
        "object": {0}, "array": {1}, "string": {2}, "integer": {3, 4, 5},
        "number": {3, 4, 5, 6}, "boolean": {7}, "null": {8},
    }
    for kind, indices in accepts.items():
        group(f"type {kind}", {"type": kind}, [(text, text, i in indices) for i, text in enumerate(samples)])
    group("true schema", True, [(s, s, True) for s in samples])
    group("false schema", False, [(s, s, False) for s in samples])
    group("object fields", {"type": "object", "properties": {"x": {"type": "string"}}, "required": ["x"], "additionalProperties": False},
          [("present", '{"x":"a"}', True), ("missing", '{}', False), ("type", '{"x":0}', False), ("extra", '{"x":"a","y":1}', False)])
    group("additional schema", {"additionalProperties": {"type": "string"}},
          [("string", '{"a":"b"}', True), ("number", '{"a":1}', False)])
    group("array", {"type": "array", "items": {"type": "string"}, "minItems": 1, "uniqueItems": True},
          [("one", '["a"]', True), ("two", '["a","b"]', True), ("empty", '[]', False), ("duplicate", '["a","a"]', False), ("type", '[1]', False)])
    group("string length", {"type": "string", "minLength": 2},
          [("ascii", '"ab"', True), ("unicode", '"猫😀"', True), ("short", '"😀"', False), ("empty", '""', False)])
    group("enum", {"enum": ["stop", "continue"]},
          [("stop", '"stop"', True), ("continue", '"continue"', True), ("other", '"retry"', False), ("type", 'true', False)])
    group("const", {"const": True}, [("true", 'true', True), ("false", 'false', False), ("one", '1', False)])
    group("oneOf", {"oneOf": [{"type": "integer"}, {"minimum": 0}]},
          [("one match", '-1', True), ("two matches", '1', False), ("zero matches", '-0.5', False)])
    group("local ref", {"$defs": {"name": {"type": "string", "minLength": 1}}, "$ref": "#/$defs/name"},
          [("valid", '"x"', True), ("empty", '""', False), ("type", '0', False)])
    group("exact integer bounds", {"type": "integer", "minimum": 1, "maximum": 18446744073709551615},
          [(s, s, ok) for s, ok in [
              ("1", True), ("2.0", True), ("20e-1", True), ("18446744073709551615", True),
              ("18446744073709551616", False), ("0", False), ("-0", False), ("-1", False),
              ("2.5", False), ("1e-1000000000", False), ("0e-1000000000", False), ("1e1000000000", False),
          ]])

    definition = json.loads((ROOT / "schema/definition.schema.json").read_text())
    trace = json.loads((ROOT / "schema/trace.schema.json").read_text())
    definition_cases, trace_cases = [], []
    for name in ["users", "branch", "merge"]:
        path = ROOT / f"Test/definitions/{name}.json"
        text = path.read_text()
        definition_cases.append((name, text, True))
        # Fresh producer output, not a corpus silently frozen at an older format.
        generated = subprocess.run([str(ROOT / ".lake/build/bin/suimon"), "gen", str(path), "--seed", "3"],
                                   check=True, capture_output=True, text=True).stdout
        lines = generated.splitlines()
        if len(lines) < 3 or not generated.endswith("\n"):
            raise AssertionError(f"{name}: generation did not produce committed records")
        trace_cases.extend((f"{name} line {i + 1}", line, True) for i, line in enumerate(lines))
        broken = json.loads(text)
        broken["extra"] = True
        definition_cases.append((name + " extra field", json.dumps(broken), False))
    unchecked = {"definition": {"main": "w", "workflows": [{"id": "w", "placements": []}]}, "validated": False}
    trace_cases.append(("unchecked", json.dumps(unchecked), True))
    unchecked["validated"] = True
    trace_cases.append(("validated", json.dumps(unchecked), False))
    # Exercise exact-number handling after crossing trace -> definition's $ref,
    # where a validator must preserve the Decimal adapter while changing roots.
    timed_header = ('{"definition":{"main":"w","workflows":[{"id":"w","placements":'
                    '[{"name":"a","node":{"type":"merge","element":"T"},"policy":"stop",'
                    '"timeout":{"callMs":NUMBER}}]}]},"validated":true}')
    trace_cases.extend(("reference timeout " + number, timed_header.replace("NUMBER", number), valid)
                       for number, valid in [("2.0", True), ("20e-1", True), ("18446744073709551615", True),
                                             ("18446744073709551616", False), ("1e-1000000000", False)])
    trace_cases.extend((label, json.dumps(value), False) for label, value in [
        ("unknown op", {"seq": 1, "op": {"type": "retry"}}),
        ("commit with op", {"seq": 1, "op": {"type": "cancel"}, "commit": True}),
        ("zero seq", {"seq": 0, "commit": True}),
        ("payload type", {"seq": 1, "op": {"type": "start", "input": "v"}, "values": {"v": 1}}),
    ])
    group("definition schema", definition, definition_cases)
    group("trace schema", trace, trace_cases, [("definition.schema.json", definition)])
    if count <= 100:
        raise AssertionError(f"unexpectedly small oracle corpus: {count}")
    with tempfile.TemporaryDirectory(prefix="suimon-schema-") as directory:
        corpus = Path(directory) / "corpus.json"
        corpus.write_text(json.dumps(groups, ensure_ascii=False), encoding="utf-8")
        subprocess.run([str(ROOT / ".lake/build/bin/suimon_schema_test"), "--oracle", str(corpus)], check=True)


if __name__ == "__main__":
    main()
