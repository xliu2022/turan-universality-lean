#!/usr/bin/env python3
"""Inventory completed Lean 3.1.0 NDJSON exports without invoking a kernel.

The schema and implicit name/level zero entries follow the pinned toolchain's
LeanExport/Basic.lean and LeanExport/Parse.lean. Input is read line by line;
compact expression hashes and head-name indices are retained instead of the
full expressions. A successful audit is a structural/completeness check, not
type checking, proof validation, or definitional comparison.
"""

from __future__ import annotations

import argparse
from array import array
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys
import time


class AuditError(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise AuditError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def loads(data):
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_constant=lambda x: (_ for _ in ()).throw(AuditError(f"non-JSON number: {x}")))


def obj(value, fields, context):
    require(type(value) is dict, f"{context}: expected object")
    require(set(value) == set(fields), f"{context}: fields {set(value)} != {set(fields)}")
    return value


def nat(value, context):
    require(type(value) is int and value >= 0, f"{context}: expected natural number")
    return value


def boolean(value, context):
    require(type(value) is bool, f"{context}: expected Boolean")
    return value


def string(value, context):
    require(type(value) is str, f"{context}: expected string")
    return value


def list_of(value, callback, context):
    require(type(value) is list, f"{context}: expected array")
    return [callback(x) for x in value]


def json_bytes(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")


def digest(tag, *parts):
    h = hashlib.sha256()
    for part in (tag.encode("ascii"), *parts):
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    return h.digest()


def file_sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


class ExportAudit:
    EXPR_KINDS = ("bvar", "sort", "const", "app", "lam", "forallE", "letE",
                  "proj", "natVal", "strVal", "mdata")
    BINDERS = {"default", "implicit", "strictImplicit", "instImplicit"}

    def __init__(self, path, targets):
        self.path = path
        self.targets = targets
        self.names = [None]  # 0 is Name.anonymous; it is not emitted.
        self.name_keys = set()
        self.name_hash = [digest("name.anonymous")]
        self.render_cache = {0: "<anonymous>"}
        self.level_hash = [digest("level.zero")]  # Implicit universe zero.
        self.expr_hash = bytearray()
        self.expr_kind = bytearray()
        self.expr_head = array("I")
        self.declarations = {}
        self.constant_refs = set()
        self.structural_refs = set()
        self.group_refs = set()
        self.axioms = []
        self.unsafe = []
        self.counts = Counter()
        self.decl_counts = Counter()
        self.line = 0
        self.offset = 0
        self.metadata = None
        self.target_records = {}

    def name_ref(self, value):
        value = nat(value, "name reference")
        require(value < len(self.names), f"undefined/forward name reference {value}")
        return value

    def level_ref(self, value):
        value = nat(value, "level reference")
        require(value < len(self.level_hash), f"undefined/forward level reference {value}")
        return value

    def expr_ref(self, value):
        value = nat(value, "expression reference")
        require(value < len(self.expr_kind), f"undefined/forward expression reference {value}")
        return value

    def expr_digest(self, value):
        value = self.expr_ref(value)
        return self.expr_hash[32 * value:32 * (value + 1)]

    def render_name(self, index):
        self.name_ref(index)
        if index not in self.render_cache:
            pre, kind, value = self.names[index]
            if kind == "num":
                part = str(value)
            else:
                # Quoted components distinguish Name.str "0" from Name.num 0.
                part = value if re.fullmatch(r"[^\W\d][\w']*", value) else "«" + value + "»"
            self.render_cache[index] = (self.render_name(pre) + "." if pre else "") + part
        return self.render_cache[index]

    def type_summary(self, index):
        self.expr_ref(index)
        head = self.expr_head[index]
        return {
            "expression_index": index,
            "root_kind": self.EXPR_KINDS[self.expr_kind[index]],
            "head_constant": self.render_name(head) if head else None,
            "structural_sha256": bytes(self.expr_digest(index)).hex(),
        }

    def consume_name(self, row):
        index = nat(row["in"], "name index")
        require(index == len(self.names), f"duplicate or noncontiguous name index {index}")
        kind = "str" if "str" in row else "num"
        obj(row, ["in", kind], "name record")
        data = obj(row[kind], ["pre", "str" if kind == "str" else "i"], "name node")
        pre = self.name_ref(data["pre"])
        value = string(data["str"], "name string") if kind == "str" else nat(data["i"], "name numeral")
        key = (pre, kind, value)
        require(key not in self.name_keys, f"duplicate interned name value {key!r}")
        self.name_keys.add(key)
        self.names.append(key)
        self.name_hash.append(digest("name." + kind, self.name_hash[pre], json_bytes(value)))
        return "name." + kind

    def consume_level(self, row):
        index = nat(row["il"], "level index")
        require(index == len(self.level_hash), f"duplicate or noncontiguous level index {index}")
        kinds = set(row) - {"il"}
        require(len(kinds) == 1, "level record needs one constructor")
        kind = kinds.pop()
        data = row[kind]
        if kind == "param":
            parts = [self.name_hash[self.name_ref(data)]]
        elif kind == "succ":
            parts = [self.level_hash[self.level_ref(data)]]
        elif kind in ("max", "imax"):
            require(type(data) is list and len(data) == 2, "binary level constructor needs two indices")
            parts = [self.level_hash[self.level_ref(x)] for x in data]
        else:
            raise AuditError(f"unsupported level constructor: {kind}")
        self.level_hash.append(digest("level." + kind, *parts))
        return "level." + kind

    def consume_expr(self, row):
        index = nat(row["ie"], "expression index")
        require(index == len(self.expr_kind), f"duplicate or noncontiguous expression index {index}")
        kinds = set(row) - {"ie"}
        require(len(kinds) == 1, "expression record needs one constructor")
        kind = kinds.pop()
        require(kind in self.EXPR_KINDS, f"unsupported expression constructor {kind}")
        data = row[kind]
        head = 0
        if kind == "bvar":
            parts = [json_bytes(nat(data, "bound variable index"))]
        elif kind == "sort":
            parts = [self.level_hash[self.level_ref(data)]]
        elif kind == "const":
            obj(data, ["name", "us"], "constant expression")
            head = self.name_ref(data["name"])
            self.constant_refs.add(head)
            us = list_of(data["us"], self.level_ref, "constant universe arguments")
            parts = [self.name_hash[head]] + [self.level_hash[u] for u in us]
        elif kind == "app":
            obj(data, ["fn", "arg"], "application")
            fn, arg = self.expr_ref(data["fn"]), self.expr_ref(data["arg"])
            parts = [self.expr_digest(fn), self.expr_digest(arg)]
            head = self.expr_head[fn]
        elif kind in ("lam", "forallE"):
            obj(data, ["name", "type", "body", "binderInfo"], kind)
            require(data["binderInfo"] in self.BINDERS, "invalid binder information")
            parts = [self.name_hash[self.name_ref(data["name"])],
                     self.expr_digest(data["type"]), self.expr_digest(data["body"]),
                     json_bytes(data["binderInfo"])]
        elif kind == "letE":
            obj(data, ["name", "type", "value", "body", "nondep"], kind)
            parts = [self.name_hash[self.name_ref(data["name"])],
                     self.expr_digest(data["type"]), self.expr_digest(data["value"]),
                     self.expr_digest(data["body"]), json_bytes(boolean(data["nondep"], "let nondep"))]
        elif kind == "proj":
            obj(data, ["typeName", "idx", "struct"], "projection")
            type_name = self.name_ref(data["typeName"])
            self.structural_refs.add(type_name)
            parts = [self.name_hash[type_name], json_bytes(nat(data["idx"], "projection index")),
                     self.expr_digest(data["struct"])]
        elif kind == "natVal":
            string(data, "natural literal")
            require(re.fullmatch(r"[0-9]+", data) is not None, "invalid natural literal")
            parts = [str(int(data)).encode("ascii")]
        elif kind == "strVal":
            parts = [string(data, "string literal").encode("utf-8")]
        else:  # mdata is optional in the pinned format; default exports omit it.
            obj(data, ["expr", "data"], "expression metadata")
            require(type(data["data"]) is dict, "metadata payload needs object")
            parts = [self.expr_digest(data["expr"]), json_bytes(data["data"])]
        self.expr_hash.extend(digest("expr." + kind, *parts))
        self.expr_kind.append(self.EXPR_KINDS.index(kind))
        self.expr_head.append(head)
        return "expr." + kind

    def consume_declaration(self, kind, data, record_hash):
        fields = {"name", "levelParams", "type"}
        additions = {
            "axiom": {"isUnsafe"},
            "def": {"value", "hints", "safety", "all"},
            "thm": {"value", "all"},
            "opaque": {"value", "all", "isUnsafe"},
            "quot": {"kind"},
            "inductive.type": {"all", "ctors", "numParams", "numIndices", "numNested", "isRec", "isReflexive", "isUnsafe"},
            "inductive.ctor": {"induct", "cidx", "numParams", "numFields", "isUnsafe"},
            "inductive.rec": {"all", "numParams", "numIndices", "numMotives", "numMinors", "rules", "k", "isUnsafe"},
        }
        obj(data, fields | additions[kind], kind + " declaration")
        name = self.name_ref(data["name"])
        require(name != 0, "anonymous declaration")
        require(name not in self.declarations, f"duplicate declaration: {self.render_name(name)}")
        params = list_of(data["levelParams"], self.name_ref, "universe parameter names")
        require(len(params) == len(set(params)), "duplicate declaration universe parameter")
        ty = self.expr_ref(data["type"])
        if "value" in data:
            self.expr_ref(data["value"])
        if "all" in data:
            self.group_refs.update(list_of(data["all"], self.name_ref, "mutual group names"))
        if "isUnsafe" in data and boolean(data["isUnsafe"], "declaration isUnsafe"):
            self.unsafe.append(self.render_name(name))
        if kind == "def":
            require(data["safety"] in ("safe", "partial", "unsafe"), "invalid definition safety")
            if data["safety"] != "safe":
                self.unsafe.append(self.render_name(name))
            hints = data["hints"]
            if type(hints) is str:
                require(hints in ("opaque", "abbrev"), "invalid reducibility hint")
            else:
                obj(hints, ["regular"], "reducibility hint")
                nat(hints["regular"], "reducibility height")
        elif kind == "quot":
            require(data["kind"] in ("type", "ctor", "lift", "ind"), "invalid quotient primitive kind")
        elif kind.startswith("inductive."):
            for key in ("numParams", "numIndices", "numNested", "cidx", "numFields", "numMotives", "numMinors"):
                if key in data:
                    nat(data[key], key)
            for key in ("isRec", "isReflexive", "k"):
                if key in data:
                    boolean(data[key], key)
            if "ctors" in data:
                self.structural_refs.update(list_of(data["ctors"], self.name_ref, "constructor names"))
            if "induct" in data:
                self.structural_refs.add(self.name_ref(data["induct"]))
            if "rules" in data:
                require(type(data["rules"]) is list, "recursor rules must be array")
                for rule in data["rules"]:
                    obj(rule, ["ctor", "nfields", "rhs"], "recursor rule")
                    self.structural_refs.add(self.name_ref(rule["ctor"]))
                    nat(rule["nfields"], "recursor field count")
                    self.expr_ref(rule["rhs"])
        summary = {
            "name": self.render_name(name), "name_index": name, "kind": kind,
            "record_line": self.line, "type": self.type_summary(ty),
        }
        self.declarations[name] = summary
        self.decl_counts[kind] += 1
        if kind == "axiom":
            self.axioms.append(summary["name"])
        if summary["name"] in self.targets:
            require(kind == "thm", f"target is {kind}, not theorem: {summary['name']}")
            self.target_records[summary["name"]] = {
                **summary, "record_byte_offset": self.offset, "record_sha256": record_hash,
                "level_parameters": [self.render_name(p) for p in params],
                "value_expression_index": data["value"],
                "value_structural_sha256": bytes(self.expr_digest(data["value"])).hex(),
            }
        # If a target has a named proposition type, retain the definition body
        # digest as well. Type digests themselves never unfold named constants.
        if kind == "def" and summary["name"] == "TuranUniversality.Registry.structuralStatement":
            summary["value_structural_sha256"] = bytes(self.expr_digest(data["value"])).hex()

    def run(self):
        initial = self.path.stat()
        h = hashlib.sha256()
        final_newline = False
        last_kind = None
        last_record_hash = None
        with self.path.open("rb") as stream:
            for self.line, raw in enumerate(stream, 1):
                try:
                    require(raw.endswith(b"\n"), "unterminated last NDJSON record (possible truncation)")
                    require(raw.strip(), "blank NDJSON record")
                    row = loads(raw)
                    require(type(row) is dict, "NDJSON record must be an object")
                    if "meta" in row:
                        obj(row, ["meta"], "metadata record")
                        require(self.line == 1 and self.metadata is None, "metadata must occur exactly once at start")
                        self.metadata = row["meta"]
                        require(type(self.metadata) is dict, "metadata payload must be object")
                        require(self.metadata.get("format", {}).get("version") == "3.1.0", "unsupported export format")
                        require(self.metadata.get("exporter", {}).get("name") == "lean4export", "unexpected exporter")
                        kind = "meta"
                    else:
                        require(self.metadata is not None, "missing initial metadata record")
                        if "in" in row:
                            kind = self.consume_name(row)
                        elif "il" in row:
                            kind = self.consume_level(row)
                        elif "ie" in row:
                            kind = self.consume_expr(row)
                        else:
                            require(len(row) == 1, "declaration record needs exactly one constructor")
                            kind, data = next(iter(row.items()))
                            record_hash = hashlib.sha256(raw).hexdigest()
                            if kind == "inductive":
                                obj(data, ["types", "ctors", "recs"], "inductive block")
                                require(type(data["types"]) is list and data["types"], "empty inductive block")
                                for key, subtype in (("types", "type"), ("ctors", "ctor"), ("recs", "rec")):
                                    require(type(data[key]) is list, f"inductive {key} must be array")
                                    for declaration in data[key]:
                                        self.consume_declaration("inductive." + subtype, declaration, record_hash)
                            else:
                                require(kind in ("axiom", "def", "thm", "opaque", "quot"), f"unsupported record {kind}")
                                self.consume_declaration(kind, data, record_hash)
                    self.counts[kind] += 1
                    h.update(raw)
                    self.offset += len(raw)
                    final_newline = True
                    last_kind = kind
                    last_record_hash = hashlib.sha256(raw).hexdigest()
                except (AuditError, ValueError, TypeError, KeyError, UnicodeDecodeError) as error:
                    raise AuditError(f"{self.path}:{self.line}: {error}") from error
        require(self.metadata is not None, "empty NDJSON file")
        final = self.path.stat()
        stable = (initial.st_dev, initial.st_ino, initial.st_size, initial.st_mtime_ns) == (
            final.st_dev, final.st_ino, final.st_size, final.st_mtime_ns)
        require(stable, "export file changed while being parsed")
        require(self.offset == initial.st_size, "parsed byte count differs from file size")
        missing = (self.constant_refs | self.structural_refs) - set(self.declarations)
        require(not missing, "missing referenced declarations: " + ", ".join(self.render_name(n) for n in sorted(missing)))
        missing_targets = set(self.targets) - set(self.target_records)
        require(not missing_targets, f"missing target theorem roots: {sorted(missing_targets)}")
        name_by_text = {self.render_name(n): n for n in range(1, len(self.names))}
        flags = {}
        for forbidden in ("sorryAx", "Lean.ofReduceBool"):
            idx = name_by_text.get(forbidden)
            flags[forbidden] = {"name_interned": idx is not None,
                                "declaration_present": idx in self.declarations if idx is not None else False,
                                "constant_expression_present": idx in self.constant_refs if idx is not None else False}
        targets = [self.target_records[name] for name in self.targets]
        for target in targets:
            if target["type"]["root_kind"] == "const":
                head = self.expr_head[target["type"]["expression_index"]]
                target["named_type_declaration"] = self.declarations[head]
        return {
            "file": str(self.path), "bytes": initial.st_size, "sha256": h.hexdigest(),
            "metadata": self.metadata, "ndjson_records": self.line,
            "record_counts": dict(sorted(self.counts.items())),
            "interned_names_including_implicit_anonymous": len(self.names),
            "interned_levels_including_implicit_zero": len(self.level_hash),
            "interned_expressions": len(self.expr_kind),
            "declaration_counts": dict(sorted(self.decl_counts.items())),
            "total_declarations": len(self.declarations), "targets": targets,
            "axiom_names": sorted(self.axioms), "forbidden_name_presence": flags,
            "unsafe_or_partial_declarations": sorted(self.unsafe),
            "integrity": {
                "all_json_records_parsed": True, "duplicate_json_keys_rejected": True,
                "all_interned_ids_contiguous_and_unique": True,
                "all_name_level_expression_references_resolved": True,
                "all_expression_constant_and_structural_references_declared": True,
                "all_declaration_names_unique": True, "all_target_roots_are_theorems": True,
                "missing_targets": [], "missing_referenced_declarations": [],
                "undefined_mutual_group_metadata_names": sorted(self.render_name(n) for n in self.group_refs - set(self.declarations)),
                "file_unchanged_during_parse": stable, "ends_with_complete_newline_terminated_record": final_newline,
                "last_record_kind": last_kind, "last_record_sha256": last_record_hash,
                "format_has_dedicated_end_marker": False,
            },
            "declarations": list(self.declarations.values()),
        }


def provenance(root, metadata_path, export_path, module, targets):
    metadata = loads(metadata_path.read_bytes())
    require(metadata.get("exit_code") == 0 and metadata.get("timed_out") is False,
            f"completed successful export record required: {metadata_path}")
    command = metadata.get("command", [])
    require(command[-len(targets):] == targets and module in command, "export metadata target/module mismatch")
    log_path = root / metadata["log"]
    require(file_sha256(log_path) == metadata["log_sha256"], "export log hash differs from completion record")
    log_records = [loads(line) for line in log_path.read_bytes().splitlines() if line.strip()]
    matches = [x for x in log_records if x.get("output") == str(export_path.relative_to(root))]
    require(len(matches) == 1 and matches[0].get("exit_code") == 0, "missing successful exporter output record")
    actual = matches[0]
    require(actual.get("output_bytes") == export_path.stat().st_size, "file length differs from completed exporter log")
    require(actual["command"][3] == module and set(targets) <= set(actual["command"][5:]), "underlying exporter command mismatch")
    return {"completion_record": str(metadata_path.relative_to(root)),
            "completion_record_sha256": file_sha256(metadata_path),
            "export_log": str(log_path.relative_to(root)), "export_log_sha256": metadata["log_sha256"],
            "exporter_exit_code": 0, "exporter_reported_bytes": actual["output_bytes"],
            "file_size_matches_completed_exporter": True,
            "export_finished_utc": metadata.get("finished_utc")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--challenge", default=".verification-work/challenge.ndjson")
    parser.add_argument("--solution", default=".verification-work/solution.ndjson")
    parser.add_argument("--challenge-completion", default="verification/combined/export-challenge-01.json")
    parser.add_argument("--solution-completion", default="verification/combined/export-solution-01.json")
    parser.add_argument("--output", default="verification/combined/export-inventory.json")
    args = parser.parse_args()
    root = args.root.resolve()
    config_path = root / "comparator.json"
    config = loads(config_path.read_bytes())
    targets = config["theorem_names"]
    require(len(targets) == 3 and len(set(targets)) == 3, "expected exactly three unique configured theorem targets")
    require(config["definition_names"] == [], "this audit expects no additional definition targets")
    standard = {"propext", "Quot.sound", "Classical.choice"}
    require(set(config["permitted_axioms"]) == standard, "configured axiom set is not the standard three")
    started = time.monotonic()
    results = {}
    for label in ("challenge", "solution"):
        path = root / getattr(args, label)
        completed = root / getattr(args, label + "_completion")
        source = provenance(root, completed, path, config[label + "_module"], targets)
        print(f"Parsing all {label} NDJSON records ({path.stat().st_size:,} bytes)", file=sys.stderr, flush=True)
        result = ExportAudit(path, targets).run()
        result["file"] = str(path.relative_to(root))
        result["provenance"] = source
        results[label] = result
    solution = results["solution"]
    require(set(solution["axiom_names"]) == standard, "solution does not contain exactly the standard axiom declarations")
    require(not solution["unsafe_or_partial_declarations"], "solution contains unsafe or partial declarations")
    require(not any(any(v.values()) for v in solution["forbidden_name_presence"].values()),
            "solution contains sorryAx or Lean.ofReduceBool")
    solution["axiom_policy"] = {"exactly_standard_three": True, "unpermitted_axioms": [],
                                 "sorryAx_absent": True, "Lean.ofReduceBool_absent": True}
    comparisons = []
    for c, s in zip(results["challenge"]["targets"], solution["targets"]):
        comparisons.append({"theorem": c["name"],
                            "raw_type_structural_digest_equal": c["type"]["structural_sha256"] == s["type"]["structural_sha256"],
                            "note": "A structural digest is an inventory checksum, not definitional equality or a proof check."})
    report = {
        "audit": "Complete streaming NDJSON structure and declaration inventory",
        "status": "pass", "created_utc": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "script": "scripts/audit-exports.py", "script_sha256": file_sha256(Path(__file__)),
        "comparator_config": "comparator.json", "comparator_config_sha256": file_sha256(config_path),
        "configured_targets": targets,
        "format_reference": "Pinned Lean 4.35.0-rc2 LeanExport/Basic.lean and LeanExport/Parse.lean, format 3.1.0",
        "scope": "All NDJSON records, all declared constants including inductive types/constructors/recursors, all expression references, and all three theorem roots in both exports.",
        "limitations": [
            "This script does not invoke Lean, NanoDa, Comparator, or any kernel and does not type-check proofs.",
            "Format 3.1.0 has no end-of-file footer. Completeness is supported by successful export completion records, their hashed logs and recorded byte lengths, complete final JSON lines, contiguous interned IDs, resolved references, and presence of all requested roots.",
            "Structural SHA-256 hashes describe the exported expression DAG using recursively resolved names and universe levels. They include binder names and do not unfold constants or use proof irrelevance; equality or inequality of these digests is not a theorem-equivalence test.",
            "Challenge deliberately includes its three placeholder proofs, so its exported sorryAx is expected. The solution is checked to have no sorryAx or Lean.ofReduceBool name, declaration, or constant expression.",
        ],
        "type_digest_encoding": "SHA-256 of 8-byte-big-endian length-prefixed constructor tag and ordered recursively computed child digests/scalar UTF-8 fields; see script digest() and consume_expr().",
        "target_type_inventory_comparison": comparisons,
        "exports": results,
    }
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": "pass", "report": str(output.relative_to(root)),
                      "report_bytes": output.stat().st_size, "report_sha256": file_sha256(output),
                      "elapsed_seconds": report["elapsed_seconds"],
                      "exports": {label: {key: value[key] for key in ("bytes", "sha256", "ndjson_records", "total_declarations", "axiom_names")}
                                  for label, value in results.items()}}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (AuditError, OSError, KeyError, ValueError) as exc:
        print(f"Export inventory FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
