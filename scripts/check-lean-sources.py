#!/usr/bin/env python3
"""Check source requirements before builds; full Palomar verification is still required.

Header and file-size scanners follow PalomarSubmission/source_requirements.py.
The project additionally permits exactly three deliberate statement holes in the merged
independent Challenge file, and rejects proof holes or custom trust
commands elsewhere. Comparator remains responsible for the dependency audit.
"""
import os
import re
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
# Lean 4 Init/Meta/Defs.lean identifier characters; Python Unicode classes
# are broader. A qualified identifier also continues across a dot.
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")
TRUST_TOKEN = re.compile(
    rf"(?<![{ID_REST}.])(?:sorryAx|sorry|admit|axiom|native_decide|(?:Lean\.)?ofReduceBool)"
    rf"(?![{ID_REST}]|\.[{ID_FIRST}«])"
)
DECLARATION = re.compile(
    rf"(?<![{ID_REST}.])(theorem|lemma|def|opaque|instance|abbrev)\s+"
    rf"([{ID_FIRST}][{ID_REST}.]*)"
)
CHALLENGE_HOLES = {
    "Challenge.lean": ["main_theorem", "numerical_main_theorem", "structural_main_theorem"],
}


def code_only(text: str) -> str:
    """Mask comments, string literals and quoted names, preserving offsets.

    This is a conservative lexical safeguard, not a replacement for Lean's
    parser or the kernel/export audit. Nested comments and raw string literals
    are handled so documentation cannot look like a forbidden proof command.
    """
    chars = list(text)
    index = 0
    while index < len(text):
        start = index
        if text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end
        elif text.startswith("/-", index):
            index += 2
            depth = 1
            while depth and index < len(text):
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        elif text[index] == "«":
            end = text.find("»", index + 1)
            index = len(text) if end < 0 else end + 1
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        elif text[index] == "r" and re.match(r'r#+"', text[index:]):
            opener = re.match(r'r(#+)"', text[index:])
            terminator = '"' + opener.group(1)
            end = text.find(terminator, index + opener.end())
            index = len(text) if end < 0 else end + len(terminator)
        else:
            index += 1
            continue
        for position in range(start, min(index, len(chars))):
            if chars[position] != "\n":
                chars[position] = " "
    return "".join(chars)


def proof_policy_errors(relative: str, text: str) -> list[str]:
    """Permit exactly the declared theorem placeholders in the Challenge."""
    code = code_only(text)
    tokens = list(TRUST_TOKEN.finditer(code))
    expected = CHALLENGE_HOLES.get(relative)
    errors = []
    holes = [token for token in tokens if token.group() == "sorry"]
    for token in tokens:
        if expected is not None and token.group() == "sorry":
            continue
        line = text.count("\n", 0, token.start()) + 1
        errors.append(f"{relative}:{line}: forbidden proof/trust token {token.group()}")
    if expected is not None:
        found = []
        for hole in holes:
            declarations = list(DECLARATION.finditer(code[:hole.start()]))
            if not declarations or declarations[-1].group(1) != "theorem":
                errors.append(f"{relative}: a placeholder is outside a theorem declaration")
            else:
                found.append(declarations[-1].group(2))
        if sorted(found) != sorted(expected):
            errors.append(f"{relative}: expected one placeholder in each of {expected}; found {found}")
    return errors


def has_module_header(text: str) -> bool:
    """Recognize the initial marker, without confusing comments with headers.

    Documentation comments are commands, not header whitespace. Do not strip a
    BOM or arbitrary Unicode whitespace: Lean's header parser does not either.
    This cheap check precedes installation; execute confirms with --deps-json.
    """
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            # Lean consumes the character after the plain opener before
            # scanning its body (unlike nested openers). Match its parser.
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    """LF/CRLF lines; an unterminated final line counts, a final LF adds none."""
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    """Lean source paths, including contained projects and symlinks to reject.

    Lake configuration shares the line cap, but is exempt from module headers.
    Never traverse symlinks or Git internals.
    """
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = False
    files = lean_source_files(root)
    for path in files:
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
        if str(relative) in CHALLENGE_HOLES:
            if physical_lines(text) > 1_000 or len(text.encode("utf-8")) > 100 * 1024:
                print(f"{relative}: exceeds the Challenge limit of 1,000 lines or 100 KiB")
                failed = True
        for error in proof_policy_errors(str(relative), text):
            print(error)
            failed = True
    for challenge in CHALLENGE_HOLES:
        if not (root / challenge).is_file():
            print(f"{challenge}: required independent statement module is missing")
            failed = True
    if not failed:
        print(f"Checked {len(files)} Lean sources; no proof holes outside the {sum(map(len, CHALLENGE_HOLES.values()))} declared Challenge placeholders.")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
