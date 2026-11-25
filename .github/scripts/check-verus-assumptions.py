#!/usr/bin/env python3
"""追跡中の Rust ソースから、追加の監査が必要な Verus 構文を検出する。"""

from pathlib import Path
import re
import subprocess
import sys


TOKEN = re.compile(
    r"(?P<space>\s+|//[^\n]*)"
    r"|(?P<comment>/\*)"
    r'|(?P<raw>(?:br|cr|r)(?P<hashes>\#*)")'
    r'|(?P<string>[bc]?"(?:[^"\\]|\\[\s\S])*")'
    r"""|(?P<char>b?'(?:[^'\\\r\n\t]|\\(?:[nrt\\'"0]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}))')"""
    r"|(?P<lifetime>'(?:r\#)?[^\W\d]\w*)"
    r"|(?P<ident>(?:r\#)?[^\W\d]\w*)"
    r"|(?P<other>::|.)"
)
COMMENT_MARKER = re.compile(r"/\*|\*/")
VERIFIER_ATTRIBUTES = {
    "assume_termination",
    "exec_allows_no_decreases_clause",
    "external",
    "external_body",
    "external_fn_specification",
    "externals_available_without_declaration",
}


def comment_end(source: str, start: int) -> int:
    depth = 1
    for marker in COMMENT_MARKER.finditer(source, start):
        depth += 1 if marker[0] == "/*" else -1
        if depth == 0:
            return marker.end()
    raise ValueError("unterminated block comment")


def tokens(source: str) -> list[tuple[str, int]]:
    """コメント・リテラルの内容を除き、構文の語と行番号を返す。"""
    result = []
    offset, line = 0, 1
    while offset < len(source):
        token = TOKEN.match(source, offset)
        end = token.end()
        if token.lastgroup == "comment":
            end = comment_end(source, end)
        elif token.lastgroup == "raw":
            closer = '"' + token["hashes"]
            close = source.find(closer, end)
            if close == -1:
                raise ValueError("unterminated raw string")
            end = close + len(closer)
        elif token.lastgroup in {"ident", "other"}:
            result.append((token[0].removeprefix("r#"), line))
        else:
            # リテラルを挟む語が連続した構文と見なされないようにする。
            if token.lastgroup != "space":
                result.append(("", line))
        line += source.count("\n", offset, end)
        offset = end
    return result


def assumptions(source: str) -> list[tuple[int, str]]:
    """複数行や cfg_attr の内側に書かれた属性も検出する。"""
    words = tokens(source) + [("", 0), ("", 0)]
    findings = []
    for index, (word, line) in enumerate(words[:-2]):
        next_word, name = words[index + 1][0], words[index + 2][0]
        if next_word == "::" and (
            (word == "verifier" and name in VERIFIER_ATTRIBUTES)
            or (word == "verus" and name == "trusted")
        ):
            findings.append((line, f"{word}::{name}"))
        elif (
            (word in {"assume", "admit"} and next_word in {"(", "::"})
            or word == "assume_specification"
            or (word == "axiom" and next_word == "fn")
        ):
            findings.append((line, word))
    return findings


def main() -> int:
    paths = subprocess.check_output(["git", "ls-files", "-z", "--", "*.rs"]).decode("utf-8")
    found = False
    count = 0
    for name in filter(None, paths.split("\0")):
        count += 1
        try:
            candidates = assumptions(Path(name).read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            print(f"{name}: unable to audit Rust source: {error}", file=sys.stderr)
            found = True
            continue
        for line, construct in candidates:
            print(f"{name}:{line}: Verus assumption or check bypass: {construct}", file=sys.stderr)
            found = True
    if found:
        return 1
    if count == 0:
        print("No tracked Rust sources to audit.", file=sys.stderr)
        return 1
    print(f"Audited {count} tracked Rust sources.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
