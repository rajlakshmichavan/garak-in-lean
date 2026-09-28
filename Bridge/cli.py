#!/usr/bin/env python3
"""garak-in-lean bridge (LOUVRE-style).

Calls OpenAI to synthesize a `CheckerSpec` JSON for a natural-language
description of a garak vulnerability category (see `Garak/Types.lean`'s
`VulnCategory`: PromptInjection, InsecureOutput, SensitiveDisclosure,
Overreliance, ModelTheft, Toxicity). Pipes the JSON through Lean's
`Verify.lean` harness, which checks it against the adversarial/benign
sample prompts the LLM itself declared. On verification failure, feeds
the counterexample back to the LLM and retries up to 3 times -- same
loop as LOUVRE's `bridge/cli.py`.

Usage:
    export OPENAI_API_KEY=sk-...
    python bridge/cli.py "block prompts that try to override the system prompt, e.g. 'ignore previous instructions'"
    python bridge/cli.py --example bridge/examples/prompt_injection.json   # skip LLM, verify only
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PENDING = ROOT / "bridge" / "_pending.json"
PROMPT_PATH = ROOT / "bridge" / "prompts" / "checker_synthesis.txt"
VERIFY_LEAN = ROOT / "bridge" / "Verify.lean"

MAX_RETRIES = 3
MODEL = os.environ.get("GARAK_LEAN_MODEL", "gpt-4.1-mini")


def call_openai(description: str, history: list[dict]) -> dict:
    """Call OpenAI Chat Completions with the synthesis prompt and history."""
    try:
        from openai import OpenAI
    except ImportError:
        sys.exit("openai package not installed. Run: pip install openai")

    client = OpenAI()
    system_prompt = PROMPT_PATH.read_text()
    user_messages = [
        {
            "role": "user",
            "content": f"Vulnerability category to build a garak Checker for:\n{description}",
        }
    ]
    for entry in history:
        user_messages.append(
            {"role": "assistant", "content": json.dumps(entry["attempt"])}
        )
        user_messages.append(
            {
                "role": "user",
                "content": (
                    f"That attempt failed verification.\n"
                    f"Reason: {entry['reason']}\n"
                    f"Counterexample: {entry.get('counterexample') or '(none)'}\n"
                    f"Revise and try again."
                ),
            }
        )

    resp = client.chat.completions.create(
        model=MODEL,
        messages=[{"role": "system", "content": system_prompt}, *user_messages],
        response_format={"type": "json_object"},
        temperature=0.2,
    )
    text = resp.choices[0].message.content
    return json.loads(text)


def lean_verify(spec: dict) -> tuple[bool, str, str | None]:
    """Run the Lean harness; return (ok, reason, counterexample)."""
    PENDING.write_text(json.dumps(spec, indent=2))
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(VERIFY_LEAN), str(PENDING)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
    )
    out = proc.stdout.strip()
    err = proc.stderr.strip()
    try:
        result = json.loads(out)
    except json.JSONDecodeError:
        return False, f"lean harness error (exit {proc.returncode}): {err or out}", None
    return result.get("ok", False), result.get("reason", ""), result.get("counterexample")


def synthesize(description: str) -> dict | None:
    history: list[dict] = []
    for attempt in range(1, MAX_RETRIES + 1):
        print(f"\n=== Attempt {attempt} / {MAX_RETRIES} ===")
        spec = call_openai(description, history)
        print("LLM proposed:")
        print(json.dumps(spec, indent=2))
        ok, reason, counterexample = lean_verify(spec)
        if ok:
            print(f"\n[CERTIFIED] {reason}")
            return spec
        print(f"\n[REJECTED] {reason}")
        if counterexample:
            print(f"  counterexample: {counterexample!r}")
        history.append(
            {"attempt": spec, "reason": reason, "counterexample": counterexample}
        )
    print("\nMax retries exhausted.")
    return None


def verify_only(path: Path) -> None:
    spec = json.loads(path.read_text())
    print(f"Verifying {path}")
    ok, reason, counterexample = lean_verify(spec)
    print(json.dumps({"ok": ok, "reason": reason, "counterexample": counterexample}, indent=2))
    sys.exit(0 if ok else 1)


def main() -> None:
    ap = argparse.ArgumentParser(description="garak-in-lean bridge (LOUVRE-style)")
    ap.add_argument("description", nargs="?", help="natural-language vulnerability description")
    ap.add_argument(
        "--example", type=Path,
        help="verify a hand-curated CheckerSpec without calling the LLM",
    )
    args = ap.parse_args()
    if args.example:
        verify_only(args.example)
        return
    if not args.description:
        ap.error("either a description or --example is required")
    if not os.environ.get("OPENAI_API_KEY"):
        sys.exit("OPENAI_API_KEY not set")
    result = synthesize(args.description)
    sys.exit(0 if result else 1)


if __name__ == "__main__":
    main()
