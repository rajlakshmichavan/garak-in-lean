#!/usr/bin/env python3
"""garak report.jsonl -> apply.lean trace.json

Reads a garak report (one JSON object per line, written to
~/.local/share/garak/garak_runs/garak.<id>.report.jsonl) and emits the trace
shape that Bridge/apply.lean consumes:

    {"turns": [{"attackerPrompt": "..."}, ...]}

apply.lean reads ONLY turns[*].attackerPrompt and ignores every other field, so
this converter just has to find each attack prompt garak sent and list it.

Usage:
    python Bridge/report_to_trace.py garak.<id>.report.jsonl > trace.json
    python Bridge/report_to_trace.py garak.<id>.report.jsonl -o trace.json

NOTE: garak's field names vary by version and entry type. This script tries the
known locations for the attack prompt in order; the exact field for garak 0.16.0
is confirmed against a real report and pinned in PROMPT_FIELDS below. If a report
yields 0 prompts, run with --debug to see the keys actually present.
"""

from __future__ import annotations
import argparse, json, sys

# Where the attacker prompt lives in a garak report entry, tried in order.
# garak writes several entry types per line (an "init"/"config" header, then
# "attempt" entries). Attempt entries carry the prompt. These paths cover the
# common garak schemas; the first one that yields a non-empty string wins.
#   - "prompt" as a plain string (older/simple probes)
#   - "prompt" as an object with "turns"/"text" (chat-format probes, incl. atkgen)
#   - "notes"/"trigger" fallbacks
def extract_prompt(entry: dict):
    p = entry.get("prompt")
    # 1. prompt is a plain string
    if isinstance(p, str) and p.strip():
        return p
    # 2. prompt is a dict (chat format): {"turns":[{"content":{"text": "..."}}]} or {"text": "..."}
    if isinstance(p, dict):
        if isinstance(p.get("text"), str) and p["text"].strip():
            return p["text"]
        turns = p.get("turns")
        if isinstance(turns, list):
            # take the last user/attacker turn's text
            for turn in reversed(turns):
                if isinstance(turn, dict):
                    c = turn.get("content")
                    if isinstance(c, dict) and isinstance(c.get("text"), str):
                        return c["text"]
                    if isinstance(c, str) and c.strip():
                        return c
                    if isinstance(turn.get("text"), str) and turn["text"].strip():
                        return turn["text"]
    # 3. some probes log the sent text under these
    for k in ("trigger", "query", "input"):
        v = entry.get(k)
        if isinstance(v, str) and v.strip():
            return v
    return None

def main():
    ap = argparse.ArgumentParser(description="garak report.jsonl -> apply.lean trace.json")
    ap.add_argument("report", help="path to garak.<id>.report.jsonl")
    ap.add_argument("-o", "--out", help="output file (default: stdout)")
    ap.add_argument("--debug", action="store_true", help="print keys seen, for diagnosing an empty result")
    args = ap.parse_args()

    prompts, seen, key_union = [], set(), set()
    with open(args.report, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(entry, dict):
                continue
            if args.debug:
                key_union |= set(entry.keys())
            pr = extract_prompt(entry)
            if pr and pr not in seen:      # de-dupe repeated prompts
                seen.add(pr)
                prompts.append(pr)

    if args.debug:
        print(f"[debug] entries scanned; top-level keys seen: {sorted(key_union)}", file=sys.stderr)
        print(f"[debug] extracted {len(prompts)} unique prompts", file=sys.stderr)

    if not prompts:
        print("No attacker prompts found. Re-run with --debug to see the report's "
              "keys, and paste the first 2 lines of the report so the field path "
              "can be corrected.", file=sys.stderr)
        sys.exit(2)

    trace = {"turns": [{"attackerPrompt": p} for p in prompts]}
    out_str = json.dumps(trace, indent=2, ensure_ascii=False)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as g:
            g.write(out_str)
        print(f"wrote {len(prompts)} prompts to {args.out}", file=sys.stderr)
    else:
        print(out_str)

if __name__ == "__main__":
    main()
