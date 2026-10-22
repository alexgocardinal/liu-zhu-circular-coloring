from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent.parent
result = subprocess.run(
    ["lake", "env", "lean", "Audit.lean"],
    cwd=root,
    check=True,
    capture_output=True,
    text=True,
)
print(result.stdout, end="")
if result.stderr:
    print(result.stderr, end="")

allowed = {"propext", "Classical.choice", "Quot.sound"}
seen = set()

for line in result.stdout.splitlines():
    match = re.fullmatch(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", line
    )
    if match:
        name, names = match.groups()
        seen.add(name)
        used = {item.strip() for item in names.split(",") if item.strip()}
        unexpected = used - allowed
        if unexpected:
            raise SystemExit(
                f"Unexpected axioms for {name}: {sorted(unexpected)}"
            )
        continue
    match = re.fullmatch(
        r"'([^']+)' does not depend on any axioms", line
    )
    if match:
        seen.add(match.group(1))

required = {
    "CircularColoring.no_coloring33_4",
    "CircularColoring.witness_in_range",
    "CircularColoring.witness_respects_edges",
}
missing = required - seen
if missing:
    raise SystemExit(f"Missing audit results: {sorted(missing)}")

print("Axiom audit passed.")
