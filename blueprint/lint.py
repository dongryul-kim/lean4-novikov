#!/usr/bin/env python3
"""Check Lean links and the integrity of the blueprint dependency graph."""

from pathlib import Path
import re
import sys


NODE_KINDS = "definition|lemma|theorem|proposition|corollary"
NODE_PATTERN = re.compile(
    rf"\\begin\{{(?P<kind>{NODE_KINDS})\}}"
    rf"(?P<body>.*?)"
    rf"\\end\{{(?P=kind)\}}",
    re.DOTALL,
)
LEAN_PATTERN = re.compile(r"\\lean\s*\{")
LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")
USES_PATTERN = re.compile(r"\\uses\{([^}]*)\}", re.DOTALL)
MAIN_THEOREM_LABEL = "thm:novikov_descent_equivalence"


def main() -> int:
    repository = Path(__file__).resolve().parent.parent
    sections = repository / "blueprint" / "src" / "sections"
    documents = [
        (path, path.read_text(encoding="utf-8"))
        for path in sorted(sections.glob("*.tex"))
    ]
    errors: list[str] = []

    def location(path: Path, text: str, offset: int) -> str:
        line = text.count("\n", 0, offset) + 1
        return f"{path.relative_to(repository)}:{line}"

    label_locations: dict[str, list[str]] = {}
    for path, text in documents:
        for label in LABEL_PATTERN.finditer(text):
            label_locations.setdefault(label.group(1), []).append(
                location(path, text, label.start())
            )
    for label, locations in label_locations.items():
        if len(locations) > 1:
            errors.append(
                f"duplicate label {label!r} at {', '.join(locations)}"
            )

    completed = 0
    dependency_count = 0
    graph: dict[str, list[str]] = {}
    graph_locations: dict[str, str] = {}

    for path, text in documents:
        for node in NODE_PATTERN.finditer(text):
            body = node.group("body")
            node_location = location(path, text, node.start())
            label_match = LABEL_PATTERN.search(body)
            label = label_match.group(1) if label_match else None

            if r"\leanok" in body:
                completed += 1
                if label is None:
                    errors.append(
                        f"{node_location}: completed {node.group('kind')} has no label"
                    )
                if not LEAN_PATTERN.search(body):
                    errors.append(
                        f"{node_location}: completed {node.group('kind')} "
                        "has no \\lean annotation"
                    )

            dependencies: list[str] = []
            for uses in USES_PATTERN.finditer(body):
                dependencies.extend(
                    dependency.strip()
                    for dependency in uses.group(1).split(",")
                    if dependency.strip()
                )
            dependency_count += len(dependencies)

            seen: set[str] = set()
            for dependency in dependencies:
                if dependency in seen:
                    errors.append(
                        f"{node_location}: duplicate dependency {dependency!r}"
                    )
                seen.add(dependency)
                if dependency not in label_locations:
                    errors.append(
                        f"{node_location}: undefined dependency {dependency!r}"
                    )
                if label is not None and dependency == label:
                    errors.append(
                        f"{node_location}: node depends on itself ({label!r})"
                    )

            if label is not None:
                graph.setdefault(label, dependencies)
                graph_locations.setdefault(label, node_location)

    state: dict[str, int] = {}
    stack: list[str] = []
    cycle: list[str] | None = None

    def visit(label: str) -> bool:
        nonlocal cycle
        state[label] = 1
        stack.append(label)
        for dependency in graph.get(label, []):
            if dependency not in graph:
                continue
            if state.get(dependency, 0) == 0:
                if visit(dependency):
                    return True
            elif state[dependency] == 1:
                start = stack.index(dependency)
                cycle = stack[start:] + [dependency]
                return True
        stack.pop()
        state[label] = 2
        return False

    for label in graph:
        if state.get(label, 0) == 0 and visit(label):
            assert cycle is not None
            errors.append(
                f"{graph_locations[label]}: dependency cycle: "
                + " -> ".join(cycle)
            )
            break

    if MAIN_THEOREM_LABEL not in graph:
        errors.append(f"missing main theorem node {MAIN_THEOREM_LABEL!r}")
    else:
        ancestors: set[str] = set()
        pending = [MAIN_THEOREM_LABEL]
        while pending:
            label = pending.pop()
            for dependency in graph.get(label, []):
                if dependency in graph and dependency not in ancestors:
                    ancestors.add(dependency)
                    pending.append(dependency)
        disconnected = sorted(
            set(graph) - ancestors - {MAIN_THEOREM_LABEL}
        )
        for label in disconnected:
            errors.append(
                f"{graph_locations[label]}: node {label!r} is not a dependency "
                f"of the main theorem {MAIN_THEOREM_LABEL!r}"
            )

    if errors:
        print("Blueprint lint failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(
        "Blueprint lint passed "
        f"({completed} completed nodes, {len(label_locations)} labels, "
        f"{dependency_count} dependency edges, one connected DAG)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
