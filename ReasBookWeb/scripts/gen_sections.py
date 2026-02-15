#!/usr/bin/env python3
"""Generate ReasBookSite/Sections.lean from the current ReasBook module tree."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
import json

SITE_BASE = "https://optsuite.github.io/ReasBook/"
DOCS_BASE = f"{SITE_BASE}docs/"
GITHUB_SOURCE_BASE = "https://github.com/optsuite/ReasBook/blob/main/ReasBook/"

BOOK_TITLES = {
    "ConvexAnalysis_Rockafellar_1970": "Convex Analysis (Rockafellar, 1970)",
    "IntegerProgramming_Conforti_2014": "Integer Programming (Conforti et al., 2014)",
    "Analysis2_Tao_2022": "Analysis II (Tao, 2022)",
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": "Introduction to Real Analysis, Volume I (Jiri Lebl, 2025)",
}

PAPER_TITLES = {
    "SmoothMinimization_Nesterov_2004": "Smooth Minimization (Nesterov, 2004)",
    "OnSomeLocalRings_Maassaran_2025": "On Some Local Rings (Maassaran, 2025)",
}

BOOK_CHAPTER_TITLES = {
    "Analysis2_Tao_2022": {
        1: "Metric Spaces",
        2: "Continuous Functions on Metric Spaces",
        3: "Uniform Convergence",
        4: "Power Series",
        5: "Fourier Series",
        6: "Several Variable Differential Calculus",
    },
    "ConvexAnalysis_Rockafellar_1970": {
        1: "Part I: Basic Concepts",
        2: "Part II: Topological Properties",
        3: "Part III: Duality Correspondences",
        4: "Part IV: Representation and Inequalities",
    },
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": {
        1: "Real Numbers",
        2: "Sequences and Series",
        3: "Continuous Functions",
        4: "The Derivative",
        5: "The Riemann Integral",
        6: "Sequences of Functions",
        7: "Metric Spaces",
    },
}

BOOK_SECTION_TITLES = {
    "Analysis2_Tao_2022": {
        1: {
            1: "Definitions and Examples",
            2: "Some Point-Set Topology of Metric Spaces",
            3: "Relative Topology",
            4: "Cauchy Sequences and Complete Metric Spaces",
            5: "Compact Metric Spaces",
        },
        2: {
            1: "Continuous Functions",
            2: "Continuity and Product Spaces",
            3: "Continuity and Compactness",
            4: "Continuity and Connectedness",
            5: "Topological Spaces (Optional)",
        },
        3: {
            1: "Limiting Values of Functions",
            2: "Pointwise and Uniform Convergence",
            3: "Uniform Convergence and Continuity",
            4: "The Metric of Uniform Convergence",
            5: "Series of Functions; the Weierstrass M-Test",
            6: "Uniform Convergence and Integration",
            7: "Uniform Convergence and Derivatives",
            8: "Uniform Approximation by Polynomials",
        },
        4: {
            1: "Formal Power Series",
            2: "Real Analytic Functions",
            3: "Abel's Theorem",
            4: "Multiplication of Power Series",
            5: "The Exponential and Logarithm Functions",
            6: "A Digression on Complex Numbers",
            7: "Trigonometric Functions",
        },
        5: {
            1: "Periodic Functions",
            2: "Inner Products on Periodic Functions",
            3: "Trigonometric Polynomials",
            4: "Periodic Convolutions",
            5: "The Fourier and Plancherel Theorems",
        },
        6: {
            1: "Linear Transformations",
            2: "Derivatives in Several Variable Calculus",
        },
    },
    "ConvexAnalysis_Rockafellar_1970": {
        1: {1: "Affine Sets", 2: "Convex Sets and Cones", 3: "The Algebra of Convex Sets", 4: "Convex Functions"},
        2: {
            5: "Functional Operations",
            6: "Relative Interiors of Convex Sets",
            7: "Closures of Convex Functions",
            8: "Recession Cones and Unboundedness",
            9: "Some Closedness Criteria",
            10: "Continuity of Convex Functions",
        },
        3: {
            11: "Separation Theorems",
            12: "Conjugates of Convex Functions",
            13: "Support Functions",
            14: "Polars of Convex Sets",
            15: "Polars of Convex Functions",
            16: "Dual Operations",
        },
        4: {
            17: "Caratheodory's Theorem",
            18: "Extreme Points and Faces of Convex Sets",
            19: "Polyhedral Convex Sets and Functions",
            20: "Some Applications of Polyhedral Convexity",
        },
    },
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": {
        1: {
            1: "Basic Properties",
            2: "The Set of Real Numbers",
            3: "Absolute Value and Bounded Functions",
            4: "Intervals and the Size of R",
            5: "Decimal Representation of the Reals",
        },
        2: {
            1: "Sequences and Limits",
            2: "Facts About Limits of Sequences",
            3: "Limit Superior, Limit Inferior, and Bolzano-Weierstrass",
            4: "Cauchy Sequences",
            5: "Series",
            6: "More on Series",
        },
        3: {
            1: "Limits of Functions",
            2: "Continuous Functions",
            3: "Extreme and Intermediate Value Theorems",
            4: "Uniform Continuity",
            5: "Limits at Infinity",
            6: "Monotone Functions and Continuity",
        },
        4: {
            1: "The Derivative",
            2: "Mean Value Theorem",
            3: "Taylor's Theorem",
            4: "Inverse Function Theorem",
        },
        5: {
            1: "The Riemann Integral",
            2: "Properties of the Integral",
            3: "Fundamental Theorem of Calculus",
            4: "The Logarithm and the Exponential",
            5: "Improper Integrals",
        },
        6: {
            1: "Pointwise and Uniform Convergence",
            2: "Interchange of Limits",
            3: "Picard's Theorem",
        },
        7: {
            1: "Metric Spaces",
            2: "Open and Closed Sets",
            3: "Sequences and Convergence",
            4: "Completeness and Compactness",
            5: "Continuous Functions",
            6: "Fixed Point Theorem and Picard's Theorem Again",
        },
    },
}

PAPER_SECTION_TITLES = {
    "SmoothMinimization_Nesterov_2004": {
        1: "Introduction",
        2: "Smooth Approximations of Non-differentiable Functions",
        3: "Fast Gradient Methods",
        4: "Applications",
        5: "Implementation Issues and Modifications",
    },
    "OnSomeLocalRings_Maassaran_2025": {
        1: "Separable Case",
        2: "Lifting the Isomorphisms",
    },
}

TBD_BOOKS = {"IntegerProgramming_Conforti_2014"}

SKIP_STEMS = {"utils", "tactics", "scratch", "internal", "helper", "helpers"}

CHAPTER_RE = re.compile(r"^(?:chapter_|chap)(\d+)$", re.IGNORECASE)
SECTION_RE = re.compile(r"^section_?(\d+)$", re.IGNORECASE)
PART_RE = re.compile(r"^part_?(\d+)$", re.IGNORECASE)


@dataclass(frozen=True)
class Entry:
    category: str
    module: str
    title: str
    route: str
    book_or_paper: str
    chapter_num: int
    section_num: int
    part_num: int
    stem: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "repo_root",
        nargs="?",
        default=None,
        help="Path to the ReasBook repo root (the directory containing ReasBookWeb/ and ReasBook/).",
    )
    return parser.parse_args()


def humanize_identifier(s: str) -> str:
    s = s.replace("_", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return s.title() if s else s


def module_doc_title(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    m = re.search(r"/(?:-!|--)\s*(.*?)\s*-/", text, re.DOTALL)
    if not m:
        return None
    body = m.group(1)
    lines = []
    for raw in body.splitlines():
        line = raw.strip().lstrip("#").strip()
        if not line:
            continue
        if line.startswith("import "):
            continue
        lines.append(line)
    if not lines:
        return None
    first = lines[0]
    if len(first) > 60:
        return None
    if "`" in first or ":" in first or "." in first:
        return None
    if len(first.split()) > 8:
        return None
    if not re.match(r"^(Section|Chapter|Appendix)\\b", first, re.IGNORECASE):
        return None
    return first


def chapter_number(parts: Iterable[str]) -> int:
    for p in parts:
        m = CHAPTER_RE.match(p)
        if m:
            return int(m.group(1))
    return 0


def chapter_title(parts: Iterable[str]) -> str | None:
    for p in parts:
        m = CHAPTER_RE.match(p)
        if m:
            return f"Chapter {int(m.group(1)):02d}"
    return None


def chapter_title_for_book(book: str, chapter_num: int) -> str:
    named = BOOK_CHAPTER_TITLES.get(book, {}).get(chapter_num)
    if named:
        return f"Chapter {chapter_num:02d} -- {named}"
    return f"Chapter {chapter_num:02d}"


def parse_section_part(stem: str) -> tuple[int, int]:
    section_num = 0
    part_num = 0
    lower = stem.lower()
    for token in lower.split("_"):
        ms = SECTION_RE.match(token)
        if ms:
            section_num = int(ms.group(1))
            continue
        mp = PART_RE.match(token)
        if mp:
            part_num = int(mp.group(1))
    m2 = re.match(r"section(\d+)", lower)
    if m2:
        section_num = int(m2.group(1))
    m3 = re.search(r"part(\d+)", lower)
    if m3:
        part_num = int(m3.group(1))
    return section_num, part_num


def section_title_from_stem(stem: str) -> str:
    lower = stem.lower()
    if lower in {"paper", "main"}:
        return "Overview"

    sec, part = parse_section_part(stem)
    if sec > 0:
        base = f"Section {sec:02d}"
        if part > 0:
            return f"{base} -- Part {part}"
        return base

    return humanize_identifier(stem)


def entry_label(e: Entry) -> str:
    if e.category == "books":
        section_titles = BOOK_SECTION_TITLES.get(e.book_or_paper, {}).get(e.chapter_num, {})
        if e.section_num in section_titles and e.part_num == 0:
            return section_titles[e.section_num]
    if e.category == "papers":
        paper_titles = PAPER_SECTION_TITLES.get(e.book_or_paper, {})
        if e.section_num in paper_titles and e.part_num == 0:
            return paper_titles[e.section_num]
    if e.part_num > 0:
        return ""
    return section_title_from_stem(e.stem)


def readme_label(e: Entry) -> str:
    base = entry_label(e)
    if not base:
        return ""
    if e.category == "books":
        return f"{e.chapter_num}.{e.section_num} {base}"
    if e.category == "papers":
        return f"Section {e.section_num}: {base}"
    return base


def book_title(book: str) -> str:
    if book in BOOK_TITLES:
        return BOOK_TITLES[book]
    return humanize_identifier(book)


def paper_title(paper: str) -> str:
    if paper in PAPER_TITLES:
        return PAPER_TITLES[paper]
    return humanize_identifier(paper)


def to_module(source_root: Path, path: Path) -> str:
    rel = path.relative_to(source_root)
    return ".".join(rel.with_suffix("").parts)


def normalize_path(path: str) -> str:
    path = path.strip()
    if not path:
        return ""
    has_trailing_slash = path.endswith("/")
    pieces = [piece for piece in path.split("/") if piece]
    if not pieces:
        return ""
    out = "/".join(pieces)
    if has_trailing_slash:
        out += "/"
    return out


def route_from_module(module: str) -> str:
    return normalize_path("/".join(part.lower() for part in module.split(".")) + "/")


def should_include_book(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False

    parts_lower = [p.lower() for p in path.parts]
    in_chapter_tree = any(CHAPTER_RE.match(p) for p in parts_lower)
    if not in_chapter_tree:
        return False

    if stem.startswith("section"):
        return True

    return module_doc_title(path) is not None


def should_include_paper(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False
    if stem in {"paper", "main"}:
        return True
    return stem.startswith("section")


def collect_entries(source_root: Path) -> list[Entry]:
    entries: list[Entry] = []

    books_root = source_root / "Books"
    papers_root = source_root / "Papers"

    for path in sorted(books_root.rglob("*.lean")):
        if not should_include_book(path):
            continue
        rel = path.relative_to(books_root)
        book = rel.parts[0]
        if book in TBD_BOOKS:
            continue
        ch_title = chapter_title(rel.parts)
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
        title_parts = [book_title(book)]
        if ch_title:
            title_parts.append(ch_title)
        title_parts.append(sec_title)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="books",
                module=to_module(source_root, path),
                title=" -- ".join(title_parts),
                route=route_from_module(to_module(source_root, path)),
                book_or_paper=book,
                chapter_num=chapter_number(rel.parts),
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
            )
        )

    for path in sorted(papers_root.rglob("*.lean")):
        if not should_include_paper(path):
            continue
        rel = path.relative_to(papers_root)
        paper = rel.parts[0]
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="papers",
                module=to_module(source_root, path),
                title=f"{paper_title(paper)} -- {sec_title}",
                route=route_from_module(to_module(source_root, path)),
                book_or_paper=paper,
                chapter_num=0,
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
            )
        )

    entries.sort(
        key=lambda e: (
            0 if e.category == "books" else 1,
            e.book_or_paper.lower(),
            e.chapter_num,
            e.section_num,
            e.part_num,
            e.stem,
        )
    )
    return entries


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_sections(entries: list[Entry]) -> str:
    books: dict[str, dict] = {}
    papers: dict[str, dict] = {}
    for e in entries:
        if e.section_num <= 0 or e.part_num > 0:
            continue
        if e.category == "books":
            target = books
        elif e.category == "papers":
            target = papers
        else:
            continue

        key = e.book_or_paper
        if key not in target:
            target[key] = {
                "slug": key.lower(),
                "title": book_title(key) if e.category == "books" else paper_title(key),
                "sections": [],
            }

        if e.category == "books":
            chapter_label = chapter_title_for_book(e.book_or_paper, e.chapter_num)
            label = f"{chapter_label} -- {entry_label(e)}"
        else:
            label = entry_label(e)
        target[key]["sections"].append({"title": label, "route": e.route})

    payload = {"books": [books[k] for k in sorted(books)], "papers": [papers[k] for k in sorted(papers)]}
    sidebar_json = json.dumps(payload, ensure_ascii=True, separators=(",", ":"))

    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("namespace ReasBookSite.Sections")
    lines.append("")
    lines.append("def sections : Array (Lean.Name × String) := #[")
    for e in entries:
        lines.append(f"  (`{e.module}, {lean_string(e.title)}),")
    lines.append("]")
    lines.append("")
    lines.append("def routes : Array (String × Lean.Name) := #[")
    for e in entries:
        lines.append(f"  ({lean_string(e.route)}, `{e.module}),")
    lines.append("]")
    lines.append("")
    lines.append(f"def sidebarDataJson : String := {lean_string(sidebar_json)}")
    lines.append("")
    lines.append("end ReasBookSite.Sections")
    lines.append("")
    return "\n".join(lines)


def emit_route_table(entries: list[Entry]) -> str:
    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("import VersoBlog")
    lines.append("import ReasBookSite.Home")
    lines.append("import Book")
    lines.append("")
    lines.append("open Verso Genre Blog Site Syntax")
    lines.append("")
    lines.append("namespace ReasBookSite.RouteTable")
    lines.append("")
    lines.append("scoped syntax \"reasbook_site_dir\" : dir_spec")
    lines.append("")
    lines.append("macro_rules")
    lines.append("  | `(dir_spec| reasbook_site_dir) =>")
    lines.append("    `(dir_spec| /")
    lines.append('      static "static" ← "./static_files"')
    for e in entries:
        lines.append(f"      {lean_string(e.route)} Book.{e.module}")
    lines.append("    )")
    lines.append("")
    lines.append("def reasbook_site : Site := site ReasBookSite.Home /")
    lines.append('  static "static" ← "./static_files"')
    for e in entries:
        lines.append(f"  {lean_string(e.route)} Book.{e.module}")
    lines.append("")
    lines.append("end ReasBookSite.RouteTable")
    lines.append("")
    return "\n".join(lines)


def doc_link(module: str) -> str:
    return f"{DOCS_BASE}{module.replace('.', '/')}.html"


def source_link(module: str) -> str:
    return f"{GITHUB_SOURCE_BASE}{module.replace('.', '/')}.lean"


def verso_link(route: str) -> str:
    return f"{SITE_BASE}{route}"


def write_book_readmes(source_root: Path, entries: list[Entry]) -> None:
    books_root = source_root / "Books"
    all_books = sorted([p.name for p in books_root.iterdir() if p.is_dir()])

    by_book: dict[str, list[Entry]] = {book: [] for book in all_books}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)

    for book in all_books:
        title = book_title(book)
        book_module = f"Books.{book}.Book"
        book_file = books_root / book / "Book.lean"
        item_entries = sorted(
            [e for e in by_book.get(book, []) if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.part_num, e.stem),
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        if book in TBD_BOOKS:
            out.append("- Links: Verso (TBD) | Documentation (TBD) | Lean source (TBD)")
        else:
            verso_target = verso_link(item_entries[0].route) if item_entries else f"{SITE_BASE}books/{book.lower()}/"
            links = [
                f"[Verso]({verso_target})",
                f"[Documentation]({doc_link(book_module)})",
            ]
            if book_file.exists():
                links.append(
                    f"[Lean source]({GITHUB_SOURCE_BASE}Books/{book}/Book.lean)"
                )
            else:
                links.append(
                    f"[Lean source]({GITHUB_SOURCE_BASE}Books/{book}/)"
                )
            out.append(f"- Links: {' | '.join(links)}")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no chapter/section modules discovered yet)")
            out.append("")
        else:
            current_chapter = None
            for e in item_entries:
                if current_chapter != e.chapter_num:
                    current_chapter = e.chapter_num
                    out.append(f"## {chapter_title_for_book(book, current_chapter)}")
                    out.append("")
                label = readme_label(e)
                if not label:
                    continue
                out.append(
                    f"- {label} "
                    f"([Verso]({verso_link(e.route)})) "
                    f"([Documentation]({doc_link(e.module)})) "
                    f"([Lean source]({source_link(e.module)}))"
                )
            out.append("")

        readme = books_root / book / "README.md"
        readme.write_text("\n".join(out), encoding="utf-8")
        print(f"Wrote {readme}")


def write_paper_readmes(source_root: Path, entries: list[Entry]) -> None:
    papers_root = source_root / "Papers"
    all_papers = sorted([p.name for p in papers_root.iterdir() if p.is_dir()])

    by_paper: dict[str, list[Entry]] = {paper: [] for paper in all_papers}
    for e in entries:
        if e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)

    for paper in all_papers:
        title = paper_title(paper)
        paper_file = papers_root / paper / "Paper.lean"
        if paper_file.exists():
            paper_module = f"Papers.{paper}.Paper"
        else:
            paper_module = f"Papers.{paper}.Main"
        item_entries = sorted(
            [e for e in by_paper.get(paper, []) if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.section_num, e.part_num, e.stem),
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        verso_target = verso_link(item_entries[0].route) if item_entries else f"{SITE_BASE}papers/{paper.lower()}/"
        links = [
            f"[Verso]({verso_target})",
            f"[Documentation]({doc_link(paper_module)})",
        ]
        if paper_file.exists():
            links.append(
                f"[Lean source]({GITHUB_SOURCE_BASE}Papers/{paper}/Paper.lean)"
            )
        else:
            links.append(
                f"[Lean source]({GITHUB_SOURCE_BASE}Papers/{paper}/Main.lean)"
            )
        out.append(f"- Links: {' | '.join(links)}")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no section modules discovered yet)")
            out.append("")
        else:
            out.append("## Sections")
            out.append("")
            for e in item_entries:
                label = readme_label(e)
                if not label:
                    continue
                out.append(
                    f"- {label} "
                    f"([Verso]({verso_link(e.route)})) "
                    f"([Documentation]({doc_link(e.module)})) "
                    f"([Lean source]({source_link(e.module)}))"
                )
            out.append("")

        readme = papers_root / paper / "README.md"
        readme.write_text("\n".join(out), encoding="utf-8")
        print(f"Wrote {readme}")


def main() -> None:
    args = parse_args()
    if args.repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    else:
        repo_root = Path(args.repo_root).resolve()

    source_root = repo_root / "ReasBook"
    out_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "Sections.lean"
    route_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "RouteTable.lean"

    if not (source_root / "lakefile.lean").exists() and not (source_root / "lakefile.toml").exists():
        raise SystemExit(f"Lean project not found at {source_root}")

    entries = collect_entries(source_root)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(emit_sections(entries), encoding="utf-8")
    route_file.write_text(emit_route_table(entries), encoding="utf-8")
    write_book_readmes(source_root, entries)
    write_paper_readmes(source_root, entries)
    print(f"Wrote {out_file} with {len(entries)} sections")
    print(f"Wrote {route_file} with generated route macro")


if __name__ == "__main__":
    main()
