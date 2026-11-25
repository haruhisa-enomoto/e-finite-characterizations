#!/usr/bin/env python3
"""Build the mathematical website from handwritten pages and the actual Lean statement."""
import html
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAGES = {"index": "Overview", "statement": "Statement", "proof": "Proof guide",
         "library": "Library", "api": "API", "verification": "Verification"}
DECLARATIONS = [
    ('equivalences_arbitraryField', 'Characterizations/Equivalences', 'The seventeen arbitrary-field tests'),
    ('equivalences_infiniteField', 'Characterizations/Equivalences', 'Counting bricks and stable bricks by composition vector'),
    ('equivalences_algebraicallyClosedField', 'Characterizations/Equivalences', 'Three geometric tests'),
    ('rankTwoEquivalences', 'Silting/Fans/RankTwoTauTilting', 'Brick-finiteness and τ-tilting finiteness in rank at most two'),
    ('brick_discrete_iff_multiplicityFree', 'Geometry/ComponentMultiplicity', 'Weyman’s conjecture'),
    ('isEFinite_iff_torsionFreeMonoids_cancellative', 'GrothendieckGroups/MonoidCancellation', 'Cancellation in torsion-free classes'),
    ('isEFinite_of_artin_epi_targets', 'RingEpimorphisms/ArtinTargets', 'Artin targets of Tor-vanishing epimorphisms'),
]


def main():
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
    repo_url = "https://github.com/haruhisa-enomoto/e-finite-characterizations"
    source_url = repo_url + "/blob/" + ("main" if dirty else commit)
    source = (ROOT / "EFiniteCharacterizations/Characterizations/Equivalences.lean").read_text()
    statement = source[source.index("variable (k R"):source.index("/-- The seventeen")].strip()
    for block in source.split("/-- ")[1:]:
        statement += "\n\n/-- " + block.split(" := by\n")[0]
    output = ROOT / "_site"
    output.mkdir(exist_ok=True)
    shutil.copytree(ROOT / "website/assets", output / "assets", dirs_exist_ok=True)
    api = ROOT / "docbuild/.lake/build/doc"
    api_state_path = ROOT / "docbuild/.lake/build/api-build.json"
    api_state = json.loads(api_state_path.read_text()) if api_state_path.exists() else {}
    has_api = (api / "index.html").exists() and api_state.get("complete", False)
    if has_api:
        for revisions in ([api_state["source_commit"], "HEAD"], ["HEAD"]):
            subprocess.run(["git", "diff", "--exit-code", *revisions, "--",
                            "EFiniteCharacterizations.lean", "EFiniteCharacterizations",
                            "lean-toolchain", "lake-manifest.json"],
                           cwd=ROOT, check=True)
        # A source migration can delete modules; discard stale generated pages.
        if (output / "api").exists():
            shutil.rmtree(output / "api")
        shutil.copytree(api, output / "api")
        for page in (output / "api").rglob("*.html"):
            overview = Path(os.path.relpath(output / "index.html", page.parent)).as_posix()
            page.write_text(page.read_text().replace(
                "<span>Documentation</span>",
                f'<span><a href="{overview}">Characterizations of E-finite algebras</a></span>', 1))
    elif (output / "api").exists():
        shutil.rmtree(output / "api")
    status_file = ROOT / "verification-status.json"
    status = json.loads(status_file.read_text()) if status_file.exists() else {}
    rows = []
    for declaration, module, description in DECLARATIONS:
        path = "EFiniteCharacterizations/" + module
        target = ("api/" + path + ".html#EFiniteCharacterizations." + declaration) if has_api else source_url + "/" + path + ".lean"
        rows.append(f'<tr><td><a href="{target}"><code>{declaration}</code></a></td><td>{description}</td></tr>')
    replacements = {
        "source_url": source_url,
        "repo_url": repo_url,
        "statement": html.escape(statement),
        "statement_lines": str(len(statement.splitlines())),
        "declaration_rows": "".join(rows),
        "api_link": '<p><a href="api/index.html">Browse and search the generated API</a></p>' if has_api else
                    '<p>The API has not been generated in this preview. Follow <code>docbuild/README.md</code> to build the documentation tool, run <code>python3 scripts/build_api.py</code>, then rebuild this site.</p>',
        "verification_status": html.escape(status.get("summary", "Verification records are available in the repository.")),
    }
    nav = "".join(f'<a href="{slug}.html">{label}</a>' for slug, label in PAGES.items())
    nav += f'<a href="{repo_url}">GitHub</a>'
    revision = f'<a href="{repo_url}/tree/{commit}">{commit[:7]}</a>' + (" (preview)" if dirty else "")
    api_revision = (f' · API: <a href="{repo_url}/tree/{api_state["source_commit"]}">{api_state["source_commit"][:7]}</a>') if has_api else ""
    for slug, title in PAGES.items():
        body = (ROOT / f"website/pages/{slug}.html").read_text()
        for key, value in replacements.items():
            body = body.replace("{{" + key + "}}", value)
        if "{{" in body:
            raise SystemExit(f"Unresolved template value in {slug}")
        page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} · Characterizations of E-finite algebras</title><link rel="stylesheet" href="assets/site.css"></head>
<body><a class="skip" href="#main">Skip to content</a><header class="site-header"><nav class="nav" aria-label="Main"><a class="brand" href="index.html">Characterizations of E-finite algebras</a>{nav}</nav></header>
<main id="main">{body}</main><footer class="site-footer">Source: {revision}{api_revision}<br>Haruhisa Enomoto · Lean formalization · Apache-2.0</footer></body></html>'''
        (output / f"{slug}.html").write_text(page)
    (output / "build.json").write_text(json.dumps({"commit": commit, "dirty": dirty,
        "api_generated": has_api, "api_source_commit": api_state.get("source_commit") if has_api else None,
        "statement_lines": len(statement.splitlines())}, indent=2) + "\n")
    print(f"Built {len(PAGES)} pages in {output}")


if __name__ == "__main__":
    main()
