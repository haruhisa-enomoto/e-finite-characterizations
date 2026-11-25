#!/usr/bin/env python3
"""Build the static companion website from website/pages/*.html and the Lean sources."""
import html
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAGES = {
    "index": "Overview",
    "statement": "Statements",
    "proof": "Proof guide",
    "library": "Library",
    "api": "API",
    "verification": "Verification",
}

# (qualified declaration under EFiniteCharacterizations, module path under EFiniteCharacterizations/, role)
DECLARATIONS = [
    ("equivalences_arbitraryField", "Characterizations/Equivalences",
     "Theorem A(I): seventeen equivalent characterizations of E-finiteness over an arbitrary field"),
    ("equivalences_infiniteField", "Characterizations/Equivalences",
     "Theorem A(II) (Corollary 5.4): dimension-vector characterizations (dim-brick) and (dim-stab) over infinite fields"),
    ("equivalences_algebraicallyClosedField", "Characterizations/Equivalences",
     "Theorem A(III) (Theorem 6.1): King moduli closed points, open brick orbits, and open wide loci over k = k̄"),
    ("seven_pointwise_implications", "Characterizations/BrickFiniteness",
     "Per-algebra equivalence of the seven brick-finiteness conjectures (i)–(vii)"),
    ("rankTwoEquivalences", "Silting/Fans/RankTwoTauTilting",
     "Theorem B (Theorem 8.4): E-finiteness ⇔ τ-tilting finiteness ⇔ brick-finiteness in rank n ≤ 2"),
    ("brick_discrete_iff_multiplicityFree", "Geometry/ComponentMultiplicity",
     "Corollary C (Weyman's conjecture): Schur-representation-finiteness (dim-brick) ⇔ multiplicity-freeness"),
    ("proveArbitraryField", "MainTheorems",
     "Bridge proving the standalone Mathlib-only Statement.ArbitraryField"),
    ("TwoTerm.rationally_independent_stable_classes_in_cone", "Stability/ConeTorsionPairs",
     "Proposition 2.3: linear independence of dimension vectors of stable bricks at weights in C°(U)"),
    ("TwoTerm.minimal_image_stable_at_corrected_class", "Stability/MissingWeightWitnesses",
     "Proposition 2.7: minimal-image bricks at a missing weight g ∉ Σ(Λ) and their corrected stability weight"),
    ("exists_rationally_dependent_stable_semibrick", "Stability/RationalExtraction",
     "Theorem 3.1: extracting a jointly stable dependent semibrick when Hom_Λ(M, N) = 0 for [M] = [N] ≠ 0"),
    ("isEFinite_iff_injective_torsionMonoid", "GrothendieckGroups/TorsionMonoidEmbedding",
     "Theorem 4.1, (mon-dim): injectivity of M(T) → K₀(mod Λ) for every torsion class T"),
    ("isEFinite_iff_torsionFreeMonoids_cancellative", "GrothendieckGroups/MonoidCancellation",
     "Corollary 4.3: E-finiteness ⇔ cancellativity of Grothendieck monoids of all torsion-free (or torsion) classes"),
    ("exists_presilting_perpendicular_of_wide", "Subcategories/WidePerpendicular",
     "Theorem 5.1, (wide): every wide subcategory over an E-finite algebra is a τ-perpendicular category J(U)"),
    ("isEFinite_iff_brickLabels", "Subcategories/BrickLabels",
     "Theorem 5.1, (brick-label): every brick labels a cover T' ⋖ T in f-tors Λ via Filt(B) = T ∩ (T')⊥"),
    ("right_brick_count_le_of_isEFinite", "Stability/SharpBrickGrowth",
     "Theorem 5.2, (poly-brick): explicit cumulative bound 2(n - 1)(m + 1)^{n(n - 1)} for bricks of length ≤ m"),
    ("no_generic_right_brick_of_isEFinite", "LargeModules/GenericBrickExclusion",
     "Lemma 7.3, (no-gen-brick): exclusion of generic bricks over E-finite algebras via rank reduction"),
    ("isEFinite_iff_no_genericGrain", "LargeModules/GenericGrainCriterion",
     "Proposition 7.6 & Theorem 7.8, (no-gen-grain): generic grains constructed via Malcev–Neumann series"),
    ("isEFinite_iff_boundedProjectiveThickGeneration", "Silting/ThickSubcategories/BoundedProjectiveHomotopy",
     "Proposition 7.5 & Theorem 7.8, (thick-gen): presilting generation of thick subcategories of K^{[-1,0]}(proj Λ)"),
    ("rightUniversalLocalizationsFinite_of_isEFinite", "RingEpimorphisms/UniversalLocalization",
     "Theorem 7.8, (univ-loc): finite-dimensionality of arbitrary universal localizations via presilting pencils"),
    ("isEFinite_of_artin_epi_targets", "RingEpimorphisms/ArtinTargets",
     "Corollary 7.9: ring epimorphisms with Tor₁^Λ(Γ, Γ) = 0 and Artin algebra targets"),
    ("TwoTerm.sternBrocot_plane_test_and_count", "Silting/Fans/SternBrocot",
     "Proposition 8.3: finite Stern–Brocot mediant test and bound 2^x + 2^y + 2 on two-term silting complexes"),
    ("FieldExtension.absolute_frobenius_correspondence", "ScalarExtension/AbsoluteFrobeniusCorrespondence",
     "Lemma A.2: bijection between ground stable bricks and Frobenius orbits of geometric stable bricks"),
]


def extract_equivalences_signatures(source: str) -> str:
    header = source[source.index("variable (k R"):source.index("/--", source.index("variable (k R"))].strip()
    blocks = [header]
    for block in source.split("/-- ")[1:]:
        blocks.append("/-- " + block.split(" := by\n")[0])
    return "\n\n".join(blocks)


def main():
    subprocess.run(["python3", str(ROOT / "scripts/generate_challenge.py"), "--check"], check=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
    repo_url = "https://github.com/haruhisa-enomoto/e-finite-characterizations"
    source_url = repo_url + "/blob/" + ("main" if dirty else commit)

    equiv_source = (ROOT / "EFiniteCharacterizations/Characterizations/Equivalences.lean").read_text()
    statement = extract_equivalences_signatures(equiv_source)
    challenge = (ROOT / "Challenge.lean").read_text()

    output = ROOT / "_site"
    output.mkdir(exist_ok=True)
    shutil.copytree(ROOT / "website/assets", output / "assets", dirs_exist_ok=True)

    api = ROOT / "docbuild/.lake/build/doc"
    api_state_path = ROOT / "docbuild/.lake/build/api-build.json"
    api_state = json.loads(api_state_path.read_text()) if api_state_path.exists() else {}
    has_api = (api / "index.html").exists() and api_state.get("complete", False)
    if has_api:
        for revisions in ([api_state["source_commit"], "HEAD"], ["HEAD"]):
            subprocess.run(
                ["git", "diff", "--exit-code", *revisions, "--",
                 "EFiniteCharacterizations.lean", "EFiniteCharacterizations",
                 "lean-toolchain", "lake-manifest.json"],
                cwd=ROOT, check=True,
            )
        if (output / "api").exists():
            shutil.rmtree(output / "api")
        shutil.copytree(api, output / "api")
        for page in (output / "api").rglob("*.html"):
            overview = Path(os.path.relpath(output / "index.html", page.parent)).as_posix()
            page.write_text(page.read_text().replace(
                "<span>Documentation</span>",
                f'<span><a href="{overview}">Characterizations of E-finite algebras</a></span>', 1,
            ))
    elif (output / "api").exists():
        shutil.rmtree(output / "api")

    status_file = ROOT / "verification-status.json"
    status = json.loads(status_file.read_text()) if status_file.exists() else {}

    rows = []
    for declaration, module, description in DECLARATIONS:
        path = "EFiniteCharacterizations/" + module
        target = (
            f"api/{path}.html#EFiniteCharacterizations.{declaration}"
            if has_api
            else f"{source_url}/{path}.lean"
        )
        short_mod = module.split("/")[-1]
        rows.append(
            f'<tr><td><a href="{target}"><code>{html.escape(declaration)}</code></a>'
            f'<br><small style="color:var(--muted)">{html.escape(short_mod)}.lean</small></td>'
            f'<td>{html.escape(description)}</td></tr>'
        )

    replacements = {
        "source_url": source_url,
        "repo_url": repo_url,
        "statement": html.escape(statement),
        "statement_lines": str(len(statement.splitlines())),
        "challenge": html.escape(challenge),
        "challenge_lines": str(len(challenge.splitlines())),
        "declaration_rows": "".join(rows),
        "api_link": (
            '<div class="actions"><a class="button primary" href="api/index.html">'
            'Open searchable doc-gen4 API (389 modules)</a></div>'
            if has_api
            else '<p class="callout">The generated API is not present in this local preview. '
                 'Follow <code>docbuild/README.md</code>, run <code>python3 scripts/build_api.py</code>, '
                 'and rebuild the site.</p>'
        ),
        "verification_status": html.escape(
            status.get("summary", "Verification records are archived in verification/.")
        ),
    }

    revision = f'<a href="{repo_url}/tree/{commit}"><code>{commit[:7]}</code></a>' + (" (working preview)" if dirty else "")
    api_revision = (
        f' · API built from <a href="{repo_url}/tree/{api_state["source_commit"]}">'
        f'<code>{api_state["source_commit"][:7]}</code></a>'
        if has_api else ""
    )

    for slug, title in PAGES.items():
        nav_items = []
        for s, label in PAGES.items():
            cur = ' aria-current="page"' if s == slug else ""
            nav_items.append(f'<a href="{s}.html"{cur}>{label}</a>')
        nav_items.append(f'<a href="{repo_url}">GitHub ↗</a>')
        nav = "".join(nav_items)

        body = (ROOT / f"website/pages/{slug}.html").read_text()
        for key, value in replacements.items():
            body = body.replace("{{" + key + "}}", value)
        if "{{" in body:
            raise SystemExit(f"Unresolved template value in {slug}.html")

        page = f'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>{title} · Characterizations of E-finite algebras</title>
  <link rel="stylesheet" href="assets/site.css">
</head>
<body>
  <a class="skip" href="#main">Skip to main content</a>
  <header class="site-header">
    <nav class="nav" aria-label="Primary">
      <a class="brand" href="index.html">E-finite Algebras · Lean 4</a>{nav}
    </nav>
  </header>
  <main id="main">
{body}
  </main>
  <footer class="site-footer">
    <div>Haruhisa Enomoto · Lean 4 formalization (<a href="{source_url}/LICENSE">Apache-2.0</a>)</div>
    <div>Commit {revision}{api_revision}</div>
  </footer>
</body>
</html>
'''
        (output / f"{slug}.html").write_text(page)

    (output / "build.json").write_text(json.dumps({
        "commit": commit,
        "dirty": dirty,
        "api_generated": has_api,
        "api_source_commit": api_state.get("source_commit") if has_api else None,
        "statement_lines": len(statement.splitlines()),
        "challenge_lines": len(challenge.splitlines()),
    }, indent=2) + "\n")
    print(f"Built {len(PAGES)} pages in {output}")


if __name__ == "__main__":
    main()
