# Interactive explainers

Interactive companions to *Low-discrepancy quasi-uniform digital sequences in every dimension* (version 1, `../paper/`).
Single self-contained HTML files (CSS, JavaScript and data inlined; no network access apart from the plain doi.org /
arxiv.org links of the reference lists). The paper is cited by its LaTeX labels. Certified bounds are truncated,
measured values rounded, and every negative statement is given with its scope, as in the paper.

| page | title | content |
|---|---|---|
| `index.html` | Classical Sequences Cut Corners | what quasi-uniform means (prefix viewer, exact separation of every prefix for random points, Halton, Sobol', Faure and a residue sequence); the carry of `fig:carry`; the exact close pairs of `rem:faurerate` and `cor:sobol` (and the pair of `tab:sobolpar`); `cor:unscrambled`; the Faure offset map against the self-similar brick wall (`tab:faure`, `fig:idea`) |
| `residue.html` | One Scramble Fixes It | residues and the brick wall (`thm:WF`); the residue sequence in 2D and 3D (lattice image plus jitter, `thm:residue`, `fig:residue`); the Korobov bound and an exhaustive check-vector search reproducing `tab:residue`; staggered residue sequences and `cor:dyadic`; block-periodic sequences (`thm:block`(a)) |
| `limits.html` | Limits of Exact Rules | exact digit relations and `thm:count` (the board of `fig:count`); level families (`fig:levels`); windows (`lem:antipode`, `thm:BS`, `fig:HB` with the thresholds of `cor:HB17`, `thm:A3`, `thm:A`); `cor:nodesign`, `prop:joint` |
| `certificate.html` | Certifying Separation | geometric digits, lattice image and jitter (`ex:running`); carries and slip planes (`fig:hierarchy`, `tab:running`); the guaranteed gap (`lem:cert`, `rem:onedigit`); `lem:octave` and the bound of `thm:B2` |
| `practice.html` | Every N in Practice | the minimum separation over 64 ≤ N ≤ 2^23 (`tab:practice`, `fig:evidence`); a live run in 3D (residue sequences, Faure, Owen-scrambled Sobol', random points); digital shifts (`lem:shift`(b)) |

## Files

- `*.html`: the pages, assembled by `build_page.py` from `src/<page>_src.html`, `src/style.css`, `src/core.js`
  (generators, exact separations, λ_jit), `src/refs.json` (the reference lists) and `data.json`.
- `data.json`: values computed by `gen_data.py` with the paper's figure builders (`../paper/scripts/`: exact
  separations by `sepx.cpp`, asserted against the printed values; the drop data of `fig:evidence`; the free-diagonal
  constants of `fig:freediag`; the reference matrices). `check/ref.json`: reference generator matrices from the
  paper's builders, also written by `gen_data.py`. Rerunning `gen_data.py` reproduces both files byte for byte.
- `check/crosscheck.cjs`: runs `src/core.js` under node and checks it against the paper: the JavaScript generators
  against the reference matrices entry by entry, the in-browser exact separations against the precomputed values,
  λ_jit and the bounds of `tab:residue` and `cor:dyadic`, the explicit close pairs, and the certified bounds of
  `tab:practice`.

```sh
g++ -O3 -std=c++17 -o paper/scripts/bin/sepx paper/scripts/sepx.cpp      # once (see paper/scripts/README.md)
uv run --no-project --with numpy --with matplotlib==3.11.0 python explainers/gen_data.py   # data.json, check/ref.json (~5 s)
python3 explainers/build_page.py          # rebuild the pages from src/ and data.json
node explainers/check/crosscheck.cjs      # cross-check (a few seconds)
```

On GitHub Pages (`site/build_site.sh`, `.github/workflows/pages.yml`, started by hand only) the pages are at
<https://lgruen.github.io/quasi-uniform-sequences-lean/explainers/>.

Limits of the browser: exact separations are computed for up to about 4·10^5 points; larger levels are shown from the
precomputed values in `data.json`.
