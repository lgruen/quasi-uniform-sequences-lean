# Explainers

A step-by-step series on the residue sequences of *Low-discrepancy quasi-uniform digital sequences in every
dimension* (version 1, `../paper/`), written from the ground up for computer science students: why the classical
sequences fail, and how one fixed scramble makes the points stay apart at every scale. **In progress**; the plan and
the tutor notes are in [`tutor/COURSE.md`](tutor/COURSE.md). The earlier five interactive pages are in the git
history and in the v1.0.0 release.

## Files

- `NN-*.html`: the steps (added as they are written); `index.html`: the overview.
- `tutor/COURSE.md`: the spine of the series for a reader or an LLM tutor: audience, arc, per-step notes and
  check questions, progress.
- `src/core.js`: generators, exact separations and λ_jit in JavaScript, shared by the pages; `src/refs.json`:
  references.
- `data.json`, `check/ref.json`: written by `gen_data.py` from the paper's figure builders (`../paper/scripts/`).
- `check/crosscheck.cjs`: checks `src/core.js` against the paper's numbers and reference matrices.

```sh
uv run --no-project --with numpy --with matplotlib==3.11.0 python explainers/gen_data.py   # data.json, check/ref.json
node explainers/check/crosscheck.cjs      # cross-check (a few seconds)
```

On GitHub Pages (`site/build_site.sh`, `.github/workflows/pages.yml`, started by hand only) the pages are at
<https://lgruen.github.io/quasi-uniform-sequences-lean/explainers/>.
