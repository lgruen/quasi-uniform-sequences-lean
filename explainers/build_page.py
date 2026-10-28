# build_page.py -- assemble the self-contained explainer pages: src/<page>_src.html + src/style.css + src/core.js +
# data.json (from gen_data.py) + src/refs.json -> <page>.html next to this file.  Placeholders in the sources: __CSS__,
# __CORE__, __DATA__, __BIB__.  At __BIB__ the reference list is inserted: every entry of src/refs.json that the page
# links to with href="#ref-KEY", sorted by author and year (an unknown key is an error).  The output has no external
# fetches (system fonts, inline script and data); the only external URLs are the doi.org / arxiv.org links of the
# reference list, which are plain links.
#   run:  python3 `explainers/build_page.py
import os, json, re, html
H = os.path.dirname(os.path.abspath(__file__))
PAGES = ("index", "residue", "limits", "certificate", "practice")
css = open(os.path.join(H, "src", "style.css")).read()
core = open(os.path.join(H, "src", "core.js")).read()
data = json.dumps(json.load(open(os.path.join(H, "data.json"))), separators=(",", ":"))
refs = {k: v for k, v in json.load(open(os.path.join(H, "src", "refs.json"))).items() if not k.startswith("_")}
LINK = re.compile(r'href="https://(?:doi\.org|arxiv\.org/abs)/[^"\s]+"')


def surname(a):
    return a.split(",")[0].split()[-1]


def bib(src):
    keys = sorted(set(re.findall(r'href="#ref-([A-Za-z0-9]+)"', src)), key=lambda k: (surname(refs[k]["a"]) if k in refs else k, refs.get(k, {}).get("y", ""), k))
    missing = [k for k in keys if k not in refs]
    assert not missing, ("unknown reference keys", missing)
    out = []
    for k in keys:
        r = refs[k]
        e = lambda s: html.escape(s, quote=False)
        s = f'{e(r["a"])}. <i>{e(r["t"])}</i>. {e(r["v"])}, {e(r["y"])}.'
        links = []
        if r.get("doi"):
            links.append(f'<a href="https://doi.org/{r["doi"]}">doi:{e(r["doi"])}</a>')
        if r.get("arxiv"):
            links.append(f'<a href="https://arxiv.org/abs/{r["arxiv"]}">arXiv:{e(r["arxiv"])}</a>')
        if links:
            s += " " + ", ".join(links) + "."
        if r.get("extra"):
            s += " " + e(r["extra"])
        out.append(f'<li id="ref-{k}">{s}</li>')
    return '<ol class="bib">\n' + "\n".join(out) + "\n</ol>"


for page in PAGES:
    fn = os.path.join(H, "src", f"{page}_src.html")
    if not os.path.exists(fn):
        print(f"{page}: no source, skipped")
        continue
    src = open(fn).read()
    for k in ("__CSS__", "__CORE__", "__DATA__", "__BIB__"):
        assert src.count(k) == 1, (page, k)
    src = src.replace("__BIB__", bib(src))
    out = src.replace("__CSS__", css).replace("__DATA__", data.replace("</", "<\\/")).replace("__CORE__", core)
    rest = LINK.sub("", out).replace("http://www.w3.org/2000/svg", "")
    assert "http://" not in rest and "https://" not in rest, page
    open(os.path.join(H, f"{page}.html"), "w").write(out)
    nref = src.count('<li id="ref-')
    print(f"{page}.html {len(out) // 1024} KB, {nref} references")
