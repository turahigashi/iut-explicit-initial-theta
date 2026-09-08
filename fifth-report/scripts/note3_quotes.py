#!/usr/bin/env python3
"""Locate quotation candidates in reader-supplied PDFs at the specified hashes.

Usage: python3 scripts/note3_quotes.py --sources PDF_DIR --manifest scripts/quotes_manifest.json --paper paper/constant_comparison.tex

The manifest must match the manuscript. Matching ignores mathematics and
punctuation and identifies candidates only; inspect each original passage.
Requires pdftotext. Source PDFs are supplied separately by the reader.
"""
import argparse, hashlib, json, re, shutil, subprocess, sys, tempfile, unicodedata, pathlib

SKIP = 80
RARE = 200
MINW = 5
GAP = "\x00gap\x00"

def unlatex(s):
    for pat in (r"\\emph\{([^{}]*)\}", r"\\textbf\{([^{}]*)\}", r"\\text\{([^{}]*)\}"):
        s = re.sub(pat, r"\1", s)
    s = re.sub(r"\\l?dots", GAP, s)
    s = re.sub(r"\$[^$]*\$", " ", s)
    s = re.sub(r"\\[a-zA-Z]+", " ", s)
    return s.replace("{", " ").replace("}", " ")

DASH = r"[\u002d\u00ad\u2010-\u2015\u2212]"

def words(s, join_dashes=True):
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if unicodedata.category(c)[0] != "C" or c in " \n\t" + GAP)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.replace("\ufb01", "fi").replace("\ufb02", "fl")

    s = re.sub(DASH + r"\s*\n\s*", "", s)

    s = re.sub(DASH, "" if join_dashes else " ", s)
    s = s.replace("'", "").replace("\u2019", "").replace("\u2018", "")
    return re.findall(re.escape(GAP) + r"|[a-z0-9]+", s.lower())

def find(needle, hay, index):
    hits = []
    for i in index.get(needle[0], ()):
        pos, budget, ok = i + 1, SKIP, True
        for w in needle[1:]:
            if w == GAP: budget = len(hay); continue
            j = pos
            while j < len(hay) and hay[j] != w and budget > 0:
                j += 1; budget -= 1
            if j >= len(hay) or hay[j] != w: ok = False; break
            pos, budget = j + 1, min(budget, SKIP)
        if ok: hits.append(i)
    return hits

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--sources", required=True)
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--paper", default="paper/constant_comparison.tex",
                    help="the manuscript the manifest must match, quotation for quotation")
    ap.add_argument("--json")
    a = ap.parse_args()
    man = json.loads(pathlib.Path(a.manifest).read_text())

    paper = pathlib.Path(a.paper)
    if paper.is_file():
        body = re.sub(r"(?<!\\)%.*", "", paper.read_text())
        cur = [" ".join(m.group(1).split()) for m in re.finditer(r"``(.+?)\'\'", body, re.S)]
        have = [q["tex"] for q in man["quotations"]]
        if cur != have:
            print(f"  manifest describes {len(have)} quotations, {paper} contains "
                  f"{len(cur)}; they are not the same list, so nothing here has been "
                  f"checked against the current manuscript")
            for i, (x, y) in enumerate(zip(have, cur), 1):
                if x != y:
                    print(f"    first difference at {i}:\n      manifest: {x[:70]}\n"
                          f"      paper   : {y[:70]}"); break
            return 2
    else:

        print(f"  {paper} not present; the manifest cannot be matched against a "
              f"manuscript, so nothing can be checked"); return 2
    if not shutil.which("pdftotext"):
        print("  pdftotext not found; cannot extract the sources"); return 2
    srcs, index, freq = {}, {}, {}
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="note3_quotes_"))
    for name, meta in man["sources"].items():
        pdf = pathlib.Path(a.sources) / meta["pdf"]
        if not pdf.is_file():
            print(f"  missing source: {pdf}"); return 2
        got = hashlib.sha256(pdf.read_bytes()).hexdigest()
        if got != meta["sha256"]:
            print(f"  {name}: SHA-256 {got[:16]}... does not match the manifest's "
                  f"{meta['sha256'][:16]}...; that is a different printing, and a "
                  f"quotation checked against it has not been checked"); return 2
        p = tmp / (name + ".txt")
        subprocess.run(["pdftotext", "-layout", str(pdf), str(p)], check=True)
        raw = p.read_text(errors="ignore")
        for mode in (True, False):
            w = words(raw, mode)
            srcs[(name, mode)] = w
            d = {}
            for i, t in enumerate(w): d.setdefault(t, []).append(i)
            index[(name, mode)] = d
            if mode:
                for t in set(w): freq[t] = freq.get(t, 0) + w.count(t)
    rep, bad = [], 0
    for q in man["quotations"]:
        core = [w for w in words(unlatex(q["tex"])) if w != GAP]
        checkable = len(core) >= MINW and any(freq.get(w, 0) <= RARE for w in core)
        found = {}
        if checkable:
            for (k, mode) in srcs:
                h = find(words(unlatex(q["tex"]), mode), srcs[(k, mode)], index[(k, mode)])
                if h:
                    g = man["sources"][k].get("group", k)
                    found[g] = max(found.get(g, 0), len(h))

        if q.get("kind") == "self": st = "SELF"
        elif not checkable: st = "NOCHECK"
        elif q["source"] and q["source"] in found: st = "CANDIDATE"
        elif q["source"]: st = "NOT IN CITED SOURCE"
        elif found: st = "CANDIDATE"
        else: st = "NOT FOUND"
        bad += st in ("NOT FOUND", "NOT IN CITED SOURCE")
        rep.append({**q, "status": st, "found": found})
        print(f'{st:20s} [{q["n"]:2d}] cited={str(q["source"] or "-"):6s} '
              f'found={found or "-"}  {q["tex"][:44]}')
    c = lambda s: sum(r["status"] == s for r in rep)
    print(f'\n{len(rep)} quotations: {c("CANDIDATE")} located in the cited source, '
          f'{c("NOT IN CITED SOURCE")} NOT located there, '
          f'{c("NOT FOUND")} not located at all, '
          f'{c("NOCHECK")} too short or too generic for this search, '
          f'{c("SELF")} the paper quoting its own earlier wording.')
    print('"Located" means a word-sequence candidate was found, with mathematics dropped '
          'and punctuation ignored.  It is not a verdict of verbatim identity: each '
          'candidate still needs an eye on the source.')
    if a.json: pathlib.Path(a.json).write_text(json.dumps(rep, ensure_ascii=False, indent=1))
    return 1 if bad else 0

if __name__ == "__main__":
    raise SystemExit(main())
