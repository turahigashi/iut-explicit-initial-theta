#!/usr/bin/env python3
"""Check every quoted passage of note3 against the sources, by search.

The paper's own attribution is NOT used to decide where to look: each quotation is
searched in every source, so a misattribution appears as "found in X, cited as Y".

Hazards handled, each of which produced a false answer in an earlier version of this
script and was found by hand-checking its output rather than by trusting it:

  * text extraction interleaves floats, so arbitrary material sits between the parts
    of a quotation that surround an inline formula -- absorbed by a skip budget;
  * a hyphen at a line break joins two words ("log-linkcompatible"), so hyphens are
    removed from both sides before tokenizing rather than treated as separators;
  * characters that only NFKD turns into spaces sit inside words, so "Definition 1.1"
    was not findable at all until the sources were NFKD-normalized;
  * dropping inline mathematics can leave a word sequence so generic ("the image in
    ... of the submodule of ... invariants of ...") that the skip budget makes it
    match almost anywhere: one quotation was reported in the wrong source this way.
    A needle must now carry at least one word that is rare in the corpus.
  * an ellipsis in a quotation marks omitted source text of unbounded length.

Usage:  python3 note3_quotes.py --sources DIR --manifest manifest.json

DIR holds the reader's own copies of the sources, as PDFs named in the manifest.  This
program extracts the text itself and checks each PDF's SHA-256 against the manifest,
refusing to run on a printing the manifest does not name: an earlier version recorded
those hashes and never looked at them, so it would happily report a match found in a
different edition (external review, 2026-09-08).

WHAT A MATCH DOES AND DOES NOT ESTABLISH.  The search is a word-sequence match that
drops inline mathematics and ignores brackets, punctuation and case.  It therefore
locates a CANDIDATE passage; it does not establish verbatim identity.  It cannot see a
quotation that stops early inside the source's own bracket without an ellipsis, that
drops a qualifying clause, or that alters a formula -- external review found one of
each while this program reported them as found.  Every candidate still needs an eye.
"""
import argparse, hashlib, json, re, shutil, subprocess, sys, tempfile, unicodedata, pathlib

SKIP = 80                 # words of interleaved formula/float absorbed between words
RARE = 200                # a needle needs one word occurring at most this often
MINW = 5                  # and at least this many words, to be checkable at all
GAP = "\x00gap\x00"       # an ellipsis: unbounded omission (lower case:
                          # .lower() turned an upper-case marker into the
                          # ordinary word "gap" and every ellipsis stopped
                          # the search dead)

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
    # Every dash-like character, not just ASCII hyphen: the source uses U+2010..U+2015
    # and U+2212, which NFKD leaves alone, so removing only "-" made the two sides
    # disagree and turned six correct quotations into misses.
    s = re.sub(DASH + r"\s*\n\s*", "", s)      # hyphenation across a line break
    # Text extraction is ambiguous about hyphens: a line-break hyphen joins two words
    # ("log-linkcompatible"), while dropping an inline formula next to a hyphenated
    # compound splits one ("$0$-column" -> "column" against the source's "0-column").
    # Removing dashes fixes the first and breaks the second; treating them as
    # separators does the reverse.  So both readings are tried, and a quotation counts
    # as found if either succeeds.
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
    ap.add_argument("--paper", default="paper/note3.tex",
                    help="the manuscript the manifest must match, quotation for quotation")
    ap.add_argument("--json")
    a = ap.parse_args()
    man = json.loads(pathlib.Path(a.manifest).read_text())
    # The manifest must still describe the manuscript.  It had silently drifted three
    # quotations behind after an edit, so the search was checking strings the paper no
    # longer contained (external review, 2026-09-08).
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
        # Continuing here would report on a manifest nobody has matched against a
        # manuscript, which is the failure this gate exists to prevent.
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
        # The question is whether the quotation stands verbatim in the source the
        # paper cites.  A hit in some other source is reported, but it is never a
        # substitute: with inline mathematics dropped a short quotation can be a
        # generic word sequence that matches almost anywhere.
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
