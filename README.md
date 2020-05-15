# HTabDyn, a hybrid logic and relation-changing logic tableau prover

HTabDyn is a tableau-based satisfiability checker. It currently
handles the hybrid logic H(:,E,down-arrow) with role inclusions,
and terminates on input within any fragments that exclude the down-arrow operator.

Relevant references for HTabDyn are [1] and [2] for the general tableau algorithm
and [3] for the pattern-based blocking and lazy branching technique currently used.

## Downloading

Download the source code of HTabDyn either using Darcs:

    darcs clone --lazy http://hub.darcs.net/gh/htabdyn

Or [downloading the source code as a zip file](http://hub.darcs.net/gh/htabdyn/dist)
and unpacking it.

## Compiling and using

To build HTabDyn, you will need GHC and either [cabal-install](https://wiki.haskell.org/Cabal-Install)
or [stack](http://www.haskellstack.org/).
Dependencies, including [hylolib](http://hackage.haskell.org/package/hylolib),
will be downloaded and compiled automatically.

A help is available by running:

    htabdyn --help

## Example of use with Relation-Changing formulas

The `--translate` flag interprets input formulas as Relation-Changing ones,
and translates them to Hybrid Logic. There is no guarantee that HTab will
terminate on such formulas since they are translated to HL(:,E,down-arrow).

Example formulas are provided in the `./rc/`.

The following command runs the translation and hybrid tableau algorithm
on the input formula `swap_no_tree` introduced in [3] :

    htabdyn --translate -f rc/swap_no_tree.frm

Since the translation preserve equivalence, it is interesting to have
a look at the model created from an open branch.

The `-m mod` flag writes a model into the `mod` file
(if the formula is satisfiable). It does so in a specific format
undestandable by HTab and Hylolib. Using the `-d` flag, one can ask
Htab to generate the model into the dot graphviz format:

    htabdyn --translate -f rc/swap_no_tree.frm -d -m mod
    dot mod -Tpdf -O
    evince mod.pdf

If some relation-changing formula makes HTab run forever, you may want to
use the flag `--sembranch=no` to disable the semantic branching technique,
which can be problematic in the presence of many nominals and binders:

    htabdyn --translate -f rc/swap_diamond.frm --sembranch=no -d -m mod

[1] https://cs.famaf.unc.edu.ar/~hoffmann/publi/2009_m4m_htab.pdf
[2] https://cs.famaf.unc.edu.ar/~hoffmann/publi/2010_jal.pdf
[3] http://www.ps.uni-saarland.de/papers/abstracts/GoetzmannKaminskiSmolkaSpartacus.pdf
[4] https://cs.famaf.unc.edu.ar/~hoffmann/publi/2013_swap_igpl.pdf
