# Artefact evaluation

To run the tool install all necessary packages mentioned in the main README
file. Or [download virtual
machine](http://www.fit.vutbr.cz/~lengal/public/trusty.ova) and install all
required packages (from `install.sh`).

CADE benchmarks:
* [ws2s] tree-constant
* [ws2s] tree-sub-lr
* [ws2s] path

In the project root folder you can run experiments using
```
python3 experimental/experimental.py src/LazyWSkS mona benchmarks/\[ws2s\]\ tree-sub-lr/ -f n
```
where `n` is a number of formulas. For space evaluation change `experimental.py`
for `experimental-space.py`.
