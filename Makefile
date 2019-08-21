#
# Makefile for WSkS decision procedure written in Haskell
# Author: Vojtech Havlena, 2018
#

all:
	cd src && make

install:
	cabal install --only-dependencies

release:
	cd src && make release

test:
	cd src && make test

clean:
	cd src && make clean
