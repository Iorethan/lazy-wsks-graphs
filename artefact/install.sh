#!/usr/bin/env bash

sudo apt-get update
sudo apt-get install mona
sudo apt-get install git
sudo apt-get install ghc
sudo apt-get install make
sudo apt-get install cabal-install

# The following two commands are necessary only for running of the test suite
sudo apt-get install python3-pip
sudo pip3 install termcolor

sudo add-apt-repository ppa:hvr/ghc
sudo apt-get update
sudo apt-get install ghc-8.4.4
sudo apt-get install cabal-install-2.2
sudo update-alternatives --config opt-ghc
sudo update-alternatives --config opt-cabal

echo "PATH=/opt/ghc/bin:/opt/cabal/bin:\$PATH" >> .bashrc
source .bashrc

git clone https://github.com/vhavlena/lazy-wsks.git
cd lazy-wsks

cabal update
make install
make release
