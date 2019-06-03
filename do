#!/bin/sh

case "$1" in
  "build")
    cabal v2-build all
    ;;
  "dev")
    case "$2" in
      "z3-effect")
        ghcid -c "cabal v2-repl z3-effect" --restart z3-effect/z3-effect.cabal
        ;;
      "zzz")
        ghcid -c "cabal v2-repl zzz" --restart zzz/zzz.cabal
        ;;
    esac
    ;;
  "repl")
    case "$2" in
      "z3-effect")
        cabal v2-repl z3-effect
        ;;
      "zzz")
        cabal v2-repl zzz
        ;;
    esac
    ;;
esac
