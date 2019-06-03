#!/bin/sh

case "$1" in
  "z3-effect")
    case "$2" in
      "dev")
        ghcid -c "cabal v2-repl z3-effect" --restart z3-effect/z3-effect.cabal
        ;;
      "repl")
        cabal v2-repl z3-effect
        ;;
    esac
    ;;
  "zzz")
    case "$2" in
      "dev")
        ghcid -c "cabal v2-repl zzz" --restart zzz/zzz.cabal
        ;;
      "repl")
        cabal v2-repl zzz
        ;;
    esac
    ;;
esac
