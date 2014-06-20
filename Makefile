.PHONY: hoq

FLAGS = \
	-fwarn-incomplete-patterns \
	-fwarn-unused-imports \

hoq:
	cabal build --ghc-options="$(FLAGS)"
