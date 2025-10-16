{
  mkDerivation,
  standard-library,
  standard-library-classes,
  standard-library-meta,
  abstract-set-theory,
  iog-prelude,
}:
mkDerivation {
  pname = "cardano-common";
  version = "+";
  src = ../.;
  meta = { };
  libraryFile = "cardano-common.agda-lib";
  buildInputs = [
    standard-library
    standard-library-classes
    standard-library-meta
    abstract-set-theory
    iog-prelude
  ];
}
