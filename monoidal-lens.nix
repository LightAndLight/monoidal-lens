{ mkDerivation, base, inspection-testing, lens, stdenv }:
mkDerivation {
  pname = "monoidal-lens";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base inspection-testing lens ];
  license = stdenv.lib.licenses.bsd3;
}
