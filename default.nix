{ nixpkgs ?  <nixpkgs> }:

with (import nixpkgs {});

agdaPackages.mkDerivation {
  version = "0.1.0";
  pname = "kit-theory";
  src = ./.;
  buildInputs = [
    agdaPackages.standard-library
    myAgdaPackages.reflection-lib
  ];

  libraryName = "kit-theory";  # has to match the .agda-lib
  everythingFile = "src/KitTheory/Everything.agda";  # defaults to "Everything.agda"
  # libraryFile = "";  # defaults to `${libraryName}.agda-lib`

  # If this library does not use an Everything.agda file and instead has a
  # Makefile, then there is no need to set everythingFile and we set a custom
  # buildPhase:
  #
  # buildPhase = ''
  #   patchShebangs find-deps.sh
  #   make
  # '';

  meta = {
    description = ".";
    # homepage = http://;
    license = "GPLv2";
    # maintainers = [ stdenv.lib.maintainers.MAINTAINER ];
  };
}
