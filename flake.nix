{
  description = "kitty";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.05";
    reflection-lib.url = "path:/home/m0rphism/Development/projects/agda/reflection-lib/";
  };

  outputs = { self, nixpkgs, reflection-lib, ... }: 
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
      config = {
        allowUnfree = true;
        allowBroken = true;
        zathura.useMupdf = true;
      };
    };
    lib = nixpkgs.lib;
  in {
    packages.x86_64-linux.default = self.packages.x86_64-linux.kitty;

    packages.x86_64-linux.kitty = pkgs.agdaPackages.mkDerivation {
      version = "0.1.0";
      pname = "kitty";
      src = ./.;
      buildInputs = with pkgs.agdaPackages; [ standard-library reflection-lib.packages.x86_64-linux.reflection-lib ];

      libraryName = "kitty";  # has to match the .agda-lib
      everythingFile = "src/Kitty/Everything.agda";  # defaults to "Everything.agda"
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
        # maintainers = [ stdenv.lib.maintainers.m0rphism ];
      };
    };
  };
}
