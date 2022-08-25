{
  description = "Formalisation of the Vehicle Language in Agda";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.05;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agda = pkgs.agda.withPackages (ps: [ ps.standard-library ]);
      in rec {
        packages = {
          html-doc = pkgs.stdenvNoCC.mkDerivation rec {
            name = "vehicle-formalisation";
            src = self;
            buildInputs = [ agda ];
            phases = ["unpackPhase" "buildPhase" "installPhase"];
            buildPhase = ''
mkdir -p html;
agda --html --html-dir=html src/Everything.agda
'';
            installPhase = ''
mkdir -p $out;
cp html/* $out/;
'';
          };
        };
        defaultPackage = packages.html-doc;
      });
}
