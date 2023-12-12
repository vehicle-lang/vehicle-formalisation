{
  description = "Formalisation of the Vehicle Language in Agda";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agda = pkgs.agda.withPackages
          (ps: [ (ps.standard-library.overrideAttrs (oldAttrs: {
            version = "2.0";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "v2.0";
              hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
            };
          })) ]);
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
