{
  description = "ZK-DTT";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib;
    eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        tex' = pkgs.texlive.combined.scheme-full;
        tex = pkgs.texliveFull.withPackages (ps:
          with ps; [
            biblatex
            biber
            xetex
            tikz-inet
            pgf
            graphbox
            mathtools
            hyphenat
            url
            bbm
            beamer
            unicode-math
            fontspec
            xcharter
            fvextra
            stmaryrd
            ulem
            fancyhdr
            fitch
            minted
            dejavu
          ]);
        buildtex = (pkg-name:
          pkgs.stdenvNoCC.mkDerivation rec {
            name = pkg-name;
            src = self;
            buildInputs = [ pkgs.coreutils tex ];
            FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories = [ ]; };
            preBuild = ''
              export HOME=$(mktemp -d)
              export XDG_CACHE_HOME="$HOME/.cache"
            '';
            buildPhase = ''
              runHook preBuild
              install -D -t build/ ./papers/*.bib
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
              biber --input-directory=build -output-directory=build ${
                builtins.baseNameOf pkg-name
              }
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
            '';
            installPhase = ''
              mkdir -p $out
              cp build/${builtins.baseNameOf pkg-name}.pdf $out/
            '';
          });
        buildslide = (pkg-name:
          pkgs.stdenvNoCC.mkDerivation rec {
            name = pkg-name;
            src = self;
            buildInputs = [ pkgs.python313Packages.pygments pkgs.julia-mono pkgs.coreutils tex' ];
            buildPhase = ''
              mkdir build
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
            '';
            installPhase = ''
              mkdir -p $out
              cp build/${builtins.baseNameOf pkg-name}.pdf $out/
            '';
          });
        papers = [
          {
            name = "paper";
            path = "papers/paper";
          }
          {
            name = "adapting_equations";
            path = "papers/adapting_equations";
          }
          {
            name = "lit_review";
            path = "papers/lit_review";
          }
          #{ name = "infer_rule"; path = "papers/infer_rule"; }
        ];
        slides = [{
          name = "dcc";
          path = "slides/dcc";
        }];
      in rec {
        devShells.default =
          pkgs.mkShell { buildInputs = [ pkgs.coreutils tex ]; };
        packages = builtins.listToAttrs (builtins.map (paper: {
          name = paper.name;
          value = buildtex paper.path;
        }) papers) // {
          tex = tex;
        } // builtins.listToAttrs (builtins.map (slide: {
          name = slide.name;
          value = buildslide slide.path;
        }) slides);
        defaultPackage = pkgs.linkFarm "all-documents" ((builtins.map (paper: {
          name = paper.name;
          path = packages.${paper.name};
        }) papers) ++ (builtins.map (slide: {
          name = slide.name;
          path = packages.${slide.name};
        }) slides));
      });
}
