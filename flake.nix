{
  description = "ZK-DTT";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        tex = pkgs.texliveFull.withPackages (ps: with ps;
          [ biblatex biber xetex tikz-inet pgf graphbox mathtools hyphenat url bbm fontspec xcharter fvextra stmaryrd ulem fancyhdr fitch ]);
        buildtex = (pkg-name: pkgs.stdenvNoCC.mkDerivation rec {
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
              biber --input-directory=build -output-directory=build ${builtins.baseNameOf pkg-name}
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
              xelatex -interaction=nonstopmode -output-directory=build ${pkg-name}
            '';
            installPhase = ''
              mkdir -p $out
              cp build/${builtins.baseNameOf pkg-name}.pdf $out/
            '';
        });
        papers = [
          { name = "paper"; path = "papers/paper"; }
          { name = "adapting_equations"; path = "papers/adapting_equations"; }
          { name = "lit_review"; path = "papers/lit_review"; }
          #{ name = "infer_rule"; path = "papers/infer_rule"; }
          { name = "infer_rule_slides"; path = "papers/infer_rule_slides"; } ];
      in rec {
        devShells.default = pkgs.mkShell {
          buildInputs = [ pkgs.coreutils tex ];
        };
        packages = builtins.listToAttrs (builtins.map
          (paper: { name = paper.name; value = buildtex paper.path; })
          papers) // { tex = tex; };
        defaultPackage = pkgs.linkFarm "all-papers" (builtins.map
          (paper: { name = paper.name; path = packages.${paper.name}; })
          papers);
      });
}
