# To develop iteratively within this repository, open a Nix shell via:
#
#     $ nix-shell
#
# ... and then use `cabal` to build and test:
#
#     [nix-shell]$ cabal configure --enable-tests
#     [nix-shell]$ cabal test

{ compiler ? "ghc844", enableDhall ? false }:

let
  fetchNixpkgs = import ./nix/fetchNixpkgs.nix;

  nixpkgs = fetchNixpkgs {
    rev          = "bedbba61380a4da0318de41fcb790c176e1f26d1";
    sha256       = "0z4fgh15nz86kxib9ildmh49v6jim6vgbjyla7jbmgdcl0vd9qsg";
    outputSha256 = "0dxxw2ipa9403nk8lggjsypbr1a9jpb3q4hkjsg89gr5wz26p217";
  };

  config = { };

  overlays = [
    (pkgsNew: pkgsOld: {
      haskell = pkgsOld.haskell // {
        packages = pkgsOld.haskell.packages // {
          "${compiler}" = pkgsOld.haskell.packages."${compiler}".override {
            overrides =
              haskellPackagesNew: haskellPackagesOld:
                rec {
                  dhall =
                    haskellPackagesNew.callPackage ./nix/dhall.nix { };

                  formatting =
                    haskellPackagesNew.callPackage ./nix/formatting.nix { };

                  megaparsec =
                    haskellPackagesNew.callPackage ./nix/megaparsec.nix { };

                  neat-interpolation =
                    haskellPackagesNew.callPackage ./nix/neat-interpolation.nix { };

                  prettyprinter =
                    pkgsNew.haskell.lib.dontCheck
                      (haskellPackagesNew.callPackage ./nix/prettyprinter.nix { });

                  repline =
                    haskellPackagesNew.callPackage ./nix/repline.nix { };

                  proto3-suite-base =
                    let

                      # Adds a nix file as an input to the haskell derivation it
                      # produces. This is useful for callHackage / callCabal2nix to
                      # prevent the generated default.nix from being garbage collected
                      # (requiring it to be frequently rebuilt), which can be an
                      # annoyance.
                      #
                      # Cribbed from nixpkgs master because it was not
                      # backported to 18.09
                      callPackageKeepDeriver = src: args:
                        pkgsNew.haskell.lib.overrideCabal (haskellPackagesNew.callPackage src args) (orig: {
                          preConfigure = ''
                            # Generated from ${src}
                            ${orig.preConfigure or ""}
                          '';
                        });

                      # Cribbed from nixpkgs master because it was not
                      # backported to 18.09
                      callCabal2nixWithOptions = name: src: extraCabal2nixOptions: args:
                        let
                          filter = path: type:
                                     pkgsNew.lib.hasSuffix "${name}.cabal" path ||
                                     baseNameOf path == "package.yaml";
                          expr = haskellPackagesNew.haskellSrc2nix {
                            inherit name extraCabal2nixOptions;
                            src = if pkgsNew.lib.canCleanSource src
                                  then pkgsNew.lib.cleanSourceWith { inherit src filter; }
                                  else src;
                          };
                        in pkgsNew.haskell.lib.overrideCabal (callPackageKeepDeriver expr args) (orig: {
                             inherit src;
                           });

                      cabal2nixFlags = if enableDhall then "-fdhall" else "";
                    in
                      callCabal2nixWithOptions "proto3-suite" ./. cabal2nixFlags { };

                  proto3-suite-boot =
                    pkgsNew.haskell.lib.overrideCabal
                      proto3-suite-base
                      (oldArgs: {
                         configureFlags = (oldArgs.configureFlags or [])
                           ++ [ "--disable-optimization" ]
                           ++ (if enableDhall then [ "-fdhall" ] else []);
                         doCheck        = false;
                         doHaddock      = false;
                        }
                      );

                  proto3-wire =
                    haskellPackagesNew.callPackage ./nix/proto3-wire.nix { };

                  proto3-suite =
                    pkgsNew.haskell.lib.overrideCabal
                      proto3-suite-base
                      (oldArgs:
                        let
                          python = pkgsNew.python.withPackages (pkgs: [ pkgs.protobuf]);

                          ghc =
                            haskellPackagesNew.ghcWithPackages
                              (pkgs: oldArgs.testHaskellDepends ++ [ proto3-suite-boot ]);

                          test-files = ./test-files;

                          cg-artifacts = pkgsNew.runCommand "proto3-suite-test-cg-artifacts" {} ''
                            mkdir -p $out/protos

                            cp -r ${test-files}/. $out/protos/.

                            cd $out

                            build () {
                              echo "[proto3-suite-test-cg-artifacts] Compiling proto-file/$1"
                              ${proto3-suite-boot}/bin/compile-proto-file \
                                --out $out \
                                --includeDir "$2" \
                                --proto "$1"
                            }

                            for proto in $(find ${test-files} -name 'test_*.proto'); do
                              build ''${proto#${test-files}/} ${test-files}
                            done

                            echo "[proto3-suite-test-cg-artifacts] Protobuf CG complete"
                          '';

                          copyGeneratedCode = ''
                            echo "Copying CG  artifacts from ${cg-artifacts} into ./gen/"
                            mkdir -p gen
                            ${pkgsNew.rsync}/bin/rsync \
                              --recursive \
                              --checksum \
                              ${cg-artifacts}/ gen
                            chmod -R u+w gen
                          '';

                        in rec {
                           configureFlags = (oldArgs.configureFlags or [])
                             ++ (if enableDhall then [ "-fdhall" ] else []);

                           postPatch = (oldArgs.postPatch or "") + copyGeneratedCode;

                           testHaskellDepends = (oldArgs.testHaskellDepends or []) ++ [
                             pkgsNew.ghc
                             pkgsNew.protobuf3_1
                             proto3-suite-boot
                             python
                           ];

                           shellHook = (oldArgs.shellHook or "") + ''
                             ${copyGeneratedCode}

                             export PATH=${haskellPackagesNew.cabal-install}/bin:${ghc}/bin:${python}/bin''${PATH:+:}$PATH
                           '';
                         }
                      );
                };
          };
        };
      };
    })
  ];

   linuxPkgs = import nixpkgs { inherit config overlays; system = "x86_64-linux" ; };
  darwinPkgs = import nixpkgs { inherit config overlays; system = "x86_64-darwin"; };
        pkgs = import nixpkgs { inherit config overlays; };

in
  { proto3-suite-linux  =  linuxPkgs.haskell.packages."${compiler}".proto3-suite;
    proto3-suite-darwin = darwinPkgs.haskell.packages."${compiler}".proto3-suite;

    inherit (pkgs.haskell.packages."${compiler}") proto3-suite-boot proto3-suite;
  }
