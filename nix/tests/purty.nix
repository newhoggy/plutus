{ runCommand, fixPurty, src, lib, diffutils, glibcLocales }:
let
  # just purescript sources
  src' = lib.cleanSourceWith {
    inherit src;
    filter = with lib;
      name: type:
        let baseName = baseNameOf (toString name); in
        (
          (type == "regular" && hasSuffix ".purs" baseName) ||
          (type == "directory" && (baseName != "generated"
          && baseName != "output"
          && baseName != "node_modules"
          && baseName != ".psc-package"
          && baseName != ".spago"))
        );
  };
in
runCommand "purty-check"
{
  buildInputs = [ fixPurty diffutils glibcLocales ];
  meta.platforms = with lib.platforms; [ linux darwin ];
} ''
  set +e
  cp -a ${src'} orig
  cp -a ${src'} purty
  chmod -R +w purty
  cd purty
  fix-purty
  cd ..
  diff --brief --recursive orig purty > /dev/null
  EXIT_CODE=$?
  if [[ $EXIT_CODE != 0 ]]
  then
    mkdir -p $out/nix-support
    diff -ur orig purty > $out/purty.diff
    echo "file none $out/purty.diff" > $out/nix-support/hydra-build-products
    echo "*** purty-haskell found changes that need addressed first"
    echo "*** Please run \`nix-shell --run fix-purty\` and commit changes"
    echo "*** or apply the diff generated by hydra if you don't have nix."
    exit $EXIT_CODE
  else
    echo $EXIT_CODE > $out
  fi
''
