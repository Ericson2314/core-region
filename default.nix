{ stdenv, agda, AgdaStdlib }:

agda.mkDerivation (self: rec {
  version = "0.0.0.0";
  name = "core-region";

  src = ./.;

  buildDepends = [ AgdaStdlib ];
  everythingFile = "CoreRegion.agda";
  #sourceDirectories = [];
  #topSourceDirectories = [ "src" ];
})
