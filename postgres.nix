{ config ? {}, overlays ? [], ... }@args:

let
  spec = builtins.fromJSON (builtins.readFile ./postgres.json);
  nixpkgs = fetchTarball {
    url = "https://github.com/${spec.owner}/${spec.repo}/archive/${spec.rev}.tar.gz";
    sha256 = spec.sha256;
  };
in
import nixpkgs (args // { inherit config overlays; })
