# `ultranet`, the ad-blocking VPN server, and `ultranet-admin`, its
# administration tool.
{
  perSystem =
    { buildCrate, ... }:
    {
      packages = {
        ultranet = buildCrate "ultranet";
        ultranet-admin = buildCrate "ultranet-admin";
      };
    };
}
