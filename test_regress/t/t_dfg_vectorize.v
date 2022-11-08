// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module complete(
  input  wire [7:0] a,
  input  wire [7:0] b,
  input  wire [7:0] c,
  input  wire [7:0] d,
  output wire [7:0] o
);
  assign o[3] = a[3] | b[3] & ~c[3] ^ d[3];
  assign o[4] = a[4] | b[4] & ~c[4] ^ d[4];
  assign o[5] = a[5] | b[5] & ~c[5] ^ d[5];
  assign o[0] = a[0] | b[0] & ~c[0] ^ d[0];
  assign o[1] = a[1] | b[1] & ~c[1] ^ d[1];
  assign o[2] = a[2] | b[2] & ~c[2] ^ d[2];
  assign o[7] = a[7] | b[7] & ~c[7] ^ d[7];
  assign o[6] = a[6] | b[6] & ~c[6] ^ d[6];
endmodule;

module partial(
  input  wire [7:0] a,
  input  wire [7:0] b,
  input  wire [7:0] c,
  input  wire [7:0] d,
  output wire [7:0] o
);
  assign o[3] = 1'b0;
  assign o[4] = a[4] | b[4] & ~c[4] ^ d[4];
  assign o[5] = a[5] | b[5] & ~c[5] ^ d[5];
  assign o[0] = a[0] | b[0] & ~c[0] ^ d[0];
  assign o[1] = a[1] | b[1] & ~c[1] ^ d[1];
  assign o[2] = a[2] | b[2] & ~c[2] ^ d[2];
  assign o[7] = a[7] | b[7] & ~c[7] ^ d[7];
  assign o[6] = a[6] | b[6] & ~c[6] ^ d[6];
endmodule;

module pack_in(
  input  wire [7:0] a,
  input  wire [7:0] b,
  input  wire [7:0] c,
  input  wire [7:0] d,
  output wire [7:0] o
);
  assign o[3] = 1'b0;
  assign o[4] = a[4] | b[4] & ~c[4] ^ d[4];
  assign o[5] = a[5] | b[5] & ~c[5] ^ d[4];
  assign o[0] = a[0] | b[0] & ~c[0] ^ d[4];
  assign o[1] = a[1] | b[1] & ~c[1] ^ d[4];
  assign o[2] = a[2] | b[2] & ~c[2] ^ d[4];
  assign o[7] = a[7] | b[7] & ~c[7] ^ d[4];
  assign o[6] = a[6] | b[6] & ~c[6] ^ d[4];
endmodule;


module t(
  input  wire [7:0] a,
  input  wire [7:0] b,
  input  wire [7:0] c,
  input  wire [7:0] d,
  output wire [7:0] o_complete,
  output wire [7:0] o_partial,
  output wire [7:0] o_pack_in
);

  complete  u_complete  (.o(o_complete), .*);
  partial   u_partial   (.o(o_partial), .*);
  pack_in   u_pack_in   (.o(o_pack_in), .*);

endmodule
