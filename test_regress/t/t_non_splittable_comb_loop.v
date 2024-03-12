// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top(
  input wire [7:0] i,
  output logic [7:0] o
);

  logic [7:0] a;
  logic [7:0] b;

  // This should not yield an UNOPTFLAT
  assign b = a + 1;

  // Not splittable by -fsplit
  always_comb begin
     a = i + 1;
     o = b + a;
  end

endmodule
