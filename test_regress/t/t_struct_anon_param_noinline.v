// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Anonymous struct in a parameterized module that is not inlined, with an instance
// optimized away
module sub #(
    parameter int ID = 1
) (
    input logic clk,
    input logic [7:0] i,
    output logic [7:0] o
);
  struct {
    logic [7:0] d;
    struct {logic [1:0] x;} cfg;
  } port[2];
  always_ff @(posedge clk) begin
    port[0].d <= i;
    port[0].cfg.x <= i[1:0];
  end
  assign o = port[0].d ^ 8'(port[0].cfg.x) ^ 8'(ID);
endmodule

module t;
  logic clk = 0;
  logic [7:0] i, o1, o2;
  sub #(.ID(3)) u1 (.clk(clk), .i(i), .o(o1));
  sub #(.ID(4)) u2 (.clk(clk), .i(i), .o(o2));
  initial begin
    i = 8'h5a;
    #1 clk = 1;
    #1;
    if (o1 !== (8'h5a ^ 8'h2 ^ 8'h3)) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
