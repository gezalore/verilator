// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc;
  logic       valid;
  logic [7:0] data;
endinterface

module sub #(
    parameter int ADD = 0
) (
    input wire clk,
    ifc i
);
  // Signals sharing a type descriptor
  logic [3:0][7:0] arr_a;
  logic [3:0][7:0] arr_b;
  typedef struct packed {
    logic [3:0] a;
    logic [7:0] b;
  } pkt_t;
  pkt_t pkt_a;
  pkt_t pkt_b;
  int   cnt;

  // Enum
  typedef enum logic [1:0] {
    RED   = 2'd0,
    GREEN = 2'd1,
    BLUE  = 2'd2
  } color_t;
  color_t color;

  // Hidden due to leading underscore
  logic _skipped;

  always @(posedge clk) begin
    cnt <= cnt + ADD + 32'(i.data);
    arr_a[0] <= arr_b[1];
    pkt_a.a <= pkt_b.b[3:0];
    _skipped <= ~_skipped;
    color <= color_t'(2'(color + 1));
  end

  if (1) begin : gblk
    logic inner;
    always @(posedge clk) inner <= i.valid;
  end

  if (1) begin : _hidden
    logic invisible;
    always @(posedge clk) invisible <= i.valid;
  end

  function automatic int counted();
    static int calls = 0;
    return ++calls;
  endfunction

  always @(posedge clk) arr_b[0] <= 8'(counted());
endmodule

module t (
    input wire clk,
    input wire [3:0] din,
    output wire [3:0] dout
);
  // Instances of one module referencing different interfaces
  ifc the_ifc ();
  ifc other_ifc ();

  // Array of instances
  sub #(1) arrayed[2] (
      .clk(clk),
      .i  (the_ifc)
  );
  // Scalar instance, and one hidden due to leading underscore
  sub #(2) named (
      .clk(clk),
      .i  (other_ifc)
  );
  sub #(3) _quiet (
      .clk(clk),
      .i  (the_ifc)
  );

  assign dout = din;
  assign the_ifc.valid = din[0];
  assign the_ifc.data = {4'b0, din};
  assign other_ifc.valid = din[1];
  assign other_ifc.data = {din, 4'b0};

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
