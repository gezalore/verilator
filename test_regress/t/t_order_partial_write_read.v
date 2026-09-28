// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] a = 0;
  logic b = 0;
  logic c = 0;

  // A block writing some bits of 'v', then reading bits written by another block,
  // which in turn depends on this block
  // verilator lint_off UNOPTFLAT
  logic [3:0] v;
  logic [1:0] u;
  // verilator lint_on UNOPTFLAT
  logic [3:0] y;
  always_comb begin
    u = a;
    v[0] = c;
    y = v;
  end
  always_comb v[3:1] = {u, b};

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= a + 2'd1;
    b <= cyc[1];
    c <= cyc[0];
  end

  always @(negedge clk) begin
    `checkh(y, {a, b, c});
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
