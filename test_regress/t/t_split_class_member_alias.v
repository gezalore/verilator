// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Statements accessing a class member via different handles to the same
// object must not be split into separate processes
class C;
  int x;
endclass

module t;
  C h0, h2;
  logic clk = 0;
  int cyc = 0;
  int y, z, w;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    y = h2.x;
    h0.x = cyc * 3;
    w <= h0.x;
    z <= h2.x + y;
  end

  always @(posedge clk) begin
    if (cyc >= 2) begin
      `checkd(w, 3 * (cyc - 1));
      `checkd(z, 3 * (cyc - 1) + 3 * (cyc - 2));
    end
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    h0 = new;
    h2 = $test$plusargs("never") ? null : h0;
    forever #1 clk = ~clk;
  end
endmodule
