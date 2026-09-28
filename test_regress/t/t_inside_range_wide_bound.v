// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [63:0] big;
  logic [7:0] lo;
  logic [0:0] one;
  logic [39:0] addr;
  int r;

  // A range must not be truncated to the width of its low bound
  initial begin
    big = 64'h8000_0000_0000_0000;
    lo = 0;
    one = 1;
    addr = 40'h10_0000_0000;
    `checkd(one inside {[lo : big]}, 1'b1);
    `checkd(one inside {[1 : big]}, 1'b1);
    `checkd(addr inside {[32'h1 : 40'h10_0000_0000]}, 1'b1);
    `checkd(addr inside {[32'h1000 : addr]}, 1'b1);
    `checkd(addr inside {[$ : 40'hff_0000_0000]}, 1'b1);
    case (addr) inside
      [32'h1 : 40'h0f_ffff_ffff]: r = 1;
      [32'h1 : 40'h10_0000_0000]: r = 2;
      default: r = 3;
    endcase
    `checkd(r, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
