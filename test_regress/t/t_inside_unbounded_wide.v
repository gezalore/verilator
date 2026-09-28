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
  logic [39:0] a;
  logic signed [39:0] s;
  int r;

  // '$' bounds of ranges with an expression wider than 32 bits
  initial begin
    a = 40'hff_ffff_ffff;
    s = -40'sd5;
    `checkd(a inside {[40'h1 : $]}, 1'b1);
    `checkd(a inside {[$ : 40'h1]}, 1'b0);
    `checkd(s inside {[$ : -40'sd4]}, 1'b1);
    `checkd(s inside {[-40'sd4 : $]}, 1'b0);
    case (a) inside
      [40'h1 : $]: r = 1;
      default: r = 2;
    endcase
    `checkd(r, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
