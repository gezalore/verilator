// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Hierarchical reference to a parameter in a generate loop iteration
module sub #(parameter int P = 1) ();
  localparam int Q = P * 3;
endmodule

module t;
  for (genvar g = 0; g < 3; g++) begin : gblk
    localparam int K = g + 10;
    sub #(.P(g + 1)) u ();
  end

  initial begin
    `checkd(gblk[0].K, 10);
    `checkd(gblk[1].K, 11);
    `checkd(gblk[2].K, 12);
    `checkd(gblk[1].u.P, 2);
    `checkd(gblk[2].u.Q, 9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
