// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A procedural continuous assignment follows changes of its right hand side
// (IEEE 1800-2023 10.6.1), even if it was assigned a constant just before
module t;
  int b, r, s;

  initial begin
    b = 1;
    assign r = b;
    assign s = b + 1;
    #1;
    `checkd(r, 1);
    `checkd(s, 2);
    b = 7;
    #1;
    `checkd(r, 7);
    `checkd(s, 8);
    deassign r;
    deassign s;
    b = 3;
    #1;
    `checkd(r, 7);
    `checkd(s, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
