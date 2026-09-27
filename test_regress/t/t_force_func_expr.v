// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Function calls in the right hand side of 'force' and procedural 'assign'
// are continuously evaluated (IEEE 1800-2023 10.6)
module t;
  int b, a, q, r, p;

  function int f(int v);
    return v * 2;
  endfunction

  initial begin
    b = 1;
    force a = f(b) + 1;
    assign q = f(b) + f(b + 1);
    force r = f(b);
    assign p = f(b);
    #1;
    `checkd(a, 3);
    `checkd(q, 6);
    `checkd(r, 2);
    `checkd(p, 2);
    b = 5;
    #1;
    `checkd(a, 11);
    `checkd(q, 22);
    `checkd(r, 10);
    `checkd(p, 10);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
