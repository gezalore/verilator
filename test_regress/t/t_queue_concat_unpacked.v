// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unpacked array concatenation with fixed-size array items assigned to a queue
// or dynamic array (IEEE 1800-2023 10.10)
module t;
  int a[2];
  int b[1:0];
  int q[$];
  int d[];

  initial begin
    a = '{1, 2};
    b[1] = 3;
    b[0] = 4;
    q = {a, a};
    `checkd(q.size(), 4);
    `checkd(q[2], 1);
    `checkd(q[3], 2);
    q = {q, b};
    `checkd(q.size(), 6);
    `checkd(q[4], 3);
    `checkd(q[5], 4);
    d = {a, 5, b};
    `checkd(d.size(), 5);
    `checkd(d[2], 5);
    `checkd(d[3], 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
