// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Type of an expression that is unsized, as it is made of literals
// (IEEE 1800-2023 5.7.1, 6.23)
module t;
  int x = 3;
  var type(5) a;
  var type(1 >> x) b;
  int arr[8];
  int q[$];

  initial begin
    a = 9;
    b = -2;
    `checkd($bits(a), 32);
    `checkd($bits(b), 32);
    `checkd(a, 9);
    `checkd(b, -2);
    // Impure index of an unsized type, evaluated into a temporary
    arr[(1 << q.size()) & 7] += 5;
    q.push_back(1);
    arr[(1 << q.size()) & 7] ^= 3;
    `checkd(arr[1], 5);
    `checkd(arr[2], 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
