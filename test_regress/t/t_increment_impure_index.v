// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Increment used as an expression, with an index with side effects
module t;
  int cnt;
  int arr[8];
  int x;

  function automatic int f();
    cnt++;
    return cnt;
  endfunction

  initial begin
    cnt = 0;
    arr = '{default: 10};
    x = arr[f()]++;
    `checkd(cnt, 1);
    `checkd(x, 10);
    `checkd(arr[1], 11);
    x = ++arr[f()];
    `checkd(cnt, 2);
    `checkd(x, 11);
    `checkd(arr[2], 11);
    x = arr[f()]--;
    `checkd(cnt, 3);
    `checkd(x, 10);
    `checkd(arr[3], 9);
    x = --arr[f()] + arr[f()]++;
    `checkd(cnt, 5);
    `checkd(x, 9 + 10);
    `checkd(arr[4], 9);
    `checkd(arr[5], 11);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
