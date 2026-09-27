// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Arithmetic right shift by a wide amount, narrowed to an array index
// verilator lint_off WIDTHTRUNC
module t;
  int e;
  bit signed [59:0] q;
  bit [95:0] c;
  int arr[8];
  int x;

  initial begin
    foreach (arr[i]) arr[i] = i * 3;
    e = $test$plusargs("never") ? 1 : 17;
    q = $test$plusargs("never") ? 1 : 60'sh123_4567_89ab_cdef;
    c = $test$plusargs("never") ? 1 : 3;
    x = arr[(e >>> (c & 127)) & 7];  // 17 >>> 3 = 2
    `checkd(x, 6);
    x = arr[(q >>> (c & 127)) & 7];  // 0xef >> 3 = 29
    `checkd(x, 15);
    e = -17;
    x = arr[(e >>> (c & 127)) & 7];  // -3
    `checkd(x, 15);
    c = 40;
    x = arr[(e >>> (c & 127)) & 7];  // -1
    `checkd(x, 21);
    x = arr[(q >>> (c & 127)) & 7];  // 0x12345 = ...101
    `checkd(x, 15);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
