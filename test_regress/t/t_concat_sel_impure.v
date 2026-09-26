// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Part of a concatenation not used by the result still has its side effects
// verilator lint_off WIDTHTRUNC
module t;
  int cnt;
  int x;
  logic [7:0] b;

  function automatic int f();
    cnt++;
    return cnt;
  endfunction

  initial begin
    cnt = 0;
    x = {f(), f()};
    `checkd(cnt, 2);
    cnt = 0;
    x = {f(), 32'h0};
    `checkd(cnt, 1);
    `checkd(x, 0);
    cnt = 0;
    b = 8'({f(), f()} >> 40);
    `checkd(cnt, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
