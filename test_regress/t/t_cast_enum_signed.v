// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// verilator lint_off WIDTH
module t;
  typedef enum logic signed [2:0] {N = -2, M = 0, P = 3} s_t;
  typedef enum logic [2:0] {UA = 1, UB = 6} u_t;
  s_t s;
  u_t u;
  int v;
  logic signed [1:0] v2;
  logic [2:0] v3;

  initial begin
    // $cast to an enum checks the value as the equality operator compares
    v = -2;
    `checkd($cast(s, v), 1);
    `checkd(s, N);
    v = 6;
    `checkd($cast(s, v), 0);
    v = 3;
    `checkd($cast(s, v), 1);
    `checkd(s, P);
    v2 = -2'sd2;
    `checkd($cast(s, v2), 1);
    `checkd(s, N);
    v = 32'h80000006;
    `checkd($cast(u, v), 0);
    v = -2;
    `checkd($cast(u, v), 0);
    v = 6;
    `checkd($cast(u, v), 1);
    `checkd(u, UB);
    v3 = 3'd6;
    `checkd($cast(u, v3), 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
