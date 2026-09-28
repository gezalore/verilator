// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [6:0] n;
  logic [40:0] q;
  logic [95:0] w;
  logic [31:0] r;
  logic [63:0] r64;

  // The inverted 1-bit result of a comparison or reduction is extended to
  // the context width first, then shifted logically
  int zero;
  initial begin
    zero = $c32("0");
    n = 7'(zero);
    q = 41'(zero);
    w = 96'(zero);
    r = (~(7'h0 < n)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~(41'h0 < q)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~(96'h0 < w)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~(|n)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~(w != 96'h0)) >> 1;
    `checkh(r, 32'h7fffffff);
    r64 = (~(n != 7'h0)) >> 1;
    `checkh(r64, 64'h7fffffff_ffffffff);
    r = (-(n == 7'h0)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~((7'h0 < n) >> 1)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~(&n)) >> 1;
    `checkh(r, 32'h7fffffff);
    r = (~((n == 7'h1) && (q == 41'h0))) >> 1;
    `checkh(r, 32'h7fffffff);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
