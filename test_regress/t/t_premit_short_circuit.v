// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// The right hand side of '&&', '||' and '->', and the branches of '?:' with
// wide operations are only evaluated if needed (IEEE 1800-2023 11.4.7, 11.4.11),
// e.g. not with a null handle
class C;
  logic [99:0] w;
endclass

module t;
  C h;
  logic [99:0] x;
  int n;
  bit b;
  logic [64:0] y;
  logic [31:0] z;
  logic [126:0] r;
  logic [63:0] w;

  initial begin
    if ($test$plusargs("never")) h = new;
    x = 5;
    n = 0;
    if (h != null && (h.w + 100'd1) == x) n += 1;
    if (h == null || (h.w * x) == 100'd0) n += 2;
    if (h != null -> (h.w - x) != 100'd0) n += 4;
    if (h != null && (h.w[0] ? h.w : x) == x) n += 8;
    `checkd(n, 6);
    b = (h != null) ? ((h.w + 100'd1) == x) : x[0];
    `checkd(b, 1'b1);
    n = (h == null) ? 7 : int'(h.w * x);
    `checkd(n, 7);
    h = new;
    h.w = 4;
    n = 0;
    if (h != null && (h.w + 100'd1) == x) n += 1;
    if (h == null || (h.w * x) == 100'd20) n += 2;
    if (h != null -> (h.w - x) != 100'd0) n += 4;
    `checkd(n, 7);
    h.w = 5;
    n = 0;
    if ((h.w != 100'd0) && ((h.w << 90) >> 90) == 100'd5) n += 1;
    if (!(h.w == x) || ((h.w | x) + 100'd1) == 100'd6) n += 2;
    `checkd(n, 3);
    // A narrow '?:' converted to a temporary must hold a clean value
    y = 65'h1_0000_0000_0000_0001;
    z = 32'hd6141e8e;
    w = 64'd1;
    r = (y != 65'd0) ? 127'(((y != 65'd0) ? (~(|z)) : (y != 65'd0)) || w != 64'd0) : 127'(w);
    `checkd(r, 127'd1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
