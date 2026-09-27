// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the selects are not constant folded
  logic [95:0] v /* verilator public_flat_rw */;
  logic [95:0] g /* verilator public_flat_rw */;
  logic [100:0] w /* verilator public_flat_rw */;
  logic [100:0] g2 /* verilator public_flat_rw */;
  int i /* verilator public_flat_rw */;

  // IEEE 1800-2023 11.5.1: writing a partially out of range select only writes the bits in
  // range, and must not write anything else
  initial begin
    v = '0;
    g = '0;
    w = '0;
    g2 = '0;
    i = 80;
    v[i+:70] = '1;
    `checkh(v, {16'hffff, 80'h0});
    `checkh(g, 96'h0);
    i = 90;
    w[i+:40] = '1;
    `checkh(w, {11'h7ff, 90'h0});
    `checkh(g2, 101'h0);
    v = '0;
    i = 64;
    v[i+:64] = {32'hdeadbeef, 32'h12345678};
    `checkh(v, {32'h12345678, 64'h0});
    `checkh(g, 96'h0);
    i = 100;
    v[i+:8] = '1;
    `checkh(v, {32'h12345678, 64'h0});
    `checkh(g, 96'h0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
