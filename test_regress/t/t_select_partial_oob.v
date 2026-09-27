// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the selects are not constant folded
  logic [100:0] w /* verilator public_flat_rw */;
  logic [95:0] v /* verilator public_flat_rw */;
  int i /* verilator public_flat_rw */;

  // IEEE 1800-2023 11.5.1: the bits of a partially out of range select that are in range
  // are read as usual
  initial begin
    w = {5'h15, 32'h89abcdef, 32'h01234567, 32'hfedcba98};
    v = {32'h89abcdef, 32'h01234567, 32'hfedcba98};
    i = 90;
    `checkh(w[i+:20], 20'(w[100:90]));
    `checkh(w[i+:40], 40'(w[100:90]));
    `checkh(w[i+:70], 70'(w[100:90]));
    i = 80;
    `checkh(v[i+:20], 20'(v[95:80]));
    `checkh(v[i+:40], 40'(v[95:80]));
    `checkh(v[i+:70], 70'(v[95:80]));
    i = 64;
    `checkh(v[i+:40], 40'(v[95:64]));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
