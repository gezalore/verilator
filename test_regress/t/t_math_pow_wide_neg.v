// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the powers are not constant folded
  logic signed [64:0] b65 /* verilator public_flat_rw */;
  logic signed [95:0] b96 /* verilator public_flat_rw */;
  logic signed [62:0] e63 /* verilator public_flat_rw */;
  logic signed [95:0] e96 /* verilator public_flat_rw */;

  initial begin
    // Negative exponent: IEEE 1800-2023 Table 11-4
    e63 = -63'sd1;
    e96 = -96'sd2;
    b65 = 65'sh0_ffffffff_ffffffff;  // 2**64-1, not -1
    `checkh(b65 ** e63, 65'sh0);
    `checkh(b65 ** e96, 65'sh0);
    b65 = 65'sh1_00000000_00000001;  // 2**64+1, not 1
    `checkh(b65 ** e63, 65'sh0);
    b65 = -65'sd1;
    `checkh(b65 ** e63, -65'sd1);
    `checkh(b65 ** e96, 65'sh1);
    b65 = 65'sh1;
    `checkh(b65 ** e63, 65'sh1);
    b96 = 96'shffffffff_0000ffff_ffffffff;  // Not -1
    `checkh(b96 ** e63, 96'sh0);
    b96 = 96'shffff0000_00000000_00000001;  // Not 1
    `checkh(b96 ** e63, 96'sh0);
    b96 = -96'sd1;
    `checkh(b96 ** e63, -96'sd1);
    `checkh(b96 ** e96, 96'sh1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
