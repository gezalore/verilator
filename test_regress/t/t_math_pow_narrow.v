// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// verilator lint_off WIDTHTRUNC
module t;
  // Public so the powers are not constant folded
  logic signed [31:0] b32 /* verilator public_flat_rw */;
  logic signed [63:0] b64 /* verilator public_flat_rw */;
  logic signed [95:0] b96 /* verilator public_flat_rw */;
  logic signed [30:0] e31 /* verilator public_flat_rw */;

  // Results narrower than the operands, only the bottom bits of the power are needed
  logic signed [16:0] r17;
  logic signed [32:0] r33;
  logic signed [39:0] r40;
  logic signed [64:0] r65;

  initial begin
    // -1 to a negative power: IEEE 1800-2023 Table 11-4
    b32 = -1;
    b64 = -1;
    b96 = -1;
    e31 = -31'sd2;
    r17 = b32 ** e31;
    r33 = b64 ** e31;
    r40 = b96 ** e31;
    r65 = b96 ** e31;
    `checkh(r17, 17'sh1);
    `checkh(r33, 33'sh1);
    `checkh(r40, 40'sh1);
    `checkh(r65, 65'sh1);
    e31 = -31'sd1;
    r17 = b32 ** e31;
    r33 = b64 ** e31;
    r40 = b96 ** e31;
    r65 = b96 ** e31;
    `checkh(r17, -17'sh1);
    `checkh(r33, -33'sh1);
    `checkh(r40, -40'sh1);
    `checkh(r65, -65'sh1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
