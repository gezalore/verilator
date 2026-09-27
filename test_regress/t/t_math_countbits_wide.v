// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the counts are not constant folded
  logic [95:0] v96 /* verilator public_flat_rw */;
  logic [127:0] v128 /* verilator public_flat_rw */;
  logic [99:0] v100 /* verilator public_flat_rw */;

  initial begin
    // Widths that are a multiple of 32 bits
    v96 = 96'hb18b16aa_5f6abbf4_a21ac87e;
    `checkd($countbits(v96, 1'b1), 51);
    `checkd($countbits(v96, 1'b0), 45);
    `checkd($countbits(v96, 1'b0, 1'b1), 96);
    v128 = '0;
    `checkd($countbits(v128, 1'b0), 128);
    `checkd($countbits(v128, 1'b1), 0);
    `checkd($countbits(v128, 1'b1, 1'b0), 128);
    v100 = '0;
    `checkd($countbits(v100, 1'b0), 100);
    `checkd($countbits(v100, 1'b0, 1'b1), 100);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
