// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Reduction methods on fixed size arrays using item.index
  int ua[4] = '{1, 2, 3, 4};
  int ub[3:0] = '{4, 3, 2, 1};

  initial begin
    `checkd(ua.sum() with (item.index), 6);
    `checkd(ua.sum() with (item.index * item), 20);
    `checkd(ub.sum() with (item.index * item), 20);
    `checkd(ua.product() with (item.index + 1), 24);
    `checkd(ua.and() with (item.index | 32'h10), 32'h10);
    `checkd(ua.or() with (1 << item.index), 32'hf);
    `checkd(ua.xor() with (item.index), 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
