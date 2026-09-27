// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the divisions are not constant folded
  int sa32 /* verilator public_flat_rw */;
  int sb32 /* verilator public_flat_rw */;
  longint sa64 /* verilator public_flat_rw */;
  longint sb64 /* verilator public_flat_rw */;

  initial begin
    sa32 = 32'h80000000;
    sb32 = -1;
    sa64 = 64'h80000000_00000000;
    sb64 = -1;
    // The result wraps around to the most negative value
    `checkh(sa32 / sb32, 32'sh80000000);
    `checkh(sa32 % sb32, 32'sh0);
    `checkh(sa64 / sb64, 64'sh80000000_00000000);
    `checkh(sa64 % sb64, 64'sh0);
    `checkh(32'sh80000000 / -32'sd1, 32'sh80000000);
    `checkh(64'sh80000000_00000000 / -64'sd1, 64'sh80000000_00000000);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
