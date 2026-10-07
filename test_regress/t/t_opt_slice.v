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

  logic [7:0] m[2][2];

  initial begin
    // Array pattern reading the assigned variable
    m[1][0] = 8'h10;
    m[1][1] = 8'h11;
    m[1] = '{m[1][1], m[1][0]};
    `checkh(m[1][0], 8'h11);
    `checkh(m[1][1], 8'h10);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
