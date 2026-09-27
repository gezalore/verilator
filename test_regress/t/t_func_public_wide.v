// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Wide arguments of public tasks used in operations that are not expanded
module t;
  logic [71:0] v;

  task publicSet;
    // verilator public
    input [71:0] in_wide;
    v = in_wide * 72'h3;
  endtask

  task publicGet;
    // verilator public
    output [71:0] out_wide;
    out_wide = v + 72'h1;
    out_wide = out_wide * out_wide;
  endtask

  logic [71:0] r;

  initial begin
    publicSet(72'h12_34567890_abcdef01);
    `checkh(v, 72'h36_9d0369b2_0369cd03);
    publicGet(r);
    `checkh(r, 72'h37_3f720817_e9776810);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
