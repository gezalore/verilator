// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Wide assignment to an array element, where the index reads the array
module t;
  bit [79:0] arr[8];
  bit [99:0] mem[4][2];
  int i;

  initial begin
    i = 0;
    arr[arr[i][2:0]] = 80'h1234_5678_9abc_def0_0003;
    `checkh(arr[0], 80'h1234_5678_9abc_def0_0003);
    `checkh(arr[3], 80'h0);
    arr[arr[0][2:0]] += 80'h1111_0000_0000_0000_0001;
    `checkh(arr[3], 80'h1111_0000_0000_0000_0001);
    `checkh(arr[1], 80'h0);
    mem[mem[0][0][1:0]][1] = 100'h9_8765_4321_0fed_cba9_8765_4322;
    `checkh(mem[0][1], 100'h9_8765_4321_0fed_cba9_8765_4322);
    `checkh(mem[2][1], 100'h0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
