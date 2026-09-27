// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Assignment to an unpacked array slice
module t;
  int arr[6];
  int brr[6];
  int m[2][4];

  initial begin
    foreach (arr[i]) arr[i] = i + 1;
    arr[1:4] = arr[0:3];
    `checkd(arr[0], 1);
    `checkd(arr[1], 1);
    `checkd(arr[2], 2);
    `checkd(arr[4], 4);
    `checkd(arr[5], 6);
    foreach (brr[i]) brr[i] = 10 + i;
    brr[0:2] = arr[3:5];
    `checkd(brr[0], 3);
    `checkd(brr[2], 6);
    `checkd(brr[3], 13);
    foreach (m[i, j]) m[i][j] = i * 10 + j;
    m[1][0:2] = m[0][1:3];
    `checkd(m[1][0], 1);
    `checkd(m[1][2], 3);
    `checkd(m[1][3], 13);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
