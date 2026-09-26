// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Array query functions on associative arrays (IEEE 1800-2023 20.7)
module t;
  int aint[int];
  int abyte[byte];
  int auint[int unsigned];
  int along[longint];
  int awide[logic [69:0]];
  int aempty[int];

  initial begin
    aint[3] = 1;
    aint[-9] = 2;
    aint[20] = 3;
    `checkd($size(aint), 3);
    `checkd($size(aint, 1), 3);
    `checkd($left(aint), 0);
    `checkd($right(aint), 2147483647);
    `checkd($low(aint), -9);
    `checkd($high(aint), 20);
    `checkd($increment(aint), -1);

    abyte[-5] = 1;
    abyte[7] = 2;
    `checkd($size(abyte), 2);
    `checkd($right(abyte), 127);
    `checkd($low(abyte), -5);
    `checkd($high(abyte), 7);

    auint[1] = 1;
    auint[100] = 2;
    `checkd($size(auint), 2);
    `checkd($low(auint), 1);
    `checkd($high(auint), 100);

    along[-64'sd4] = 1;
    along[64'sd12] = 2;
    `checkd($low(along), -4);
    `checkd($high(along), 12);

    awide[70'd6] = 1;
    awide[70'd8] = 2;
    `checkd($size(awide), 2);
    `checkd($low(awide), 6);
    `checkd($high(awide), 8);

    `checkd($size(aempty), 0);

    aint.delete(20);
    `checkd($size(aint), 2);
    `checkd($high(aint), 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
