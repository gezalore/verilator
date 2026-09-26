// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A stream narrower than its target is left aligned, filled with zeros on the right
// (IEEE 1800-2023 11.4.14)
module t;
  byte bq[$];
  logic [15:0] sq[$];
  int iq[$];
  logic [31:0] x;
  logic [63:0] y;
  logic [127:0] w;

  initial begin
    bq = '{8'h01, 8'h02};
    x = {>>{bq}};
    `checkh(x, 32'h01020000);
    y = {>>{bq}};
    `checkh(y, 64'h0102000000000000);
    w = {>>{bq}};
    `checkh(w, 128'h01020000000000000000000000000000);
    x = {<<8{bq}};
    `checkh(x, 32'h02010000);
    w = {<<8{bq}};
    `checkh(w, 128'h02010000000000000000000000000000);
    sq = '{16'h1234};
    y = {>>{sq}};
    `checkh(y, 64'h1234000000000000);
    iq = '{32'haabbccdd};
    y = {>>{iq}};
    `checkh(y, 64'haabbccdd00000000);
    // Same size unchanged
    bq = '{8'h01, 8'h02, 8'h03, 8'h04};
    x = {>>{bq}};
    `checkh(x, 32'h01020304);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
