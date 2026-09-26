// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unpacking a queue with a streaming concatenation consumes the leftmost bits
// (IEEE 1800-2023 11.4.14.3)
module t;
  byte bq[$];
  byte bd[];
  int iq[$];
  logic [99:0] wq[$];
  logic [31:0] a;
  logic [15:0] h;
  logic [63:0] q64;
  logic [79:0] w80;
  logic [31:0] b, c;
  logic [7:0] b8, c8;

  initial begin
    bq = '{8'h01, 8'h02, 8'h03, 8'h04};
    {>>{a}} = bq;
    `checkh(a, 32'h01020304);
    {<<8{a}} = bq;
    `checkh(a, 32'h04030201);
    {>>{h}} = bq;
    `checkh(h, 16'h0102);
    {>>{h}} = {8'h05, 8'h06};
    `checkh(h, 16'h0506);

    bd = '{8'h0a, 8'h0b, 8'h0c};
    {>>{h}} = bd;
    `checkh(h, 16'h0a0b);

    iq = '{32'h11223344, 32'h55667788};
    {>>{q64}} = iq;
    `checkh(q64, 64'h1122334455667788);
    {>>{a}} = iq;
    `checkh(a, 32'h11223344);

    bq = '{8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07, 8'h08, 8'h09, 8'h0a, 8'h0b, 8'h0c};
    {>>{w80}} = bq;
    `checkh(w80, 80'h0102030405060708090a);

    // Into several variables
    bq = '{8'h01, 8'h02, 8'h03, 8'h04};
    {>>{b8, c8}} = bq;
    `checkh(b8, 8'h01);
    `checkh(c8, 8'h02);
    {>>{b8, c8}} = {>>8{bq}};
    `checkh(b8, 8'h01);
    `checkh(c8, 8'h02);
    {>>{h, b8}} = bq;
    `checkh(h, 16'h0102);
    `checkh(b8, 8'h03);

    // From a stream of a queue
    {>>{b8, c8}} = {<<8{bq}};
    `checkh(b8, 8'h04);
    `checkh(c8, 8'h03);
    {>>{a}} = {<<8{bq}};
    `checkh(a, 32'h04030201);
    {>>{b8, c8}} = {<<8{bq[0:1]}};
    `checkh(b8, 8'h02);
    `checkh(c8, 8'h01);

    // Round trip through a queue of wide elements
    b = 32'hdeadbeef;
    c = 32'h12345678;
    wq = {>>{b, c}};
    `checkh(wq.size(), 1);
    `checkh(wq[0], {b, c, 36'h0});
    b = 0;
    c = 0;
    {>>{b, c}} = wq;
    `checkh(b, 32'hdeadbeef);
    `checkh(c, 32'h12345678);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
