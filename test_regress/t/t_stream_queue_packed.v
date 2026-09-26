// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

// Streaming a packed value into a queue: the queue is sized to hold the stream, and a
// partial last element is zero filled on the right (IEEE 1800-2023 11.4.14)
module t;
  byte bq[$];
  int iq[$];
  logic [3:0] nq[$];
  byte bd[];
  logic [3:0] v4;
  logic [7:0] v8;
  logic [15:0] v16;
  logic [23:0] v24;
  logic [39:0] v40;
  logic [71:0] v72;

  initial begin
    v4 = 4'h5;
    v8 = 8'hab;
    v16 = 16'h1234;
    v24 = 24'habcdef;
    v40 = 40'h0102030405;
    v72 = 72'h010203040506070809;

    bq = {<<8{v16}};
    `checkp(bq, "'{'h34, 'h12}");
    bq = {>>{v16}};
    `checkp(bq, "'{'h12, 'h34}");
    bq = {>>8{v16}};
    `checkp(bq, "'{'h12, 'h34}");
    bq = {<<8{v24}};
    `checkp(bq, "'{'hef, 'hcd, 'hab}");
    bq = {>>8{v24}};
    `checkp(bq, "'{'hab, 'hcd, 'hef}");
    bq = {>>8{v4}};
    `checkp(bq, "'{'h50}");
    bq = {<<8{v40}};
    `checkp(bq, "'{'h5, 'h4, 'h3, 'h2, 'h1}");
    bq = {>>{v72}};
    `checkp(bq, "'{'h1, 'h2, 'h3, 'h4, 'h5, 'h6, 'h7, 'h8, 'h9}");
    bq = {<<8{v72}};
    `checkp(bq, "'{'h9, 'h8, 'h7, 'h6, 'h5, 'h4, 'h3, 'h2, 'h1}");
    bd = {<<8{v24}};
    `checkp(bd, "'{'hef, 'hcd, 'hab}");

    iq = {>>32{v8}};
    `checkp(iq, "'{'hab000000}");
    iq = {>>{v16}};
    `checkp(iq, "'{'h12340000}");
    iq = {<<8{v16}};
    `checkp(iq, "'{'h34120000}");
    iq = {>>{v40}};
    `checkp(iq, "'{'h1020304, 'h5000000}");

    nq = {>>4{v16}};
    `checkp(nq, "'{'h1, 'h2, 'h3, 'h4}");
    nq = {<<4{v16}};
    `checkp(nq, "'{'h4, 'h3, 'h2, 'h1}");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
