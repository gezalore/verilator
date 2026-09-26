// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

// Left streaming of a 64-bit value into a queue with a slice wider than a byte
module t;
  logic [15:0] sq[$];
  byte bq[$];
  logic [99:0] wq[$];
  logic [63:0] v64;

  initial begin
    v64 = 64'h0102030405060708;
    sq = {<<16{v64}};
    `checkp(sq, "'{'h708, 'h506, 'h304, 'h102}");
    bq = {<<16{v64}};
    `checkp(bq, "'{'h7, 'h8, 'h5, 'h6, 'h3, 'h4, 'h1, 'h2}");
    wq = {<<16{v64}};
    `checkp(wq, "'{'h708050603040102000000000}");
    sq = {<<32{v64}};
    `checkp(sq, "'{'h506, 'h708, 'h102, 'h304}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
