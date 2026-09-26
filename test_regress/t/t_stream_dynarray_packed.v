// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

// Streaming a packed value into a dynamic array
module t;
  byte bd[];
  int id[];
  logic [31:0] v;
  logic [63:0] v64;

  initial begin
    v = 32'h01020304;
    v64 = 64'h0102030405060708;

    bd = {<<8{v}};
    `checkp(bd, "'{'h4, 'h3, 'h2, 'h1}");
    bd = {>>8{v}};
    `checkp(bd, "'{'h1, 'h2, 'h3, 'h4}");
    bd = {>>{v}};
    `checkp(bd, "'{'h1, 'h2, 'h3, 'h4}");
    bd = {<<8{32'h0a0b0c0d}};
    `checkp(bd, "'{'hd, 'hc, 'hb, 'ha}");
    id = {>>{v64}};
    `checkp(id, "'{'h1020304, 'h5060708}");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
