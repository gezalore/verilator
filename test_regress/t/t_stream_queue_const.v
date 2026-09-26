// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

// Streaming a constant into a queue
module t;
  byte bq[$];
  logic [31:0] v;

  initial begin
    v = 32'h01020304;

    bq = {<<8{v}};
    `checkp(bq, "'{'h4, 'h3, 'h2, 'h1}");
    bq = {>>8{v}};
    `checkp(bq, "'{'h1, 'h2, 'h3, 'h4}");
    bq = {<<8{32'h05060708}};
    `checkp(bq, "'{'h8, 'h7, 'h6, 'h5}");
    bq = {>>8{32'h05060708}};
    `checkp(bq, "'{'h5, 'h6, 'h7, 'h8}");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
