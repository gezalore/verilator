// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Stream assigned to a wide target is left justified (IEEE 1800-2023 11.4.14)
// verilator lint_off WIDTHEXPAND
module t;
  bit [6:0] v;
  bit [6:0] r;
  bit [129:0] o;
  bit [79:0] p;

  initial begin
    v = $test$plusargs("never") ? 7'h1 : 7'h35;
    foreach (v[i]) r[6 - i] = v[i];
    o = {<<1{v}};
    `checkh(o, {r, 123'h0});
    o = {>>{v}};
    `checkh(o, {v, 123'h0});
    p = {<<1{v}};
    `checkh(p, {r, 73'h0});
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
