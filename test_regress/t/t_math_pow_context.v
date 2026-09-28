// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off WIDTH
module t;
  logic [6:0] a;
  logic b;
  logic [2:0] e;
  logic [63:0] r;
  // The base of '**' is context determined (IEEE 1800-2023 11.6.1)
  localparam logic [6:0] PA = 7'h7f;
  localparam logic [63:0] P = (PA + 7'd1) ** 3'd2;

  initial begin
    a = 7'h7f;
    b = 1'b1;
    e = 3'd2;
    r = a ** e;
    `checkh(r, 64'h3f01);
    r = (a ^ ~b) ** e;
    `checkh(r, 64'h3f01);
    r = (~b) ** e;
    `checkh(r, 64'h4);
    r = (a + 7'd1) ** e;
    `checkh(r, 64'h4000);
    `checkh(P, 64'h4000);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
