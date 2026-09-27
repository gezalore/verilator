// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// The operand of a replication is evaluated exactly once (IEEE 1800-2023 11.4.12.1)
module t;
  bit [63:0] a;
  bit [95:0] b;
  bit [31:0] c;
  bit [127:0] d;

  initial begin
    for (int i = 0; i < 4; ++i) begin
      a = {2{$urandom}};
      `checkh(a[63:32], a[31:0]);
      b = {3{$random}};
      `checkh(b[95:64], b[31:0]);
      `checkh(b[63:32], b[31:0]);
      c = {2{16'($urandom)}};
      `checkh(c[31:16], c[15:0]);
      d = {4{$urandom}};
      `checkh(d[127:96], d[31:0]);
      `checkh(d[95:64], d[63:32]);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
