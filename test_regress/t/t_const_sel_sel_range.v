// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A select from a narrower select, e.g. after inlining a truncating
// assignment, must not read bits of the wider expression beyond the
// narrower select
// verilator lint_off WIDTH
module t;
  logic [15:0] a;
  logic [1:0] idx;
  logic [3:0] n;
  logic [3:0] nref  /* verilator public_flat_rw */;
  logic [1:0] y;
  logic [1:0] yref;

  assign n = -a;
  assign nref = -a;
  assign y = n[idx+:2];
  assign yref = nref[idx+:2];

  int seed = 1;
  initial begin
    for (int i = 0; i < 32; i++) begin
      a = $random(seed);
      idx = i[1:0];
      #1;
      `checkh(y, yref);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
