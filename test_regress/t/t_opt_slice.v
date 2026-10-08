// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  typedef struct {
    logic [7:0] a;
    logic [7:0] b[2];
  } s_t;

  logic [7:0] m[2][2];
  s_t s;

  initial begin
    // Array pattern reading the assigned variable
    m[1][0] = 8'h10;
    m[1][1] = 8'h11;
    m[1] = '{m[1][1], m[1][0]};
    `checkh(m[1][0], 8'h11);
    `checkh(m[1][1], 8'h10);

    // Struct pattern reading the assigned variable
    s.a = 8'h20;
    s.b[0] = 8'h21;
    s.b[1] = 8'h22;
    s = '{a: s.b[1], b: '{s.a, s.b[0]}};
    `checkh(s.a, 8'h22);
    `checkh(s.b[0], 8'h20);
    `checkh(s.b[1], 8'h21);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
