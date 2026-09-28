// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input logic [15:0] i,
    output logic [15:0] o
);
  assign o = i;
endmodule

module t #(
    parameter logic [15:0] P = {<<4{8'hab}}
);

  localparam logic [7:0] A = 8'hab;
  localparam logic [15:0] K = {<<4{A}};
  localparam logic [99:0] W = {<<8{A, 16'h1234}};
  logic [7:0] a = 8'hab;
  logic [15:0] r;
  logic [15:0] o;
  logic [15:0] ta;

  function automatic logic [15:0] id(logic [15:0] x);
    return x;
  endfunction
  task automatic tk(input logic [15:0] x, output logic [15:0] y);
    y = x;
  endtask

  sub s (
      .i({<<4{a}}),
      .o(o)
  );

  // A stream assigned, passed or connected to a wider target is left justified (IEEE 1800-2023 11.4.14)
  initial begin
    r = {<<4{a}};
    `checkh(r, 16'hba00);
    `checkh(K, 16'hba00);
    `checkh(P, 16'hba00);
    `checkh(W, {24'h3412ab, 76'h0});
    `checkh(id({<<4{a}}), 16'hba00);
    tk({<<4{a}}, ta);
    `checkh(ta, 16'hba00);
    #1;
    `checkh(o, 16'hba00);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
