// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Wide class member assigned a concatenation reading the same member,
// directly or via another handle to the same object
class C;
  bit [199:0] w;
  function void rot(C other);
    w = {other.w[31:0], other.w[199:32]};
  endfunction
endclass

module t;
  C h, g;
  bit [199:0] v;

  initial begin
    h = new;
    g = h;
    h.w = {8{25'h1abcdef}};
    v = h.w;
    h.w = {h.w[31:0], h.w[199:32]};
    v = {v[31:0], v[199:32]};
    `checkh(h.w, v);
    h.w = {g.w[100:0], g.w[199:101]};
    v = {v[100:0], v[199:101]};
    `checkh(h.w, v);
    h.rot(g);
    v = {v[31:0], v[199:32]};
    `checkh(h.w, v);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
