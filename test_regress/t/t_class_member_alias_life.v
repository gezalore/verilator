// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Class member accessed in a method directly and via another handle that
// refers to the same object
class C;
  int x;
  function int f(C other);
    int r = 0;
    x = 1;
    other.x = 2;
    if (x == 1) r += 1;
    if (x == 2) r += 10;
    return r;
  endfunction
  function int g(C other);
    int r;
    x = 4;
    r = other.x;
    x = 5;
    return r;
  endfunction
endclass

module t;
  C c;

  initial begin
    c = new;
    `checkd(c.f(c), 10);
    `checkd(c.g(c), 4);
    `checkd(c.x, 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
