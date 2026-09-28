// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Reference arguments referring to the same variable (IEEE 1800-2023 13.5.2)
class C;
  static int s;
  static function int f(ref int a, ref int b);
    int r = 0;
    a = 1;
    b = 2;
    if (a == 1) r += 1;
    if (a == 2) r += 10;
    return r;
  endfunction
  function int g(ref int a, ref int b);
    a = 5;
    b = a + 1;
    return a;
  endfunction
  static function int h(const ref int a);
    s = 3;
    return a;
  endfunction
  static function int m(ref int a, ref int b);
    int x = 0, y = 0;
    if (a == 1) x = 1;
    b = 2;
    if (a == 1) y = 1;
    return x * 10 + y;
  endfunction
  static function void w(ref bit [199:0] a, ref bit [199:0] b);
    a = {b[31:0], b[199:32]};
  endfunction
endclass

module t;
  int x, y, r;
  bit [199:0] v, e;
  C c;

  initial begin
    c = new;
    r = C::f(x, x);
    `checkd(r, 10);
    `checkd(x, 2);
    r = c.g(y, y);
    `checkd(r, 6);
    `checkd(y, 6);
    C::s = 7;
    r = C::h(C::s);
    `checkd(r, 3);
    x = 1;
    r = C::m(x, x);
    `checkd(r, 10);
    v = {8{25'h1abcdef}};
    e = {v[31:0], v[199:32]};
    C::w(v, v);
    `checkd(v == e, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
