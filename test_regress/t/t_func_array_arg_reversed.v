// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unpacked array argument with the opposite range direction to the formal is
// assigned left to right (IEEE 1800-2023 7.6, 13.5.1), also when not inlined
// verilator lint_off ASCRANGE
class C;
  static function int f(int p[0:3]);
    return p[0] * 1000 + p[3];
  endfunction
  static function void io(inout int p[0:3]);
    p[0] = p[0] + 100;
  endfunction
  static function int f2(int p[2][0:2]);
    return p[1][0] * 10 + p[1][2];
  endfunction
endclass

module t;
  int b[3:0];
  int m[2][2:0];

  initial begin
    b[3] = 1;
    b[2] = 2;
    b[1] = 3;
    b[0] = 4;
    `checkd(C::f(b), 1004);
    C::io(b);
    `checkd(b[3], 101);
    `checkd(b[0], 4);
    m[1][2] = 5;
    m[1][1] = 6;
    m[1][0] = 7;
    `checkd(C::f2(m), 57);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
