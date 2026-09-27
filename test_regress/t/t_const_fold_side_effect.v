// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// verilator lint_off CMPCONST
// verilator lint_off UNSIGNED
// verilator lint_off WIDTH
module t;
  int cnt = 0;
  logic [31:0] r;

  function automatic logic [7:0] f();
    cnt++;
    return 8'h5;
  endfunction

  // Operations with a constant result still evaluate their operands
  initial begin
    r = f() ** 0;
    `checkd(r, 1);
    r = 32'(f() < 0);
    `checkd(r, 0);
    r = 32'(f() >= 0);
    `checkd(r, 1);
    r = 32'(0 > f());
    `checkd(r, 0);
    r = 32'(0 <= f());
    `checkd(r, 1);
    r = 32'(f() > 8'hff);
    `checkd(r, 0);
    r = 32'(f() <= 8'hff);
    `checkd(r, 1);
    r = 32'(8'hff < f());
    `checkd(r, 0);
    r = 32'(8'hff >= f());
    `checkd(r, 1);
    r = 32'(&(16'(f())));
    `checkd(r, 0);
    r = 32'(32'h100 == f());
    `checkd(r, 0);
    r = 32'(32'h100 != f());
    `checkd(r, 1);
    r = 32'(32'h100 > f());
    `checkd(r, 1);
    r = 32'($onehot0(f()[0]));
    `checkd(r, 1);
    `checkd(cnt, 14);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
