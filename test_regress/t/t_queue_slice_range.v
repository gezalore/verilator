// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  int q[$] = '{1, 2, 3};
  int r[$];
  int a = 5, b = 7, n = 3, m = -1;

  initial begin
    // IEEE 1800-2023 7.10.1: out of range queue slices
    r = q[a:b];
    `checks($sformatf("%p", r), "'{}");
    r = q[n:n];
    `checks($sformatf("%p", r), "'{}");
    r = q[m:m];
    `checks($sformatf("%p", r), "'{}");
    r = q[0:m];
    `checks($sformatf("%p", r), "'{}");
    r = q[a:$];
    `checks($sformatf("%p", r), "'{}");
    r = q[m:1];
    `checks($sformatf("%p", r), "'{'h1, 'h2}");
    r = q[1:b];
    `checks($sformatf("%p", r), "'{'h2, 'h3}");
    // Writing a slice beyond the end has no effect
    r = '{9, 9};
    q[a:b] = r;
    `checks($sformatf("%p", q), "'{'h1, 'h2, 'h3}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
