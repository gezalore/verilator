// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  int q[$] = '{5, 2, 9};
  int e[$];

  function automatic int add(int a, int b);
    return a + b;
  endfunction

  function automatic int count2(int a[$], int b[$]);
    return a.size() * 10 + b.size();
  endfunction

  initial begin
    // Array method calls that are not the first in an argument list
    `checks($sformatf("%p %p", q.min(), q.max()), "'{'h2} '{'h9}");
    `checks($sformatf("%0d %0d %0d", q.sum(), q.product(), q.xor()), "16 90 14");
    `checks($sformatf("%p %p %p", q, q.find_index with (item > 3), q.unique()),
            "'{'h5, 'h2, 'h9} '{'h0, 'h2} '{'h5, 'h2, 'h9}");
    `checkd(add(1, q.sum()), 17);
    `checkd(add(q.sum(), q.sum() with (item * 2)), 48);
    `checkd(count2(q, q.find with (item > 3)), 32);
    e = {q.min(), q.max()};
    `checks($sformatf("%p", e), "'{'h2, 'h9}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
