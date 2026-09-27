// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Fixed size arrays with a non-zero low index
  int ud[5:2] = '{4, 3, 2, 1};  // ud[5] = 4 ... ud[2] = 1
  int uu[1:4] = '{1, 2, 3, 4};  // uu[1] = 1 ... uu[4] = 4
  int un[-2:1] = '{7, 8, 9, 10};  // un[-2] = 7 ... un[1] = 10
  int idx[$];

  initial begin
    `checkd(ud.sum() with (item.index), 14);
    `checkd(ud.sum() with (item.index * item), 40);
    `checks($sformatf("%p", ud.find with (item.index == 3)), "'{'h2}");
    `checks($sformatf("%p", ud.find_index with (item > 2)), "'{'h4, 'h5}");
    `checks($sformatf("%p", ud.find_first_index with (item < 3)), "'{'h2}");
    `checks($sformatf("%p", ud.find_last_index with (item < 3)), "'{'h3}");
    `checks($sformatf("%p", ud.map() with (item.index)), "'{'h2, 'h3, 'h4, 'h5}");
    `checks($sformatf("%p", uu.unique_index), "'{'h1, 'h2, 'h3, 'h4}");
    `checks($sformatf("%p", uu.find_index with (item.index == 4)), "'{'h4}");
    idx = un.find_index with (item >= 9);
    `checkd(idx.size(), 2);
    `checkd(int'(idx[0]), 0);
    `checkd(int'(idx[1]), 1);
    idx = un.find_index with (item == 7);
    `checkd(int'(idx[0]), -2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
