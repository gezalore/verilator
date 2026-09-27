// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // item.index of an associative array is its key, also in min/max/unique
  int aa[int];
  int as[string];

  initial begin
    aa[10] = 1;
    aa[-5] = 2;
    aa[7] = 3;
    as["x"] = 1;
    as["yy"] = 2;
    as["z"] = 3;
    `checks($sformatf("%p", aa.max() with (-item.index)), "'{'h2}");
    `checks($sformatf("%p", aa.min() with (item.index)), "'{'h2}");
    `checks($sformatf("%p", as.min() with (item.index)), "'{'h1}");
    `checks($sformatf("%p", as.max() with (item.index)), "'{'h3}");
    `checks($sformatf("%p", as.unique_index with (item.index.len())), "'{\"x\", \"yy\"}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
