// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  int q[$] = '{5, 6, 7, 8};
  int ua[4] = '{5, 6, 7, 8};
  int as[string];
  string sa[3] = '{"bb", "a", "ccc"};
  logic [99:0] wa[3] = '{100'h5, 100'h1, 100'h3};
  byte ba[4] = '{1, 2, 3, 4};

  initial begin
    as["x"] = 1;
    as["yy"] = 2;
    as["z"] = 3;
    // unique, min and max using item.index or keys wider than the elements
    `checks($sformatf("%p", q.unique with (item.index / 2)), "'{'h5, 'h7}");
    `checks($sformatf("%p", ua.unique with (item.index / 2)), "'{'h5, 'h7}");
    `checks($sformatf("%p", as.unique with (item.index.len())), "'{'h1, 'h2}");
    `checks($sformatf("%p", ba.unique with (32'(item) << 30)), "'{'h1, 'h2, 'h3, 'h4}");
    `checks($sformatf("%p", q.max() with (item.index % 3)), "'{'h7}");
    `checks($sformatf("%p", ua.max() with (item.index % 3)), "'{'h7}");
    `checks($sformatf("%p", q.min() with (item.index == 2)), "'{'h5}");
    `checks($sformatf("%p", ua.max() with (item.index == 2)), "'{'h7}");
    `checks($sformatf("%p %p", sa.min() with (item.len()), sa.max() with (item.len())),
            "'{\"a\"} '{\"ccc\"}");
    `checks($sformatf("%p %p", wa.min() with (item), wa.max() with (item)), "'{'h1} '{'h5}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
