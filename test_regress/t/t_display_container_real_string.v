// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Containers of reals and strings are formatted as containers
  real ra[2] = '{1.5, 2.0};
  string sa[2] = '{"p", "q"};
  real rq[$] = '{1.5, 2.0};
  string sq[$] = '{"a", "bc"};
  int ia[string];

  initial begin
    ia["x"] = 1;
    ia["y"] = 2;
    `checks($sformatf("%p", ra), "'{1.5, 2}");
    `checks($sformatf("%p", sa), "'{\"p\", \"q\"}");
    `checks($sformatf("%p %p", ra, sa), "'{1.5, 2} '{\"p\", \"q\"}");
    `checks($sformatf("%p %p", rq, sq), "'{1.5, 2} '{\"a\", \"bc\"}");
    `checks($sformatf("%p", ia.find_index with (item == 2)), "'{\"y\"}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
