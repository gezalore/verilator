// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // item.index is an int for arrays and queues (IEEE 1800-2023 7.12.4)
  int q[$] = '{5, 6, 7, 8};
  int ua[4] = '{5, 6, 7, 8};
  int da[] = '{5, 6, 7};

  initial begin
    `checks($sformatf("%p", q.find with (item.index > -1)), "'{'h5, 'h6, 'h7, 'h8}");
    `checks($sformatf("%p", q.find_index with (item.index - 2 < 0)), "'{'h0, 'h1}");
    `checks($sformatf("%p", q.min() with (-item.index)), "'{'h8}");
    `checks($sformatf("%p", ua.min() with (-item.index)), "'{'h8}");
    `checks($sformatf("%p", ua.find with (item.index > -1)), "'{'h5, 'h6, 'h7, 'h8}");
    `checks($sformatf("%p", da.find_first with (item.index - 1 >= 0)), "'{'h6}");
    `checks($sformatf("%0d", q.sum() with ((item.index - 2) < 0 ? 1 : 0)), "2");
    q.sort() with (-item);
    `checks($sformatf("%p", q), "'{'h8, 'h7, 'h6, 'h5}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
