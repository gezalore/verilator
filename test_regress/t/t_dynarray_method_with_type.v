// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  typedef struct {
    byte k;
    string n;
  } s_t;
  s_t sd[];
  byte bd[] = '{100, 100, 100};

  initial begin
    sd = new[2];
    sd[0] = '{5, "e"};
    sd[1] = '{-3, "c"};
    // The result of a reduction with a 'with' clause has the type of the 'with' expression
    `checkd($bits(bd.sum() with (int'(item))), 32);
    `checkd($bits(bd.sum()), 8);
    `checks($sformatf("%0d", sd.sum() with (int'(item.k))), "2");
    `checks($sformatf("%0d", bd.sum() with (int'(item))), "300");
    `checks($sformatf("%0d", sd.product() with (int'(item.k))), "-15");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
