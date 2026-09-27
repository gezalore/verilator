// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  int aa[int];
  int as[string];
  int k;
  string s;

  initial begin
    aa[300] = 1;
    aa[5] = 2;
    aa[-7] = 3;
    as["b"] = 1;
    as["d"] = 2;
    // next/prev from an index that is not in the array (IEEE 1800-2023 7.9.6, 7.9.7)
    k = 6;
    `checkd(aa.next(k), 1);
    `checkd(k, 300);
    k = 6;
    `checkd(aa.prev(k), 1);
    `checkd(k, 5);
    k = 1000;
    `checkd(aa.prev(k), 1);
    `checkd(k, 300);
    k = -100;
    `checkd(aa.next(k), 1);
    `checkd(k, -7);
    k = -100;
    `checkd(aa.prev(k), 0);
    `checkd(k, -100);
    k = 1000;
    `checkd(aa.next(k), 0);
    `checkd(k, 1000);
    s = "c";
    `checkd(as.next(s), 1);
    `checkd(s, "d");
    s = "c";
    `checkd(as.prev(s), 1);
    `checkd(s, "b");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
