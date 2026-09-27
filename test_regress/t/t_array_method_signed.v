// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Methods ordering signed values
  byte ba[5] = '{100, 100, -3, 7, 127};
  int q[$] = '{5, -2, 9, -2, 0, 9};
  shortint da[];
  byte aa[int];
  byte wa[*];
  logic signed [69:0] wq[$];
  logic signed [0:0] bq[$];

  initial begin
    `checks($sformatf("%0d %0d", ba.min()[0], ba.max()[0]), "-3 127");
    `checks($sformatf("%0d %0d", q.min()[0], q.max()[0]), "-2 9");
    `checks($sformatf("%p %p", q.min() with (-item), q.max() with (item % 3)), "'{'h9} '{'h5}");
    da = '{-1, 32767, 2};
    `checks($sformatf("%0d %0d", da.min()[0], da.max()[0]), "-1 32767");
    aa[1] = 5;
    aa[2] = -5;
    aa[3] = 0;
    `checks($sformatf("%0d %0d", aa.min()[0], aa.max()[0]), "-5 5");
    wa[1] = 5;
    wa[2] = -5;
    `checks($sformatf("%0d %0d", wa.min()[0], wa.max()[0]), "-5 5");
    q.sort();
    `checks($sformatf("%p", q), "'{'hfffffffe, 'hfffffffe, 'h0, 'h5, 'h9, 'h9}");
    q.rsort();
    `checks($sformatf("%p", q), "'{'h9, 'h9, 'h5, 'h0, 'hfffffffe, 'hfffffffe}");
    q.sort() with (item % 4);
    `checks($sformatf("%0d %0d %0d", q[0], q[1], q[2]), "-2 -2 0");
    wq = '{70'sd3, -70'sd1, 70'sh20000000000000000, -70'sh20000000000000000};
    wq.sort();
    `checks($sformatf("%0d %0d %0d %0d", wq[0], wq[1], wq[2], wq[3]),
            "-36893488147419103232 -1 3 36893488147419103232");
    bq = '{1'sb0, 1'sb1, 1'sb0};
    bq.sort();
    `checks($sformatf("%0d %0d %0d", bq[0], bq[1], bq[2]), "-1 0 0");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
