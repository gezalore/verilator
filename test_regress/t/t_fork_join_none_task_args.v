// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Each process started by a fork has its own copy of the arguments and
// automatic variables of the tasks it calls (IEEE 1800-2023 9.3.2, 13.3.1)
module t;
  string names[3] = '{"a", "b", "c"};
  int seen1[string];
  string seen2[int];
  int seen3[int];

  task automatic show(string s);
    #1 seen1[s]++;
  endtask

  task automatic outer(string s, int k);
    string u;
    u = {s, s};
    show(u);
    #1 seen2[k] = u;
  endtask

  task automatic delayed(int k);
    repeat (k + 1) #1;
    seen3[k] = int'($time);
  endtask

  task automatic spawn(string s);
    // Inlined task with a fork inside
    for (int i = 0; i < 3; ++i) begin
      fork
        outer({s, names[i]}, i + 10);
      join_none
    end
  endtask

  initial begin
    spawn("x");
    foreach (names[i]) begin
      fork
        show(names[i]);
        outer(names[i], i);
      join_none
    end
    for (int i = 0; i < 3; ++i) begin
      automatic int k = i;
      fork
        delayed(k);
      join_none
    end
    #10;
    `checkd(seen1.num(), 9);
    foreach (names[i]) begin
      `checkd(seen1[names[i]], 1);
      `checkd(seen1[{names[i], names[i]}], 1);
      `checks(seen2[i], {names[i], names[i]});
      `checkd(seen3[i], i + 1);
      `checkd(seen1[{"x", names[i], "x", names[i]}], 1);
      `checks(seen2[i + 10], {"x", names[i], "x", names[i]});
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
