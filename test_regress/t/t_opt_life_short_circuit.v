// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Side effects of a function inlined into the right hand side of a
// short-circuiting operator are conditional
module t;
  string s;
  int x;

  function int note(int v);
    s = {s, $sformatf("%0d,", v)};
    return v;
  endfunction

  initial begin
    // Case items with multiple expressions are an '||' of the comparisons
    s = "r";
    x = 2;
    casez (x)
      note(2), note(3): s = {s, "a"};
      note(4): s = {s, "b"};
    endcase
    `checks(s, "r2,a");

    s = "";
    x = 3;
    case (x)
      note(1), note(3), note(5): s = {s, "a"};
      default: s = {s, "b"};
    endcase
    `checks(s, "1,3,a");

    s = "";
    x = 6;
    case (x)
      note(1), note(3): s = {s, "a"};
      default: s = {s, "b"};
    endcase
    `checks(s, "1,3,b");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
