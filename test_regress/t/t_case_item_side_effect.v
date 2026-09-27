// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Case item expressions are evaluated in order, only until the first match
// (IEEE 1800-2023 12.5)
module t;
  string s;
  int x;

  function int note(int v);
    s = {s, $sformatf("%0d,", v)};
    return v;
  endfunction

  initial begin
    s = "";
    x = 2;
    case (x)
      note(1): s = {s, "one"};
      note(2): s = {s, "two"};
      note(3): s = {s, "three"};
    endcase
    `checks(s, "1,2,two");

    s = "";
    x = 5;
    case (x)
      note(1): s = {s, "one"};
      note(2): s = {s, "two"};
      default: s = {s, "default"};
    endcase
    `checks(s, "1,2,default");

    s = "";
    x = 7;
    casez (x)
      note(0): s = {s, "a"};
      note(1): s = {s, "b"};
      note(2): s = {s, "c"};
      note(3): s = {s, "d"};
      note(4): s = {s, "e"};
      note(5): s = {s, "f"};
      note(6): s = {s, "g"};
      note(7): s = {s, "h"};
      note(8): s = {s, "i"};
      note(9): s = {s, "j"};
    endcase
    `checks(s, "0,1,2,3,4,5,6,7,h");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
