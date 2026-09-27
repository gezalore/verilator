// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  typedef enum logic [3:0] {A = 1, B = 5, C = 6, D = 12} e_t;
  e_t e;

  initial begin
    e = A;
    // Method calls on the result of next/prev with a step
    `checks(e.next(2).name(), "C");
    `checks(e.next(7).name(), "D");
    `checks(e.prev(3).name(), "B");
    `checks(e.next(0).name(), "A");
    `checks(e.next(2).next(2).name(), "A");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
