// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic c = 1'b1;
  int x = 0;
  int y = 0;
  int z = 0;
  int v = 0;
  int seen = 0;
  int w = 0;

  class C;
    static function void flip();
      c = ~c;
    endfunction
    static function void look();
      seen = v;
    endfunction
  endclass

  // Statements must stay in order with calls to functions accessing the same variables
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (c) x = x + 1;
    C::flip();
    if (c) y = y + 1;
    else z = z + 1;
    v = cyc * 7;
    w = w + 1;
    C::look();
  end

  always @(negedge clk) begin
    `checkd(x, (cyc + 1) / 2);
    `checkd(y, cyc / 2);
    `checkd(z, (cyc + 1) / 2);
    `checkd(seen, (cyc - 1) * 7);
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
