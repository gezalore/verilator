// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  initial begin
    #300;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  localparam int N = 8;

  logic [N-1:0][7:0] ip = '0;
  logic [N-1:0][7:0] op;

  logic [7:0] iu [N-1:0] = '{default: 0};
  logic [7:0] ou [N-1:0];

  always @(posedge clk) begin
    for (int n = 0; n < N; ++n) begin
      ip[n] <= ip[n] + 8'(n);
      iu[n] <= iu[n] + 8'(n);
    end
  end

  for (genvar n = 0; n < N; ++n) begin
    assign op[n] = ~ip[n];
    assign ou[n] = ~iu[n];
  end

  always @(posedge clk) begin
    $write("%05t op == '{", $time);
    for (int n = 0; n < N; ++n) begin
      if (n > 0) $write(", ");
      $write("%2d: %4d", n, op[n]);
    end
    $write("}\n");

    $write("%05t ou == '{", $time);
    for (int n = 0; n < N; ++n) begin
      if (n > 0) $write(", ");
      $write("%2d: %4d", n, ou[n]);
    end
    $write("}\n");
  end

endmodule
