// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 0;
  logic [7:0] i;
  logic [15:0] a, b;

  // Splitting this block must not separate the coverage increment from its inputs
  always_comb begin
    a = {8'd0, i} + 16'd1;
    b = {i, i};
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    i <= 8'(cyc * 3);
    if (cyc > 0 && a != {8'd0, i} + 16'd1) $stop;
    if (cyc > 0 && b != {i, i}) $stop;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
