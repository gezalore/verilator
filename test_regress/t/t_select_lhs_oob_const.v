// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [99:0] w = 100'h5;
  logic [11:0] d = 0;
  logic c = 0;
  logic signed [0:0] a;

  // Part select partially beyond the variable: only the in range bit is
  // written (IEEE 1800-2023 11.5.1)
  always_comb begin
    a = d[0];
    if (c) begin
      for (int j = 0; j < 1; j++) begin
        // verilator lint_off SELRANGE
        a[j*4+:4] = a[j*4+:4] ^ 4'(w[40:20] | 100'd3);
        // verilator lint_on SELRANGE
      end
    end
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    w <= {w[98:0], w[99] ^ w[50] ^ 1'b1};
    d <= d + 12'd7;
    c <= ~c;
    if (cyc > 0) begin
      `checks($sformatf("%x", a), $sformatf("%x", c ^ d[0]));
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
