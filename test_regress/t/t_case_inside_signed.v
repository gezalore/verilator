// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH
module t;
  logic signed [3:0] ss;
  logic [3:0] us;
  int r1, r2, r3;

  // Ranges of a case inside compare signed when all operands are signed
  always_comb begin
    case (ss) inside
      [-4'sd3 : 4'sd1]: r1 = 1;
      [4'sd2 : 4'sd6]: r1 = 2;
      default: r1 = 3;
    endcase
    case (ss) inside
      [$ : -4'sd5]: r2 = 1;
      [4'sd5 : $]: r2 = 2;
      default: r2 = 3;
    endcase
    // Unsigned, as the case expression is unsigned
    case (us) inside
      [4'sd2 : 4'sd6]: r3 = 1;
      default: r3 = 2;
    endcase
  end

  initial begin
    for (int i = -8; i < 8; i++) begin
      ss = 4'(i);
      us = 4'(i);
      #1;
      if (r1 !== ((i >= -3 && i <= 1) ? 1 : (i >= 2 && i <= 6) ? 2 : 3)) $stop;
      if (r2 !== ((i <= -5) ? 1 : (i >= 5) ? 2 : 3)) $stop;
      if (r3 !== ((us >= 2 && us <= 6) ? 1 : 2)) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
