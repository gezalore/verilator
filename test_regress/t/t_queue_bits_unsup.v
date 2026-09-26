// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int q[$];
  int x;
  initial begin
    x = $bits(q);
    $display("%0d", $bits(q));
  end
endmodule
