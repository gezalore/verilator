// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input i1a2[1:0],
  output logic o1a2[1:0]
);

  always o1a2 = i1a2;

endmodule
