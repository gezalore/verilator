// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  byte bq[$];
  byte bd[];
  int a;
  logic [63:0] x;
  initial begin
    x = {>>{a, bq}};
    x = {<<8{bq, bd}};
    {>>{a, bd}} = x;
  end
endmodule
