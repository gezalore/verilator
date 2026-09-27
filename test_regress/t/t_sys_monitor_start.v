// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// $monitor displays at the end of the time step it is invoked in, even if
// none of its arguments change then (IEEE 1800-2023 21.2.3)
module t;
  int c;

  initial begin
    c = 3;
    #1;
    $monitor("[%0t] c=%0d", $time, c);
    #1 c = 4;
    #1 c = 4;
    #1 c = 6;
    #1;
    $monitor("[%0t] second c=%0d", $time, c);
    #1 $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
