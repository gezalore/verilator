// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Struct types declared in $unit, of variables that are split, so only their member types
// remain used. The member values of the pattern are assigned to the components, and must
// not keep referencing the struct, which would outlive $unit.

typedef logic [7:0] ua_t[4:3];

typedef struct {
  ua_t m0;
  logic [6:0] m1;
} us_t;

module t;

  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  us_t a;
  us_t b;

  always_comb begin
    a = '{m0: '{crc[12:5], crc[21:14]}, m1: 7'(crc[17:11] + 7'd5)};
    b = a;
  end

  initial begin
    #1;
    if (b.m1 !== 7'(crc[17:11] + 7'd5)) $stop;
    if (b.m0[4] !== crc[12:5]) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
