// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Public so the conversions are not constant folded
  logic [199:0] u /* verilator public_flat_rw */;
  logic signed [127:0] s /* verilator public_flat_rw */;

  real r;

  initial begin
    // Converting integers with more than 53 significant bits must round to nearest, which
    // depends on bits below the top three words
    u = 200'h11415132ea692880000000003;
    r = u;
    `checkh($realtobits(r), 64'h45f1415132ea6929);
    u = 200'h3bfa2ca080c6a52dece95af5b67e6e8820e3bd;
    r = u;
    `checkh($realtobits(r), 64'h494dfd1650406353);
    u = 200'h3bfe0f5caded41000000001;
    r = u;
    `checkh($realtobits(r), 64'h458dff07ae56f6a1);
    u = 200'h9f26daa3e67744000000000000000000000000000000000001;
    r = u;
    `checkh($realtobits(r), 64'h4c63e4db547ccee9);
    u = 200'hb00e08789d3c2400000000000000001d;
    r = u;
    `checkh($realtobits(r), 64'h47e601c10f13a785);
    s = -128'sh95fa6b678c65440000000000000006;
    r = s;
    `checkh($realtobits(r), 64'hc762bf4d6cf18ca9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
