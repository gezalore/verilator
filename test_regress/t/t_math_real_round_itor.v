// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  // Converting integers with more than 53 significant bits must round to nearest
  localparam real P_U64 = 64'hcdaaac43936aa40c;
  localparam real P_S64 = 64'sheb7fec926c931d1a;
  localparam real P_S96 = 96'sh7b6eb806cc5443333056ddb0;

  // Public so the conversions are not constant folded
  logic [63:0] u64 /* verilator public_flat_rw */;
  logic signed [63:0] s64 /* verilator public_flat_rw */;

  real r;

  initial begin
    `checkh($realtobits(P_U64), 64'h43e9b55588726d55);
    `checkh($realtobits(P_S64), 64'hc3b480136d936ce3);
    `checkh($realtobits(P_S96), 64'h45dedbae01b31511);
    r = $itor(64'hcdaaac43936aa40c);
    `checkh($realtobits(r), 64'h43e9b55588726d55);
    // Constant folded and run time conversions agree
    u64 = 64'hcdaaac43936aa40c;
    s64 = 64'sheb7fec926c931d1a;
    r = u64;
    `checkh($realtobits(r), 64'h43e9b55588726d55);
    r = s64;
    `checkh($realtobits(r), 64'hc3b480136d936ce3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
