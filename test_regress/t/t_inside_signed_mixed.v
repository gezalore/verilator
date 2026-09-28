// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic signed [7:0] se;
  logic signed [63:0] e;
  logic [32:0] one;
  logic [63:0] u1;
  logic signed [126:0] sneg;
  localparam logic signed [7:0] PSE = -1;

  // Each comparison is signed only if both of its operands are signed
  // (IEEE 1800-2023 11.4.13, 11.8.1)
  initial begin
    se = -1;
    e = 0;
    one = 1;
    u1 = 1;
    sneg = {1'b1, 126'd0};
    `checkd(se inside {16'hffff}, 1'b0);
    `checkd(se == 16'hffff, 1'b0);
    `checkd(se inside {16'h00ff}, 1'b1);
    `checkd(se inside {16'shffff}, 1'b1);
    `checkd(se inside {16'h1, 16'shffff}, 1'b1);
    `checkd(se inside {[16'h0 : 16'h00fe]}, 1'b0);
    `checkd(se inside {[8'd0 : 8'd255]}, 1'b1);
    `checkd(se inside {[0 : 255]}, 1'b0);
    `checkd(se inside {[-2 : 2]}, 1'b1);
    `checkd(se inside {[-2 : 16'h00ff]}, 1'b1);
    `checkd(PSE inside {16'hffff}, 1'b0);
    `checkd(PSE inside {[-2 : 16'h00ff]}, 1'b1);
    `checkd(e inside {[0 : (64'sh0 - one)]}, 1'b1);
    `checkd(e inside {[130'sh0 : (64'sh0 - 33'h1)]}, 1'b1);
    `checkd(128'sh1 inside {127'sh0, 16'h0, [u1 : sneg]}, 1'b0);
    `checkd((128'sh1 >= u1) && (128'sh1 <= sneg), 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
