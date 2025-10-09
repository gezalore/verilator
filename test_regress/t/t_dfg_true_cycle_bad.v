// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`default_nettype none

module t(
    output wire [9:0] o,
    //
    input wire ia,
    input wire ib,
    input wire sa,
    input wire sb,
    output wire oa,
    output wire ob
);
    assign o[1:0] = o[9:8];
    assign o[3:2] = o[1:0];
    assign o[7:4] = 4'(o[3:2]);
    assign o[9:8] = o[5:4];

    assign oa = sa ? ia : ob;
    assign ob = sb ? ib : oa;
endmodule
