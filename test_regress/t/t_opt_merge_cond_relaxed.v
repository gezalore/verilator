// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); `stop; end while(0)

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  initial begin
    #300;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  int dpiSet = 0;
  function automatic void setDpi(int value);
    dpiSet = value;
  endfunction
  export "DPI-C" function setDpi;
  import "DPI-C" context function void setViaDpi(int value); // calls setDpi(value)

  int tmp;
  int cnt = 0;

  int pub /* verilator public_flat_rd */ = 0;

  always @(posedge clk) begin
    // Side effect but no state change. Should be merged
    if (cyc[1]) $display("cyc[1] is 1 once");
    ++cnt;
    if (cyc[1]) $display("cyc[1] is 1 twice");

    // Side effect but no state change. Should be merged
    if (cyc > 100000) $error("cyc > 100000 once");
    ++cnt;
    if (cyc > 100000) $error("cyc > 100000 once");

    // DPI call but no state change. Should be merged
    dpiSet = 13;
    if (cyc[1:0] == 2'd2) setViaDpi(cyc + 16);
    ++cnt;
    if (cyc[1:0] == 2'd2) setViaDpi(cyc + 32);
    `check(dpiSet, cyc % 4 == 2 ? cyc + 32 : 13);

    // DPI call, possible direct state chagne. Should not be merged
    tmp = dpiSet;
    if (dpiSet[1:0] == 2'd2) setViaDpi(dpiSet & ~32'b11);
    if (dpiSet[1:0] == 2'd2) setViaDpi(dpiSet + 10); // Won't execute
    `check(dpiSet, cyc % 4 == 2 ? (tmp & ~32'b11) : 13);

    // DPI call but may observe public state. Should not be merged
    dpiSet = 14;
    if (cyc[1:0] == 2'd3) setViaDpi(cyc + 32);
    ++pub;
    if (cyc[1:0] == 2'd3) setViaDpi(cyc + 64);
    `check(dpiSet, cyc % 4 == 3 ? cyc + 64 : 14);

    // DPI call, possible indirect state change. Should not be merged
    dpiSet = 11;
    tmp = cyc + $c(0); // Prevent repalcing with 'cyc'
    if (tmp % 3 == 0) begin
        setViaDpi(3);
        tmp = dpiSet + 2;
    end
    if (tmp % 3 == 0) setViaDpi(4); // Won't execute
    `check(dpiSet, cyc % 3 == 0 ? 3 : 11);
    dpiSet = 3;

    // DPI call, possible indirect state change. Should not be merged
    tmp = cyc + $c(0); // Prevent repalcing with 'cyc'
    if (tmp % 2 == 0) begin
        setViaDpi(6);
        if (cyc[2]) tmp = dpiSet + 1;
    end
    if (tmp % 2 == 0) setViaDpi(4); // Sometime executes
    `check(tmp, cyc % 2 == 0 ? (cyc[2] ? 7 : cyc) : cyc);
    `check(dpiSet, cyc % 2 == 0 ? (cyc[2] ? 6 : 4) : 3);

    $display("cnt=%3d pub=%3d", cnt, pub);
  end

endmodule
