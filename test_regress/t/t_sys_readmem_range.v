// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
  logic [7:0] c[0:5];

  function automatic string dump();
    string s = "";
    foreach (c[i]) s = {s, $sformatf("%h ", c[i])};
    return s;
  endfunction

  // IEEE 1800-2023 21.4: loading proceeds from the start to the finish address
  initial begin
    foreach (c[i]) c[i] = 0;
    $readmemh("t/t_sys_readmem_range_b.mem", c, 4, 1);
    `checks(dump(), "00 44 33 22 11 00 ");
    foreach (c[i]) c[i] = 0;
    $readmemh("t/t_sys_readmem_range_b.mem", c, 1, 3);  // Warns about the extra data
    `checks(dump(), "00 11 22 33 00 00 ");
    foreach (c[i]) c[i] = 0;
    $readmemh("t/t_sys_readmem_range_a.mem", c, 1, 4);
    `checks(dump(), "00 12 56 00 aa 00 ");
    foreach (c[i]) c[i] = 0;
    $readmemh("t/t_sys_readmem_range_a.mem", c, 4, 1);
    `checks(dump(), "00 00 56 cc aa 00 ");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
