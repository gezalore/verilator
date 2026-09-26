// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

// Blocking assignment to an unpacked array reading the same array
module t;
  int arr[4];
  int sr[4];
  int six[6];
  int din;

  initial begin
    arr = '{0, 1, 2, 3};
    arr = '{arr[3], arr[2], arr[1], arr[0]};
    `checkp(arr, "'{'h3, 'h2, 'h1, 'h0}");
    arr = '{arr[1], arr[2], arr[3], arr[0]};
    `checkp(arr, "'{'h2, 'h1, 'h0, 'h3}");

    din = 100;
    sr = '{10, 11, 12, 13};
    sr = '{din, sr[0], sr[1], sr[2]};
    `checkp(sr, "'{'h64, 'ha, 'hb, 'hc}");

    six = '{0, 1, 2, 3, 4, 5};
    six[1:4] = six[0:3];
    `checkp(six, "'{'h0, 'h0, 'h1, 'h2, 'h3, 'h5}");
    six = '{0, 1, 2, 3, 4, 5};
    six[0:3] = six[2:5];
    `checkp(six, "'{'h2, 'h3, 'h4, 'h5, 'h4, 'h5}");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
