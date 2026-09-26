// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define STRINGIFY(x) `"x`"
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// File functions whose result is overwritten before use still have side effects
module t;
  int fd;
  int c;
  int n;

  initial begin
    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_sys_file_unused_result.dat"}, "w");
    $fwrite(fd, "abcdef");
    $fclose(fd);

    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_sys_file_unused_result.dat"}, "r");
    c = $fgetc(fd);  // Skip 'a'
    c = $fgetc(fd);
    `checkd(c, "b");
    n = $fseek(fd, 4, 0);
    n = 0;
    c = $fgetc(fd);
    `checkd(c, "e");
    n = $rewind(fd);
    n = $fgetc(fd);
    `checkd(n, "a");
    $fclose(fd);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
