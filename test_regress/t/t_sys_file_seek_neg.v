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

// $fseek with negative offset
module t;
  int fd;
  int off;

  initial begin
    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_sys_file_seek_neg.dat"}, "w");
    $fwrite(fd, "abcdef");
    $fclose(fd);

    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_sys_file_seek_neg.dat"}, "r");
    `checkd($fseek(fd, -2, 2), 0);
    `checkd($ftell(fd), 4);
    `checkd($fgetc(fd), "e");
    `checkd($fseek(fd, -3, 1), 0);
    `checkd($ftell(fd), 2);
    `checkd($fgetc(fd), "c");
    off = -1;
    `checkd($fseek(fd, off, 1), 0);
    `checkd($fgetc(fd), "c");
    `checkd($fseek(fd, -1, 0), -1);
    $fclose(fd);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
