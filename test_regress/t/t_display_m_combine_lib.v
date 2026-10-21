// DESCRIPTION: Verilator: %m in a module with several instances, whose code is combined
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module t (
    input clk
);
  integer cyc = 0;
  lib u_lib (.clk);
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

`ifndef USE_LIB
module lib (
    input clk
);
  sub u0 (.clk);
  sub u1 (.clk);
  sub u2 (.clk);
endmodule

module sub (
    input clk
);
  /* verilator no_inline_module */
  logic [3:0] cnt = 0;
  always @(posedge clk) begin
    cnt <= cnt + 1;
    if (cnt == 4'd5) $display("sub %m cnt=%0d", cnt);
  end
  begin : blk
    always @(posedge clk) if (cnt == 4'd7) $display("blk %m");
  end
  task automatic tsk;
    $display("tsk %m");
  endtask
  always @(posedge clk) if (cnt == 4'd9) tsk();
endmodule
`endif
