// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  event e1, e2, e3, e4;
  int log_[$];

  task automatic trig4();
    #1 ->> e4;
  endtask

  // Nonblocking event triggers from processes that are resumed after a delay
  initial begin
    fork
      begin
        wait (e1.triggered);
        log_.push_back(1);
      end
      begin
        #1 ->> e1;
        log_.push_back(2);
      end
    join
    fork
      begin
        @(e2);
        log_.push_back(3);
      end
      begin
        #1 ->> e2;
        log_.push_back(4);
      end
    join
    #1 ->> e3;
    fork
      begin
        @(e4);
        log_.push_back(5);
      end
      trig4();
    join
    #1;
    if (log_ != '{2, 1, 4, 3, 6, 5}) begin
      $display("%%Error: log %p", log_);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    @(e3);
    log_.push_back(6);
  end
  initial #10 $stop;  // Timeout
endmodule
