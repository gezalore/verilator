// DESCRIPTION: Verilator: dynamic wait on stale class event
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (got), (exp)); `stop; end while(0)
// verilog_format: on

class EventHolder;
   event ev;
   time t_wait = '0;

   task wait_once;
      @ev;
      t_wait = $time;
   endtask
endclass

module t;
   EventHolder h;
   int a;
   int b;

   initial begin
      h = new;
      a = 0;
      b = 0;

      // Leave the event in the fired state before a class-method event control
      // starts. Dynamic waits must pre-clear this stale state before evaluating.
      ->h.ev;
      #10;

      fork
         begin
            #10 ->h.ev;
         end
         begin
            h.wait_once;
            a = 1;
         end
         begin
            h.wait_once;
            b = 1;
         end
      join

      `check(h.t_wait, 20);
      `check(a, 1);
      `check(b, 1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
