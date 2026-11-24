// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on


// Test case 1
class uvm_reg_field;
  rand int m_value;
endclass

class reg_class;
  rand int m_value;
  rand uvm_reg_field _dummy;
  constraint _dummy_is_reg {_dummy.m_value == m_value;}
  function new();
    _dummy = new;
  endfunction
endclass

class block_class;
  rand reg_class m_r;
  function new();
    m_r = new;
  endfunction
endclass

class tb_test;
  virtual task run_phase(int phase);
    block_class regmodel;
    regmodel = new;
    // verilator lint_off IGNOREDRETURN
    void'(regmodel.randomize() with {m_r.m_value == 32'hA5;});
    // verilator lint_on IGNOREDRETURN
    if (regmodel.m_r.m_value != 32'hA5) $stop;
  endtask
endclass


// Test case 2
class axi_agent_config;
   rand bit r_ready_delays;
   constraint r_ready_delays_c {
      r_ready_delays == 0;
   }
endclass

class axi_env_config;
   rand axi_agent_config   axim_agt_cfg;
   function new();
      axim_agt_cfg = new;
   endfunction
endclass

class axi_base_test;
  axi_env_config axi_env_cfg;
  virtual function void build_phase();
    configure_axi_env();
  endfunction
  function void configure_axi_env();
    axi_env_cfg = new;
  endfunction
endclass

class axi_wrap_test extends axi_base_test;
  function void configure_axi_env();
    void'(axi_env_cfg.randomize());
  endfunction
endclass


// Test case 3: rand member inherited from the base class
class sub_cfg;
  rand bit g;
  constraint c {g == 1;}
endclass

class base_cfg;
  rand sub_cfg s;
  function new();
    s = new;
  endfunction
endclass

class derived_cfg extends base_cfg;
endclass


// Test: static rand members of a rand member, constrained in their class and through the handle
class static_cfg;
  static rand bit g;
  static rand bit h;
  constraint c {g == 1;}
endclass

class static_cfg_holder;
  rand static_cfg s;
  constraint c {s.h == 1;}
  function new();
    s = new;
  endfunction
endclass


// Test: a static rand member not reached through a rand handle is a state variable
class state_cfg;
  static rand bit [6:0] x;
endclass

class state_cfg_user;
  state_cfg o;
  rand bit [6:0] y;
  rand bit [6:0] z;
  constraint c {
    y == o.x;
    z == state_cfg::x;
  }
  function new();
    o = new;
  endfunction
endclass


// Test: rand_mode of static rand members of a rand member
class mode_cfg;
  static rand bit [3:0] g;
  constraint c {g > 0;}
endclass

class mode_cfg_holder;
  rand mode_cfg s;
  static rand bit [3:0] k;
  function new();
    s = new;
  endfunction
endclass


// Test: static rand member of a rand member whose class is also randomized directly
class order_cfg;
  static rand bit [3:0] h;
  constraint c {h < 8;}
endclass

class order_cfg_holder;
  rand order_cfg s;
  constraint c {s.h == 3;}
  function new();
    s = new;
  endfunction
endclass


module t_constraint_global_nested_member;
  initial begin
    tb_test tb;
    axi_wrap_test axi_t;
    derived_cfg d;

    tb = new;
    tb.run_phase(0);

    axi_t = new();
    axi_t.build_phase();

    d = new;
    repeat (20) begin
      if (d.randomize() != 1) $stop;
      if (d.s.g != 1) $stop;
    end

    begin
      automatic static_cfg_holder sh = new;
      automatic int ok;
      repeat (20) begin
        ok = sh.randomize();
        `checkd(ok, 1);
        `checkd(static_cfg::g, 1);
        `checkd(static_cfg::h, 1);
      end
    end

    begin
      automatic state_cfg_user su = new;
      automatic int ok;
      state_cfg::x = 93;
      repeat (20) begin
        ok = su.randomize();
        `checkd(ok, 1);
        `checkd(state_cfg::x, 93);
        `checkd(su.y, 93);
        `checkd(su.z, 93);
      end
    end

    begin
      automatic mode_cfg_holder mh = new;
      automatic int ok;
      mode_cfg::g = 11;
      mh.s.g.rand_mode(0);
      repeat (20) begin
        ok = mh.randomize();
        `checkd(ok, 1);
        `checkd(mode_cfg::g, 11);
      end
      // Disabling the holder's own static leaves the member's static random
      mh.s.g.rand_mode(1);
      mode_cfg_holder::k.rand_mode(0);
      mode_cfg::g = 0;
      mode_cfg_holder::k = 5;
      repeat (20) begin
        ok = mh.randomize();
        `checkd(ok, 1);
        `checkd(mode_cfg::g != 0, 1);
        `checkd(mode_cfg_holder::k, 5);
      end
    end

    begin
      automatic order_cfg oc = new;
      automatic order_cfg_holder oh = new;
      automatic int ok;
      ok = oc.randomize();
      `checkd(ok, 1);
      `checkd(order_cfg::h < 8, 1);
      repeat (20) begin
        ok = oh.randomize();
        `checkd(ok, 1);
        `checkd(order_cfg::h, 3);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
