// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked arrays assigned to reversed arrays at run time, by the left-to-right
// order of their elements (IEEE 1800-2023 7.6)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int be_t[0:3];
typedef int le_t[3:0];

module sub (
    input le_t le,
    output le_t le_o
);
  assign le_o = '{30, 31, 32, 33};
  function automatic int left();
    return le[3];
  endfunction
endmodule

module t;
  be_t be;
  le_t le;
  le_t le_cond;
  le_t le_w;
  be_t be_out;
  be_t be_o;
  be_t be_io;
  be_t be_b;
  le_t le_nba;
  int le_s[1:0];
  le_t le_r;
  le_t aa[int];
  le_t da[];
  le_t q[$];
  int be2[0:1][0:2];
  int le2[1:0][2:0];
  int outer[1:0][0:2];
  int inner[0:1][2:0];
  bit sel;
  int pe[2][3:0];
  struct {
    int a[3:0];
    int b;
  } sv;

  assign le_w = be;

  sub u_sub (
      .le(be),
      .le_o(be_out)
  );

  function automatic int f_arg(le_t a);
    return a[3];
  endfunction
  function automatic int f_sel(le_t a, int k);
    return a[k];
  endfunction
  task automatic t_out(output le_t o);
    o = '{20, 21, 22, 23};
  endtask
  task automatic t_inout(inout le_t a);
    a[3] += 100;
  endtask
  function automatic le_t f_ret();
    return be;
  endfunction

  initial begin
    for (int i = 0; i < 4; ++i) be[i] = 10 + $urandom_range(i, i);
    for (int i = 0; i < 4; ++i) be_b[i] = 50 + $urandom_range(i, i);
    for (int i = 0; i < 2; ++i)
      for (int j = 0; j < 3; ++j) be2[i][j] = 10 * i + j + $urandom_range(0, 0);
    sel = $urandom_range(1, 1) == 1;
    // Assignment
    le = be;
    `checkd(le[3], 10);
    `checkd(le[0], 13);
    // Conditional of reversed operands
    le_cond = sel ? be : le;
    `checkd(le_cond[3], 10);
    le_cond = !sel ? le : be;
    `checkd(le_cond[0], 13);
    // Function argument, and an element of it selected by a variable index
    `checkd(f_arg(be), 10);
    `checkd(f_sel(be, $urandom_range(3, 3)), 10);
    `checkd(f_sel(be, $urandom_range(1, 1)), 12);
    // Output and inout task arguments
    t_out(be_o);
    `checkd(be_o[0], 20);
    `checkd(be_o[3], 23);
    be_io = be;
    t_inout(be_io);
    `checkd(be_io[0], 110);
    `checkd(be_io[3], 13);
    // Pattern elements and members
    pe = '{be, be};
    `checkd(pe[1][3], 10);
    `checkd(pe[1][0], 13);
    sv = '{a: be, b: 1};
    `checkd(sv.a[3], 10);
    `checkd(sv.a[0], 13);
    pe = '{1: be, 0: be_b};
    `checkd(pe[1][3], 10);
    `checkd(pe[0][3], 50);
    `checkd(pe[0][0], 53);
    // Declaration with an initial value, and nonblocking assignment, checked after the delay
    begin
      automatic le_t le_decl = be;
      `checkd(le_decl[3], 10);
    end
    le_nba <= be;
    // A slice
    le_s = be[0:1];
    `checkd(le_s[1], 10);
    `checkd(le_s[0], 11);
    `checkd(le_s == be[0:1], 1'b1);
    // Elements of an associative array, a dynamic array and a queue
    aa[1] = be;
    `checkd(aa[1][3], 10);
    da = new[1];
    da[0] = be;
    `checkd(da[0][3], 10);
    q.push_back(be);
    `checkd(q[0][3], 10);
    q = {q, be};
    `checkd(q[1][3], 10);
    da = {da, be};
    `checkd(da[1][3], 10);
    // Return value
    le_r = f_ret();
    `checkd(le_r[3], 10);
    `checkd(le_r[0], 13);
    // Arrays of arrays, reversed in both, or only one level
    le2 = be2;
    `checkd(le2[1][2], 0);
    `checkd(le2[0][0], 12);
    outer = be2;
    `checkd(outer[1][0], 0);
    `checkd(outer[0][2], 12);
    inner = be2;
    `checkd(inner[0][2], 0);
    `checkd(inner[1][0], 12);
    #1;
    `checkd(le_nba[3], 10);
    `checkd(le_nba[0], 13);
    // Continuous assignment, and input and output port
    `checkd(le_w[3], 10);
    `checkd(le_w[0], 13);
    `checkd(u_sub.left(), 10);
    `checkd(be_out[0], 30);
    `checkd(be_out[3], 33);
    // Equality, by the left-to-right order of elements (IEEE 1800-2023 7.4.6)
    `checkd(le == be, 1'b1);
    `checkd(le === be, 1'b1);
    `checkd(le2 == be2, 1'b1);
    `checkd(be == le_w, 1'b1);
    `checkd(le != be, 1'b0);
    // The same values at the same offsets, but in reverse left-to-right order
    le = '{13, 12, 11, 10};
    `checkd(le == be, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
