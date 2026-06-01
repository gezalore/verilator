// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  typedef struct {
    int m;
    int n[3];
  } s_t;

  function automatic int one();
    return 1;
  endfunction

  function automatic int two();
    /* verilator no_inline_task */
    return 2;
  endfunction

  function automatic int addOne(int v);
    /* verilator no_inline_task */
    return v + 1;
  endfunction

  int bumped;

  function automatic int bump(int v);
    bumped += 1;
    return v + 1;
  endfunction

  class C;
    static int i = one() + 1;
    static int j = two() + 1;
  endclass

  logic [15:0] fvec;
  s_t farr[2];
  int fidx[2];
  logic [15:0] r;

  initial begin
    `checkh(C::i, 2);
    `checkh(C::j, 3);

    fvec = 16'h1111;
    farr[1].m = 32'h0a;
    farr[1].n[2] = 32'h0b;
    fidx[1] = 0;

    force fvec = 16'habcd;
    force farr[1].m = 32'h11;
    force farr[1].n[2] = 32'h22;
    force fidx[1] = 2;

    // Whole variable read as the RHS of a simple assignment is in normal form already
    r = fvec;
    `checkh(r, 16'habcd);

    // Whole variable read under an expression is lifted
    `checkh(fvec + 16'h1, 16'habce);

    // Part select of a forced variable, the whole Sel is the read
    `checkh(fvec[7:4], 4'hc);

    // Member of a forced struct array element, the whole select path is one read
    `checkh(farr[1].m, 32'h11);

    // Element of an array member, so nested selects, but still just one read
    `checkh(farr[1].n[2], 32'h22);

    // A forced read in index position is a read in its own right, lifted separately
    `checkh(farr[1].n[fidx[1]], 32'h22);

    // Lifted alongside a call in the same expression
    `checkh(addOne(32'(fvec[3:0])), 32'he);

    // Short circuiting operators must not evaluate the read on the untaken side.
    // 'bump' has a side effect, so the LogAnd is not folded into a bitwise And.
    bumped = 0;
    `checkh(fvec[1] && (bump(farr[1].m) != 0), 1'b0);
    `checkh(bumped, 0);
    `checkh(fvec[0] ? farr[1].m : farr[1].n[2], 32'h11);

    release fvec;
    release farr[1].m;
    release farr[1].n[2];
    release fidx[1];

    // A released variable holds the forced value until next written
    `checkh(fvec + 16'h1, 16'habce);
    `checkh(farr[1].m, 32'h11);
    `checkh(farr[1].n[fidx[1]], 32'h22);

    fvec = 16'h2222;
    farr[1].m = 32'h33;
    farr[1].n[2] = 32'h44;
    fidx[1] = 2;

    `checkh(fvec + 16'h1, 16'h2223);
    `checkh(farr[1].m, 32'h33);
    `checkh(farr[1].n[fidx[1]], 32'h44);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
