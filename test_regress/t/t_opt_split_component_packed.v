// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Automatic splitting of packed arrays and structs into their elements and members

typedef struct packed {
  logic [4:0] a;
  logic [6:0] b;
} ps_t;

typedef struct packed {
  logic [5:0] hi;
  logic [5:0] lo;
} pw_t;

typedef union packed {
  logic [11:0] w;
  ps_t s;
} pu_t;

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;
  logic [63:0] crc_q = '0;

  // Packed struct, chain through members, would be UNOPTFLAT if not split
  ps_t ps;  // Split
  // Packed array, descending, chain through elements
  logic [3:0][2:0] pd;  // Split
  // Packed array, ascending
  // verilator lint_off ASCRANGE
  logic [0:3][4:0] pa;  // Split
  // verilator lint_on ASCRANGE
  // Packed array, non-zero based
  logic [4:1][3:0] pnz;  // Split
  // Packed array of packed structs, the elements are split too
  ps_t [1:0] pas;  // Split
  // Whole copy, same layout
  ps_t ps_cp;  // Split
  // Copied from, and to a plain vector
  logic [11:0] flat_in;
  ps_t pfrom;  // Split
  logic [11:0] flat_out;
  // Copied from, and to a bit select
  ps_t psel;  // Split
  logic [15:0] flat_sel;
  // Concatenation aligned with the members
  ps_t pcat;  // Split
  // Constant
  ps_t pk;  // Split
  pw_t pshr;  // Split
  logic [5:0] shr[2];
  // Result from an automatic local, reset on entry
  logic [6:0] locx;
  // Non-blocking assignments
  ps_t q;  // Split
  // Select spanning members
  ps_t pspan;  // No split: select spans members
  // Variable index
  logic [3:0][2:0] pvix;  // No split: variable index
  // Read whole in an expression
  ps_t pwhole;  // No split: referenced whole
  // Copy between different layouts
  logic [2:0][3:0] l34;  // Split
  logic [3:0][2:0] l43;  // Split
  // Only copied whole, so not split
  ps_t pw1;  // No split: only copied whole
  ps_t pw2;  // No split: only copied whole
  logic [11:0] pw_out;
  // Only copied whole, so not split, even if copied to a variable that is split
  ps_t pl1;  // No split: only copied whole
  ps_t pl2;  // Split
  // Packed union
  pu_t pu;  // No split: packed union
  // Plain vector
  logic [7:0] vec;

  assign ps.a = crc[4:0];
  assign ps.b = 7'(ps.a) + 7'd3;

  assign pd[0] = crc[2:0];
  for (genvar g = 1; g < 4; g++) begin : gen_pd
    assign pd[g] = pd[g-1] + 3'd1;
  end

  assign pa[0] = crc[4:0];
  for (genvar g = 1; g < 4; g++) begin : gen_pa
    assign pa[g] = pa[g-1] ^ crc[g*5+:5];
  end

  assign pnz[1] = crc[3:0];
  for (genvar g = 2; g <= 4; g++) begin : gen_pnz
    assign pnz[g] = pnz[g-1] + 4'd2;
  end

  always_comb begin
    pas[0].a = crc[4:0];
    pas[0].b = 7'(pas[0].a) ^ crc[11:5];
    pas[1].a = pas[0].b[4:0];
    pas[1].b = 7'(pas[1].a) + 7'd1;
  end

  assign ps_cp = ps;

  assign flat_in = crc[23:12];
  assign pfrom = flat_in;
  assign flat_out = pfrom;
  assign psel = crc[35:24];
  assign flat_sel[13:2] = psel;
  assign flat_sel[1:0] = 2'b0;
  assign flat_sel[15:14] = 2'b0;

  assign pcat = {crc[4:0], crc[13:7]};

  assign pw1 = crc[47:36];
  assign pw2 = pw1;
  assign pw_out = pw2;
  assign pl1 = crc[47:36];
  assign pl2 = pl1;

  always_comb pk = 12'h5a3;

  assign pshr = crc[47:36];
  always_comb for (int i = 0; i < 2; i++) shr[i] = 6'(pshr >> (6 * i));

  always_comb begin
    automatic ps_t loc;  // Split
    loc.a = crc[4:0];
    loc.b = 7'(loc.a) + crc[11:5];
    locx = loc.b;
  end

  always_ff @(posedge clk) begin
    q.a <= crc[4:0];
    q.b <= 7'(q.a);
    crc_q <= crc;
  end

  always_comb begin
    pspan.a = crc[4:0];
    pspan.b = crc[11:5];
    pvix[0] = crc[2:0];
    pvix[1] = pvix[0] + 3'd1;
    pvix[2] = pvix[1] + 3'd1;
    pvix[3] = pvix[2] + 3'd1;
    pwhole.a = crc[4:0];
    pwhole.b = crc[11:5];
    l34[0] = crc[3:0];
    l34[1] = l34[0] ^ crc[7:4];
    l34[2] = l34[1] ^ crc[11:8];
    l43 = l34;
    pu.w = crc[11:0];
    vec[3:0] = crc[3:0];
    vec[7:4] = vec[3:0] + 4'd1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(ps.b, 7'(crc[4:0]) + 7'd3);
    `checkh(pd[3], crc[2:0] + 3'd3);
    `checkh(pd[2][1:0], 2'(crc[2:0] + 3'd2));
    `checkh(pa[3], crc[4:0] ^ crc[9:5] ^ crc[14:10] ^ crc[19:15]);
    `checkh(pnz[4], crc[3:0] + 4'd6);
    `checkh(pas[1].b, 7'(pas[0].b[4:0]) + 7'd1);
    `checkh(pas[0].b, 7'(crc[4:0]) ^ crc[11:5]);
    `checkh(ps_cp.a, crc[4:0]);
    `checkh(ps_cp.b, 7'(crc[4:0]) + 7'd3);
    `checkh(pfrom.a, crc[23:19]);
    `checkh(pfrom.b, crc[18:12]);
    `checkh(flat_out, crc[23:12]);
    `checkh(psel.a, crc[35:31]);
    `checkh(psel.b, crc[30:24]);
    `checkh(flat_sel, {2'b0, crc[35:24], 2'b0});
    `checkh(pcat.a, crc[4:0]);
    `checkh(pcat.b, crc[13:7]);
    `checkh(pw_out, crc[47:36]);
    `checkh(pl2.a, crc[47:43]);
    `checkh(pl2.b, crc[42:36]);
    `checkh(pk.a, 5'h0b);
    `checkh(pk.b, 7'h23);
    `checkh(shr[0], crc[41:36]);
    `checkh(shr[1], crc[47:42]);
    `checkh(locx, 7'(crc[4:0]) + crc[11:5]);
    `checkh(pspan[8:3], {crc[1:0], crc[11:8]});
    `checkh(pvix[crc[1:0]], 3'(crc[2:0] + 3'(crc[1:0])));
    `checkh(pwhole ^ 12'hfff, ~{crc[4:0], crc[11:5]});
    `checkh(l43[2], {crc[8] ^ crc[4] ^ crc[0], crc[7:6] ^ crc[3:2]});
    `checkh(l43[0], crc[2:0]);
    `checkh(l43[3], {crc[11:9] ^ crc[7:5] ^ crc[3:1]});
    `checkh(pu.s.a, crc[11:7]);
    `checkh(vec[7:4], crc[3:0] + 4'd1);
    if (cyc > 1) begin
      `checkh(q.a, crc_q[4:0]);
    end
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub u_sub0 (
      .clk(clk),
      .crc(crc)
  );
  sub u_sub1 (
      .clk(clk),
      .crc(~crc)
  );

endmodule

// Not inlined, so the same variable is split in two scopes
module sub (
    input clk,
    input [63:0] crc
);
  /*verilator no_inline_module*/

  ps_t s;  // Split

  always_comb begin
    s.a = crc[4:0];
    s.b = 7'(s.a) ^ crc[11:5];
  end

  always @(posedge clk) begin
    `checkh(s.b, 7'(crc[4:0]) ^ crc[11:5]);
  end

endmodule
