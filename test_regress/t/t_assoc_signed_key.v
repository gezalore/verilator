// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Associative arrays with a signed integral index type are ordered in signed
// numerical order (IEEE 1800-2023 7.8.4)
module t;
  typedef logic signed [4:0] s5_t;
  typedef logic signed [69:0] s70_t;
  typedef logic signed [64:0] s65_t;
  typedef enum int { NEG = -2, ZERO = 0, POS = 3 } e_t;

  int aint[int];
  byte abyte[byte];
  longint along[longint];
  shortint ashort[shortint];
  int unsigned auint[int unsigned];
  int as5[s5_t];
  int as70[s70_t];
  int as65[s65_t];
  int aenum[e_t];
  int abit[bit [31:0]];

  int ki;
  byte kb;
  longint kl;
  s5_t k5;
  s70_t k70;
  s65_t k65;
  e_t ke;
  string s;

  initial begin
    aint[3] = 1;
    aint[-5] = 2;
    aint[10] = 3;
    aint[-1] = 4;
    aint[32'sh8000_0000] = 5;
    s = "";
    foreach (aint[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-2147483648 -5 -1 3 10 ");
    `checkd(aint.first(ki), 1);
    `checkd(ki, -2147483648);
    `checkd(aint.next(ki), 1);
    `checkd(ki, -5);
    `checkd(aint.last(ki), 1);
    `checkd(ki, 10);
    `checkd(aint.prev(ki), 1);
    `checkd(ki, 3);
    `checkd(aint.prev(ki), 1);
    `checkd(ki, -1);

    abyte[1] = 1;
    abyte[-1] = 2;
    abyte[-128] = 3;
    abyte[127] = 4;
    s = "";
    foreach (abyte[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-128 -1 1 127 ");
    `checkd(abyte.first(kb), 1);
    `checkd(kb, -128);

    ashort[-300] = 1;
    ashort[300] = 2;
    s = "";
    foreach (ashort[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-300 300 ");

    along[1] = 1;
    along[-1] = 2;
    along[64'sh8000_0000_0000_0000] = 3;
    s = "";
    foreach (along[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-9223372036854775808 -1 1 ");
    `checkd(along.last(kl), 1);
    `checkd(kl, 1);

    // Unsigned stays unsigned
    auint[1] = 1;
    auint[32'hffff_ffff] = 2;
    s = "";
    foreach (auint[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "1 4294967295 ");

    as5[5'sd15] = 1;
    as5[-5'sd16] = 2;
    as5[-5'sd1] = 3;
    as5[5'sd0] = 4;
    s = "";
    foreach (as5[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-16 -1 0 15 ");
    `checkd(as5.first(k5), 1);
    `checkd(k5, -16);

    as70[70'sd7] = 1;
    as70[-70'sd7] = 2;
    as70[-70'sd1] = 3;
    as70[70'sd0] = 4;
    as70[-(70'sd1 <<< 68)] = 5;
    s = "";
    foreach (as70[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-295147905179352825856 -7 -1 0 7 ");
    `checkd(as70.first(k70), 1);
    `checkd(k70, -(70'sd1 <<< 68));
    `checkd(as70.last(k70), 1);
    `checkd(k70, 70'sd7);

    as65[65'sd2] = 1;
    as65[-65'sd2] = 2;
    as65[65'sd1 <<< 63] = 3;
    s = "";
    foreach (as65[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "-2 2 9223372036854775808 ");
    `checkd(as65.first(k65), 1);
    `checkd(k65, -65'sd2);

    aenum[POS] = 1;
    aenum[NEG] = 2;
    aenum[ZERO] = 3;
    s = "";
    foreach (aenum[k]) s = {s, $sformatf("%s ", k.name())};
    `checks(s, "NEG ZERO POS ");
    `checkd(aenum.first(ke), 1);
    `checkd(ke, NEG);

    // Assignment between equivalent index types that order differently
    abit = aint;
    s = "";
    foreach (abit[k]) s = {s, $sformatf("%0d ", k)};
    `checks(s, "3 10 2147483648 4294967291 4294967295 ");
    abit[3] = 0;
    aint = abit;
    s = "";
    foreach (aint[k]) s = {s, $sformatf("%0d:%0d ", k, aint[k])};
    `checks(s, "-2147483648:5 -5:2 -1:4 3:0 10:3 ");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
