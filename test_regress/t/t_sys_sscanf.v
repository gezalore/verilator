// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  localparam int unsigned XLEN = 32;

  string pkt;
  int unsigned idx;
  logic [XLEN-1:0] val;
  int code;

  reg [255:0] line;
  reg [63:0] token;
  longint slong;

  initial begin
    // All digits after % is to get line coverage in verilated.cpp
    code = $sscanf("P20=4cff0000", "P%h=%80123456789h", idx, val);
    `checkh(code, 2);
    `checkh(idx, 32'h20);
    `checkh(val, 32'h4cff0000);

    line = "Hello 1 2 3";
    code = $sscanf(line, "%s %x\n", token, idx);
    `checkh(code, 2);
    `checks(token, "\0\0\0Hello");
    `checkh(idx, 1);

    // Input ends after some conversions: return the number assigned, not EOF
    code = $sscanf("Hi 5", "%s %d %d", token, idx, val);
    `checkh(code, 2);
    `checks(token, "\0\0\0\0\0\0Hi");
    `checkh(idx, 5);

    // Matching failure before the first conversion: 0
    code = $sscanf("Hi", "%d", idx);
    `checkh(code, 0);

    // Input ends before the first conversion: EOF
    code = $sscanf("", "%d", idx);
    `checkh(code, -1);

    // Decimal values beyond the signed 64-bit range into an unsigned target
    code = $sscanf("18446744073709551615", "%d", token);
    `checkh(code, 1);
    `checkh(token, 64'hffffffffffffffff);
    code = $sscanf("9223372036854775808", "%d", token);
    `checkh(token, 64'h8000000000000000);
    code = $sscanf("-9223372036854775808", "%d", slong);
    `checkh(slong, 64'sh8000000000000000);
    code = $sscanf("-2", "%d", token);
    `checkh(token, 64'hfffffffffffffffe);

    // Decimal values with underscores (IEEE 1800-2023 21.3.4.3)
    code = $sscanf("1_000 -2_5", "%d %d", idx, slong);
    `checkh(code, 2);
    `checkh(idx, 1000);
    `checkh(slong, -25);

    // Maximum field width (IEEE 1800-2023 21.3.4.3)
    code = $sscanf("1234", "%2d%2d", idx, val);
    `checkh(code, 2);
    `checkh(idx, 12);
    `checkh(val, 34);
    code = $sscanf("abcdef", "%2h%4x", idx, val);
    `checkh(code, 2);
    `checkh(idx, 'hab);
    `checkh(val, 'hcdef);
    code = $sscanf("1100 17", "%2b%b %1o", idx, val, slong);
    `checkh(code, 3);
    `checkh(idx, 'b11);
    `checkh(val, 'b00);
    `checkh(slong, 1);
    code = $sscanf("Hello", "%3s%s", pkt, token);
    `checkh(code, 2);
    `checks(pkt, "Hel");
    `checks(token, "\0\0\0\0\0\0lo");
    code = $sscanf("12345", "%*2d%d", idx);
    `checkh(code, 1);
    `checkh(idx, 345);

    $finish;
  end

endmodule
