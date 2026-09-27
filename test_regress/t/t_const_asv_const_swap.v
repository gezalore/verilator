// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Constant table lookup indexing a struct member used to send V3Const into
// endless recursion rotating two constants of an AND

module t;
  typedef struct packed {
    logic [3:0] a;
    logic [6:0] b;
    logic c;
  } st_t;

  localparam logic [4:0] SEL = 5'd0;
  logic [46:0] tab;
  always_comb begin
    case (SEL)
      5'd0: tab = 47'h48db2265b1f5;
      5'd1: tab = 47'h66b0d8f16adf;
      5'd2: tab = 47'h813c386bbc4;
      5'd3: tab = 47'hf17414c343c;
      5'd4: tab = 47'h61677ed4d57b;
      5'd5: tab = 47'h3c727311d8a3;
      5'd6: tab = 47'h3097a6cecc1b;
      5'd7: tab = 47'h1adfc9e9c616;
      5'd8: tab = 47'h3e7218072e8c;
      5'd9: tab = 47'h72580741c7a8;
      5'd10: tab = 47'h31e5d5f4b3b2;
      5'd11: tab = 47'h4dc06ec9d286;
      5'd12: tab = 47'h6232c324c985;
      5'd13: tab = 47'h5911008a05a6;
      5'd14: tab = 47'h22177204e52d;
      5'd15: tab = 47'h66a2b8b6d8fe;
      5'd16: tab = 47'h4baa3a902931;
      5'd17: tab = 47'hd15f1fd42a2;
      5'd18: tab = 47'h28a1e6c3f339;
      5'd19: tab = 47'h2db07d4bedc;
      5'd20: tab = 47'h532406839eb9;
      5'd21: tab = 47'h12d8a9a021e;
      5'd22: tab = 47'h70ccf06c144a;
      5'd23: tab = 47'h57de619699cf;
      5'd24: tab = 47'h7c0937730edf;
      5'd25: tab = 47'h5ce86c0fd4f5;
      5'd26: tab = 47'h4389076f3787;
      5'd27: tab = 47'h61c038c0c8fd;
      5'd28: tab = 47'h7836701966a0;
      5'd29: tab = 47'h46c47eed8d14;
      5'd30: tab = 47'h2c3f3bab6c39;
      5'd31: tab = 47'h56a23b1a11df;
    endcase
  end

  logic [2:0] in;
  st_t st;
  always_comb begin
    st = '0;
    st.b[3'(tab[21:20])] = in[0];
  end

  initial begin
    in = 3'b001;
    #1;
    if (st !== 12'h008) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
