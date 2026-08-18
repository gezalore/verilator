// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%h' exp='%h'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks_w(width,gotv,expv) do begin \
  logic [(width)-1:0] got_check; \
  logic [(width)-1:0] exp_check; \
  got_check = (gotv); \
  exp_check = (expv); \
  `checks(got_check, exp_check) \
end while(0);
module t;

  logic [7:0] i_char;
  logic [15:0] i_short;
  int i_header;
  int i_len;
  int i_data;
  int i_crc;

  logic [7:0] o_char;
  logic [15:0] o_short;
  int o_header;
  int o_len;
  int o_data;
  int o_crc;

  logic [128:0] wide129;
  logic [127:0] wide128;
  logic [31:0] wide32;
  logic [257:0] wide258;
  logic [63:0] packed64;
  logic [255:0] o_wide256;
  logic [1:0] o_2bit;
  logic [15:0] rev16;
  logic [31:0] rev32;
  logic [63:0] rev64;
  logic [15:0] o_short2;

  initial begin
    byte byte_pkt[$];
    logic [15:0] sdata_pkt[$];
    int int_pkt[$];
    logic [63:0] qdata_pkt[$];
    logic [128:0] vlwide_pkt_129[$];//this is off by one to test edge cases
    logic [127:0] vlwide_pkt_128[$];
    logic [127:0] vlwide_pkt_128b[$];
    logic [95:0] vlwide_pkt_96[$];//elements are not a power of two words wide
    byte unsigned unpk[4];
    logic [15:0] unpk16[2];
/* verilator lint_off ASCRANGE */
    byte unsigned unpk_desc[3:0];
/* verilator lint_on ASCRANGE */
/* verilator lint_off ASCRANGE */
    logic [0:7] byte_pkt_rev[$];
    logic [0:15] sdata_pkt_rev[$];
    logic [0:31] int_pkt_rev[$];
    logic [0:63] qdata_pkt_rev[$];
    logic [0:128] vlwide_pkt_129_rev[$];//this is off by one to test edge cases
    logic [0:127] vlwide_pkt_128_rev[$];


    i_header = 12;
    i_len = 5;
    i_data = 11;
    i_crc = 42;
    i_char = 15;
    i_short = 16'hFF;
    #0; // this forces no-life
    //TODO make this work with V3Life
    //-------------------- STREAML ------------------------------------
    //----------- CData QUEUE --------
    byte_pkt = {<<8{i_char}};
    o_char = {<<8{byte_pkt}};
    `checks(o_char,i_char);

    byte_pkt = {<<8{i_short}};
    o_short = {<<8{byte_pkt}};
    `checks(o_short,i_short);

    byte_pkt = {<<8{i_header}};
    o_header = {<<8{byte_pkt}};
    `checks(o_header,i_header);

    byte_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = byte_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks_w(128, {>>{byte_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks_w(128, {i_header,i_len,i_crc,i_data},{<<8{byte_pkt}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // //----------- SData QUEUE --------
    // sdata_pkt = {<<8{i_char}};
    //TODO This should compile
    // o_char = {{<<8{sdata_pkt}}}[7:0];
    // `checks(o_char,i_char);

    sdata_pkt = {<<8{i_short}};
    o_short = {<<8{sdata_pkt}};
    `checks(o_short,i_short);

    sdata_pkt = {<<8{i_header}};
    o_header = {<<8{sdata_pkt}};
    `checks(o_header,i_header);

    //test with QData
    sdata_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = sdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    sdata_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = sdata_pkt;

    `checks_w(128, {>>{sdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt = {<<8{i_header}};
    o_header = {<<8{int_pkt}};
    `checks(o_header,i_header);

    //test with QData
    int_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = int_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks_w(128, {>>{int_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------
    qdata_pkt = {<<8{i_header}};
    // o_header = {<<8{qdata_pkt}};
    //TODO This should compile
    // o_header = {{<<8{sdata_pkt}}}[32:0];
    // `checks(o_header,i_header);

    //test with QData
    qdata_pkt = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});


    qdata_pkt = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks_w(128, {>>{qdata_pkt}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------
    // test with QData
    vlwide_pkt_129 = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = vlwide_pkt_129; //TODO this shouldn't compile lhs should not be smaller then rhs
    // `checks({i_header,i_len},{o_header,o_len});

    vlwide_pkt_129 = {<<8{i_header,i_len,i_crc,i_data}};

    /* verilator lint_off WIDTHEXPAND */
    wide129 = {<<8{i_header,i_len,i_crc,i_data}};
    `checks_w(129, {>>{vlwide_pkt_129}},wide129);
    /* verilator lint_on WIDTHEXPAND */

    //------------------------------- REVERSE ENDIAN ------------------------------
    //----------- CData QUEUE --------
    byte_pkt_rev = {<<8{i_char}};
    o_char = {<<8{byte_pkt_rev}};
    `checks(o_char,i_char);

    byte_pkt_rev = {<<8{i_short}};
    o_short = {<<8{byte_pkt_rev}};
    `checks(o_short,i_short);

    byte_pkt_rev = {<<8{i_header}};
    o_header = {<<8{byte_pkt_rev}};
    `checks(o_header,i_header);

    byte_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = byte_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = byte_pkt_rev;

    `checks_w(128, {>>{byte_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks_w(128, {i_header,i_len,i_crc,i_data},{<<8{byte_pkt_rev}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

        //----------- SData QUEUE --------
    sdata_pkt_rev = {<<8{i_short}};
    o_short = {<<8{sdata_pkt_rev}};
    `checks(o_short,i_short);

    sdata_pkt_rev = {<<8{i_header}};
    o_header = {<<8{sdata_pkt_rev}};
    `checks(o_header,i_header);

    //test with QData
    sdata_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = sdata_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    sdata_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = sdata_pkt_rev;

    `checks_w(128, {>>{sdata_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt_rev = {<<8{i_header}};
    o_header = {<<8{int_pkt_rev}};
    `checks(o_header,i_header);

    //test with QData
    int_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = int_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = int_pkt_rev;

    `checks_w(128, {>>{int_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------

    //test with QData
    qdata_pkt_rev = {<<8{i_header,i_len}};
    {<<8{o_header,o_len}} = qdata_pkt_rev;
    `checks({i_header,i_len},{o_header,o_len});


    qdata_pkt_rev = {<<8{i_header,i_len,i_crc,i_data}};
    {<<8{o_header,o_len,o_crc,o_data}} = qdata_pkt_rev;

    `checks_w(128, {>>{qdata_pkt_rev}},{<<8{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------

    vlwide_pkt_129_rev = {<<8{i_header,i_len,i_crc,i_data}};
    /* verilator lint_off WIDTHEXPAND */
    wide129 = {<<8{i_header,i_len,i_crc,i_data}};
    /* verilator lint_on WIDTHEXPAND */
    `checks_w(129, {>>{vlwide_pkt_129_rev}},wide129);

    // // -------------------- STREAMR ------------------------------------
    // //----------- CData QUEUE --------
    byte_pkt = {>>{i_header}};
    o_header = {>>{byte_pkt}};
    `checks(o_header,i_header);

    byte_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = byte_pkt;
    `checks_w(64, {>>{i_header,i_len}},{>>{o_header,o_len}});
    `checks({i_header,i_len},{o_header,o_len});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = byte_pkt;

    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- IData QUEUE --------
    int_pkt = {>>{i_header}};
    o_header = {>>{int_pkt}};
    `checks(o_header,i_header);
    `checks_w(32, o_header,{>>{int_pkt}});
    `checks_w(32, {>>{o_header}},{>>{int_pkt}});

    //test with QData
    int_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = int_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = int_pkt;

    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    //----------- QData QUEUE --------

    // test with QData
    qdata_pkt = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = qdata_pkt;
    `checks({i_header,i_len},{o_header,o_len});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = qdata_pkt;

    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- VLWide QUEUE --------

    // test with QData
    vlwide_pkt_129 = {>>{i_header,i_len}};
    {>>{o_header,o_len}} = vlwide_pkt_129; //TODO this shouldn't compile lhs should not be smaller then rhs
    // `checks({i_header,i_len},{o_header,o_len});


    vlwide_pkt_129 = {>>{i_header,i_len,i_crc,i_data}};
    {>>{o_header,o_len,o_crc,o_data}} = vlwide_pkt_129; //TODO this shouldn't compile lhs should not be smaller then rhs

    // The 128 bit stream is left aligned in the 129 bit element, so the padding
    // is in the least significant bit (IEEE 1800-2023 11.4.14.3)
    `checks_w(129, {>>{vlwide_pkt_129}},{>>{i_header,i_len,i_crc,i_data,1'b0}});
    // `checks({o_header,o_len,o_crc,o_data} ,{i_header,i_len,i_crc,i_data});

    // ----------- Queues of elements no wider than QData, stream narrower --------
    // than the element, or not filling the last element

    // 32 bit stream into 64 bit elements
    qdata_pkt = {>>{i_header}};
    `checks(qdata_pkt.size(), 1);
    `checks(qdata_pkt[0], {i_header, 32'h0});

    // 96 bit stream into 64 bit elements, so the last element is half filled
    qdata_pkt = {>>{i_header,i_len,i_crc}};
    `checks(qdata_pkt.size(), 2);
    `checks(qdata_pkt[0], {i_header, i_len});
    `checks(qdata_pkt[1], {i_crc, 32'h0});

    // 32 bit stream into 8 bit elements needs four elements, and no more
    byte_pkt = {>>{i_header}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], i_header[31:24]);
    `checks(byte_pkt[1], i_header[23:16]);
    `checks(byte_pkt[2], i_header[15:8]);
    `checks(byte_pkt[3], i_header[7:0]);

    // 16 bit stream into 32 bit elements. The stream is not a whole number of
    // words wide, so it must still reach the runtime as a stream
    int_pkt = {>>{i_short}};
    `checks(int_pkt.size(), 1);
    `checks(int_pkt[0], {i_short, 16'h0});

    // As above with a dirty stream operand, which is cleaned in place
    int_pkt = {>>{i_short + i_short}};
    `checks(int_pkt.size(), 1);
    `checks(int_pkt[0], {(i_short + i_short), 16'h0});

    // 16 bit stream into 8 bit elements needs two elements, and no more
    byte_pkt = {>>{i_short}};
    `checks(byte_pkt.size(), 2);
    `checks(byte_pkt[0], i_short[15:8]);
    `checks(byte_pkt[1], i_short[7:0]);

    // Left streams of the same, the reversal is on the stream, then aligned
    rev32 = {<<8{i_header}};
    qdata_pkt = {<<8{i_header}};
    `checks(qdata_pkt.size(), 1);
    `checks(qdata_pkt[0], {rev32, 32'h0});

    // ----------- Streams between queues and other element or packed widths --------

    // A stream narrower than its packed destination is left aligned in it,
    // whatever the size of the destination
    byte_pkt = {8'h12, 8'h34};
    `checks_w(16, {>>{byte_pkt}}, 16'h1234);
    `checks_w(32, {>>{byte_pkt}}, 32'h12340000);
    `checks_w(64, {>>{byte_pkt}}, 64'h1234000000000000);
    `checks_w(128, {>>{byte_pkt}}, 128'h12340000000000000000000000000000);

    // A right stream on the left hand side packs a queue into its single
    // packed destination
    {>>{packed64}} = byte_pkt;
    `checks(packed64, 64'h1234000000000000);

    // A left stream into a queue whose elements are of a different width
    sdata_pkt = {<<8{byte_pkt}};
    `checks(sdata_pkt.size(), 1);
    `checks(sdata_pkt[0], 16'h3412);

    // A left stream with a slice size that is not a power of two, cross checked
    // against the same stream into a packed destination
    rev16 = {<<3{i_short}};
    byte_pkt = {<<3{i_short}};
    `checks(byte_pkt.size(), 2);
    `checks(byte_pkt[0], rev16[15:8]);
    `checks(byte_pkt[1], rev16[7:0]);

    // Reblocking a stream into elements of another width
    sdata_pkt = {16'h1122, 16'h3344, 16'h5566, 16'h7788};
    int_pkt = {>>{sdata_pkt}};
    `checks(int_pkt.size(), 2);
    `checks(int_pkt[0], 32'h11223344);
    `checks(int_pkt[1], 32'h55667788);
    qdata_pkt = {>>{sdata_pkt}};
    `checks(qdata_pkt.size(), 1);
    `checks(qdata_pkt[0], 64'h1122334455667788);

    // Reblocking between queues of elements wider than a QData
    vlwide_pkt_128 = {128'h00112233_44556677_8899aabb_ccddeeff};
    vlwide_pkt_128b = {>>{vlwide_pkt_128}};
    `checks(vlwide_pkt_128b.size(), 1);
    `checks(vlwide_pkt_128b[0], vlwide_pkt_128[0]);

    // Elements that are not a whole number of words, unpacked into a
    // destination of the same width as the stream
    wide258 = 258'h3_00112233445566778899aabbccddeeff_ffeeddccbbaa99887766554433221100;
    vlwide_pkt_129 = {>>{wide258}};
    `checks(vlwide_pkt_129.size(), 2);
    {>>{o_2bit, o_wide256}} = vlwide_pkt_129;
    `checks(o_2bit, wide258[257:256]);
    `checks_w(256, o_wide256, wide258[255:0]);

    // ----------- Unpacked array source into a queue --------

    unpk = '{8'h11, 8'h22, 8'h33, 8'h44};
    byte_pkt = {>>{unpk}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], 8'h11);
    `checks(byte_pkt[3], 8'h44);

    // Into elements of a width other than the source's
    int_pkt = {>>{unpk}};
    `checks(int_pkt.size(), 1);
    `checks(int_pkt[0], 32'h11223344);

    // Declared descending, so its elements stream in declaration order
    unpk_desc[3] = 8'h11;
    unpk_desc[2] = 8'h22;
    unpk_desc[1] = 8'h33;
    unpk_desc[0] = 8'h44;
    byte_pkt = {>>{unpk_desc}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], 8'h11);
    `checks(byte_pkt[3], 8'h44);

    // A left stream reverses the whole stream in slices of the given size, which
    // need not be the element width of either side, cross checked against the
    // same stream into a packed destination
    unpk16 = '{16'h1122, 16'h3344};
    wide32 = {<<8{unpk16}};
    byte_pkt = {<<8{unpk16}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], wide32[31:24]);
    `checks(byte_pkt[3], wide32[7:0]);

    wide32 = {<<3{unpk}};
    byte_pkt = {<<3{unpk}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], wide32[31:24]);
    `checks(byte_pkt[3], wide32[7:0]);

    wide32 = {<<8{unpk_desc}};
    byte_pkt = {<<8{unpk_desc}};
    `checks(byte_pkt.size(), 4);
    `checks(byte_pkt[0], wide32[31:24]);
    `checks(byte_pkt[3], wide32[7:0]);

    // ----------- VLWide QUEUE, checking the element contents --------
    // A stream narrower than its destination is left aligned, and the remaining
    // least significant bits of the destination are zeroed (IEEE 1800-2023
    // 11.4.14.3), so the whole of the destination element must be assigned.

    // 32 bit stream, one partially filled element
    vlwide_pkt_128 = {>>{i_header}};
    `checks(vlwide_pkt_128.size(), 1);
    `checks(vlwide_pkt_128[0], {i_header, 96'h0});

    // 64 bit stream, one partially filled element
    vlwide_pkt_128 = {>>{i_header,i_len}};
    `checks(vlwide_pkt_128.size(), 1);
    `checks(vlwide_pkt_128[0], {i_header, i_len, 64'h0});

    // 256 bit stream, two completely filled elements
    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data,i_data,i_crc,i_len,i_header}};
    `checks(vlwide_pkt_128.size(), 2);
    `checks(vlwide_pkt_128[0], {i_header, i_len, i_crc, i_data});
    `checks(vlwide_pkt_128[1], {i_data, i_crc, i_len, i_header});

    // 192 bit stream into elements that are not a power of two words wide
    vlwide_pkt_96 = {>>{i_header,i_len,i_crc,i_data,i_len,i_header}};
    `checks(vlwide_pkt_96.size(), 2);
    `checks(vlwide_pkt_96[0], {i_header, i_len, i_crc});
    `checks(vlwide_pkt_96[1], {i_data, i_len, i_header});

    // 192 bit stream into 128 bit elements, so the last element is only half
    // filled and its least significant bits are zeroed
    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data,i_len,i_header}};
    `checks(vlwide_pkt_128.size(), 2);
    `checks(vlwide_pkt_128[0], {i_header, i_len, i_crc, i_data});
    `checks(vlwide_pkt_128[1], {i_len, i_header, 64'h0});

    // 64 bit stream into a 129 bit element, which is not a whole number of words
    vlwide_pkt_129 = {>>{i_header,i_len}};
    `checks(vlwide_pkt_129.size(), 1);
    `checks_w(129, {>>{vlwide_pkt_129}}, {i_header, i_len, 65'h0});

    // Left stream of a 32 bit source, one partially filled element. The
    // reference is the same stream into a packed destination of the same width.
    rev32 = {<<8{i_header}};
    vlwide_pkt_128 = {<<8{i_header}};
    `checks(vlwide_pkt_128.size(), 1);
    `checks(vlwide_pkt_128[0], {rev32, 96'h0});

    // As above with a 64 bit source. This one is correct today, and pins down
    // the alignment expected by the cases above.
    rev64 = {<<8{i_header,i_len}};
    vlwide_pkt_128 = {<<8{i_header,i_len}};
    `checks(vlwide_pkt_128.size(), 1);
    `checks(vlwide_pkt_128[0], {rev64, 64'h0});

    // Unpacked back out into a target of the same width as the stream, so the
    // 64 bit source ends up in the most significant half
    vlwide_pkt_128 = {>>{i_header,i_len}};
    {>>{o_header,o_len,o_crc,o_data}} = vlwide_pkt_128;
    `checks({o_header,o_len},{i_header,i_len});
    `checks({o_crc,o_data}, 64'h0);

    // Unpacked into targets that do not start on a word boundary, so each
    // selection spans two words of the element
    wide128 = {i_header,i_len,i_crc,i_data};
    vlwide_pkt_128 = {>>{wide128}};
    {>>{o_short,o_header,o_len,o_crc,o_short2}} = vlwide_pkt_128;
    `checks(o_short, wide128[127:112]);
    `checks(o_header, wide128[111:80]);
    `checks(o_len, wide128[79:48]);
    `checks(o_crc, wide128[47:16]);
    `checks(o_short2, wide128[15:0]);

    //---------- into other queues ------
    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{int_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    sdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{sdata_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    sdata_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{sdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{byte_pkt}};
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{qdata_pkt}};
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{qdata_pkt}};
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{int_pkt}};
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    byte_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{byte_pkt}};
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    byte_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{byte_pkt}});
    `checks_w(128, {>>{byte_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    int_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{int_pkt}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    int_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{int_pkt}});
    `checks_w(128, {>>{int_pkt}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data}});

    qdata_pkt = {>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(256, {i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(256, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,i_data}});

    // The 224 bit stream leaves the last 64 bit element half filled, and it is
    // the least significant bits of that element that are zeroed
    // (IEEE 1800-2023 11.4.14.3)
    qdata_pkt = {>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc}};
    vlwide_pkt_128 = {>>{qdata_pkt}};
    `checks_w(256, {i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,32'h0},{>>{vlwide_pkt_128}});
    `checks_w(256, {>>{vlwide_pkt_128}},{>>{i_header,i_len,i_crc,i_data,i_header,i_len,i_crc,32'h0}});

    vlwide_pkt_128 = {>>{i_header,i_len,i_crc,i_data}};
    qdata_pkt = {>>{vlwide_pkt_128}};
    `checks_w(128, {i_header,i_len,i_crc,i_data},{>>{vlwide_pkt_128}});
    `checks_w(128, {>>{qdata_pkt}},{>>{i_header,i_len,i_crc,i_data}});
    $write("*-* All Finished *-*\n");
    $finish;

  end


endmodule
