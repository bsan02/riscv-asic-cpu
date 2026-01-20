`include "const.vh"
`include "Opcode.vh"
`include "ALUop.vh"
`include "ALUdec.v"

module Riscv151(
    input clk,
    input reset,

    // Memory system ports
    output [31:0] dcache_addr,
    output [31:0] icache_addr,
    output [3:0] dcache_we,
    output dcache_re,
    output icache_re,
    output [31:0] dcache_din,
    input [31:0] dcache_dout,
    input [31:0] icache_dout,
    input stall,
    output [31:0] csr
    );

    /////////////////////////////////////////////////////////////
    //STAGE 1: Instruction fetch
    localparam PC_RESET = 32'h2000; // RESET constant val --> "const.vh"

    // FETCH -> IF
    reg [31:0] s0_pc_reg;        // PC for IMEM (instruction fetch stage0)vQ
    reg [31:0] next_pc;
    reg [31:0] s0_inst_reg;
    reg flushed;

    // IF -> ID/EX
    reg [31:0] s1_pc_reg;        // PC passed to decode stage01 and memory/wb stage02
    wire [31:0] s1_inst_reg;      // pipelined reg for inst. passed to decode stage
    reg [31:0] imm_out;

    wire [3:0] ALUop;
    wire ASel, BSel;
    wire [31:0] A, B;
    reg [31:0] rf_rs1_data, rf_rs2_data, rs1_data, rs2_data, alu_result;
    wire RegWrite;
    wire [1:0] WBsel;

    reg branch_taken;
    reg PCsel;

    // IF/EX -> WB
    reg [31:0] s2_pc_reg, s2_pc_plus_4;
    reg [31:0] s2_alu_result;
    reg s2_PCSel;
    reg [1:0] s2_WBsel;
    reg s2_RegWrite;
    reg [4:0] s2_rd;
    reg [31:0] s2_imm_out;
    reg [6:0] s2_opcode;
    reg [2:0] s2_funct3;
    reg [31:0] s2_rs1_data, s2_rs2_data, wb_data;
    //reg [31:0] s2_dcache_dout;
    reg [31:0] s2_branch_target;

    // CSR (tohost) part, change later
    reg [31:0] csr_reg = 32'b0;
    assign csr = csr_reg;

    // FETCH → IF/ID
    always @(posedge clk) begin
        if (reset) begin
            s0_pc_reg   <= `PC_RESET;
            s1_pc_reg   <= 32'b0;
            PCsel <= 1'b0;
        end else if (PCsel) begin   
            s1_pc_reg   <= 32'b0;
            s0_pc_reg   <= alu_result;
        end else begin
            s0_pc_reg   <= s0_pc_reg + 32'd4;
            s1_pc_reg   <= s0_pc_reg;
        end
    end

    always @(posedge clk) begin
    if (reset) begin
        flushed <= 1'b0;
    end else begin
        flushed <= PCsel; // latch PCsel into 1-cycle flush
    end
    end

    wire [31:0] pc_plus_4 = s0_pc_reg + 32'd4; 
    assign icache_addr = s0_pc_reg;
    assign s1_inst_reg = flushed ? 32'h00000013 : icache_dout;

    assign icache_re = 1'b1;

///////////////////////////////////////////////////////

//STAGE 2: Instruction decode + execute (csr reg in stage 1)

    //implement regfile, decode instructions - including parsing for csrw
    //instruction decode
    
    wire [6:0] opcode = s1_inst_reg[6:0];
    wire [4:0] rd = s1_inst_reg[11:7];
    wire [2:0] funct3 = s1_inst_reg[14:12];
    wire [4:0] rs1 = s1_inst_reg[19:15];
    wire [4:0] rs2 = s1_inst_reg[24:20];
    wire [6:0] funct7 = s1_inst_reg[31:25];

// Regfile
    RegFile rf(
        .clk(clk),
        .we(s2_RegWrite && (s2_rd != 5'b0)),  // Control signal to write to registers
        .rs1_addr(rs1),        // rs1 field from instruction
        .rs2_addr(rs2),        // rs2 field
        .rd_addr(s2_rd),          // rd field
        .rd_data(wb_data),              // data from ALU or memory
        .rs1_data(rf_rs1_data),            // Output: value of rs1
        .rs2_data(rf_rs2_data)             // Output: value of rs2
    );

    wire forwardA = s2_RegWrite && (s2_rd == rs1) && (s2_rd != 5'd0);
    wire forwardB = s2_RegWrite && (s2_rd == rs2) && (s2_rd != 5'd0);

    always @(*) begin
        rs1_data = (forwardA ? wb_data : rf_rs1_data);
        rs2_data = (forwardB ? wb_data : rf_rs2_data);
    end
    
//immediate generator
    always @(*) begin
	    case (opcode)
            `OPC_ARI_ITYPE:  // i-type
                imm_out = {{20{s1_inst_reg[31]}}, s1_inst_reg[31:20]};
            `OPC_LOAD:  // loads
                imm_out = {{20{s1_inst_reg[31]}}, s1_inst_reg[31:20]};
            `OPC_CSR:  // csr
                imm_out = {{27{s1_inst_reg[19]}}, s1_inst_reg[19:15]};
            `OPC_STORE:  // s-type
                imm_out = {{20{s1_inst_reg[31]}}, s1_inst_reg[31:25], s1_inst_reg[11:7]};
            `OPC_BRANCH:  // b-type
                imm_out = {{19{s1_inst_reg[31]}}, s1_inst_reg[31], s1_inst_reg[7], s1_inst_reg[30:25], s1_inst_reg[11:8], 1'b0};
            `OPC_LUI:  // lui
                imm_out = {{s1_inst_reg[31:12]}, 12'b0};
            `OPC_AUIPC:  // auipc
                imm_out = {{s1_inst_reg[31:12]}, 12'b0};
            `OPC_JALR:  // j-type
                imm_out = {{20{s1_inst_reg[31]}}, s1_inst_reg[31:20]};
            `OPC_JAL:  // j-type
                imm_out = {{11{s1_inst_reg[31]}}, s1_inst_reg[31], s1_inst_reg[19:12], s1_inst_reg[20], s1_inst_reg[30:21], 1'b0};
        endcase
    end

//csr logic
    wire [11:0] csr_addr = s1_inst_reg[31:20];
    always @(posedge clk) begin // Write to CSR (csrw / csrwi)
        if ((opcode == 7'b1110011) && csr_addr == 12'h51E) begin // 12'h51E = 0x51E
            //$display("CSR WRITE @ %t | PC = %h | funct3 = %b | rs1 = %h | rs1_data = %h",
               //$time, s1_pc_reg, funct3, rs1, rs1_data);
            if (funct3 == 3'b101)  // csrwi
                csr_reg <= {27'b0, rs1};
            else if (funct3 == 3'b001)      // assume csrw
                csr_reg <= s2_alu_result;
        end
    end

//branch comparator
    always @(*) begin
        if (opcode == `OPC_BRANCH) begin
            case (funct3)
                3'b000: branch_taken = (rs1_data == rs2_data);  // BEQ
                3'b001: branch_taken = (rs1_data != rs2_data);  // BNE
                3'b100: branch_taken = ($signed(rs1_data) <  $signed(rs2_data));  // BLT (signed)
                3'b101: branch_taken = ($signed(rs1_data) >= $signed(rs2_data));  // BGE (signed)
                3'b110: branch_taken = (rs1_data <  rs2_data);   // BLTU (unsigned)
                3'b111: branch_taken = (rs1_data >= rs2_data);   // BGEU (unsigned)
                default: branch_taken = 1'b0;
            endcase
        end else begin
        branch_taken = 1'b0;
        end
    end

    wire jump_taken = 
    (opcode == `OPC_JAL) ||   // jal
    (opcode == `OPC_JALR)      //jalr
    ? 1'b1 
    : 1'b0;

    always @(*) begin
        PCsel = branch_taken || jump_taken;
    end

//control signals
    assign RegWrite =
    (opcode == `OPC_ARI_RTYPE) || // R-type (add, and, or, slt, etc.)
    (opcode == `OPC_ARI_ITYPE) || // I-type ALU (addi, slti, etc.)
    (opcode == `OPC_LOAD) || // loads (e.g., lw)
    (opcode == `OPC_JAL) || // jal
    (opcode == `OPC_JALR) || // jalr
    (opcode == `OPC_LUI) || // lui
    (opcode == `OPC_AUIPC) || // auipc
    (opcode == `OPC_CSR)     // csr instructions
    ? 1'b1
    : 1'b0; 

    assign WBsel =
    (opcode == `OPC_LOAD) ? 2'b00 :     // load (e.g., lw) → memory
    (opcode == `OPC_JAL) ||             // jal
    (opcode == `OPC_JALR) ? 2'b10 :     // jalr → PC+4
    2'b01;                               // everything else → ALU

    assign ASel =
    (opcode == `OPC_AUIPC)  ||
    (opcode == `OPC_JAL)    ||
    (opcode == `OPC_BRANCH) 
    ? 1'b1 
    : 1'b0;

    assign BSel =
       (opcode == `OPC_ARI_ITYPE)   || // I‑type ALU (addi, andi, ori, etc.)
       (opcode == `OPC_LOAD)        || // loads (for address calc)
       (opcode == `OPC_STORE)       || // stores (for address calc)
       (opcode == `OPC_BRANCH)      || // branches (to compute PC+offset)
       (opcode == `OPC_JAL)         || // JAL target = PC+offset
       (opcode == `OPC_JALR)        || // JALR target = rs1+offset
       (opcode == `OPC_AUIPC)       || // AUIPC = PC+offset
       (opcode == `OPC_LUI)        // LUI = immediate<<12
    ? 1'b1
    : 1'b0;

    assign A = ASel ? s1_pc_reg : rs1_data; 
    assign B = BSel ? imm_out : rs2_data; 

    // only use bit30 for R‑type SUB or I‑type SRAI
    wire do_sub_rtype  = (opcode == 7'b0110011)      // 0110011
                    && (funct3 == 3'b000)
                    && (funct7[5] == 1'b1);
 
    wire do_srai_itype = (opcode == 7'b0010011)  // 0010011
                    && (funct3 == 3'b101)
                    && (funct7[5] == 1'b1);

    wire do_sra_rtype  = (opcode  == 7'b0110011)
                    && (funct3   == 3'b101)       
                    && (funct7[5] == 1'b1);
 
    ALUdec alu_decoder (
    .opcode        (opcode),
    .funct         (funct3),
    .add_rshift_type(do_sub_rtype || do_srai_itype || do_sra_rtype),
    .ALUop         (ALUop)
    );
 
    ALU my_alu (
        .A(A),
        .B(B),
        .ALUop(ALUop),
        .Out(alu_result)
    );

//EX -> WB
always @(posedge clk) begin
  if (reset) begin
    s2_alu_result <= 32'b0;
    s2_pc_reg     <= 32'b0;
    s2_pc_plus_4  <= 32'b0;
    s2_rd         <= 5'd0;
    s2_RegWrite   <= 1'b0;
    s2_WBsel      <= 2'b01;
    s2_imm_out <= 32'b0;
    s2_PCSel <= 1'b0;
    s2_opcode      <= 7'b0;
    s2_funct3      <= 3'b0;
  end else if (!reset) begin
    s2_alu_result <= alu_result;    // from ALU
    s2_pc_reg     <= s1_pc_reg;
    s2_pc_plus_4  <= s1_pc_reg + 4; // or imm_e + PC_e+4 if you flopped PC
    s2_rd         <= rd;            // or rd_e if you flopped it
    s2_RegWrite   <= RegWrite;      // or RegWrite_e
    s2_WBsel      <= WBsel;         // or WBsel_e
    s2_imm_out    <= imm_out;
    s2_PCSel      <= PCsel;
    s2_branch_target <= s1_pc_reg + imm_out;
    s2_opcode <= opcode;
    s2_funct3 <= funct3;
  end
end

//STAGE 3: Memory / Writeback (access DMEM (load/store) and write back to RegFile)
    wire [1:0] off1 = alu_result[1:0];
    assign dcache_we = (opcode == `OPC_STORE) ? 
    (funct3 == 3'b000 ? (4'b0001 << off1) :        // SB
     funct3 == 3'b001 ? (4'b0011 << {off1[1], 1'b0}) : // SH
     funct3 == 3'b010 ? 4'b1111 : 4'b0000) : 4'b0000;   // SW

    assign dcache_addr = alu_result;
    assign dcache_re = (opcode == `OPC_LOAD);

    wire [1:0] off2 = s2_alu_result[1:0];
    reg [31:0] load_data;
    always @(*) begin
        case (s2_funct3)
        3'b000: // LB
        load_data = {{24{dcache_dout[8*off2+7]}},
                   dcache_dout[8*off2 +: 8]};
        3'b001: // LH
            load_data = {{16{dcache_dout[16*off2[1]+15]}},
                   dcache_dout[16*off2[1] +: 16]};
        3'b010: // LW
            load_data = dcache_dout;
        3'b100: // LBU
            load_data = {24'b0, dcache_dout[8*off2 +: 8]};
        3'b101: // LHU
            load_data = {16'b0, dcache_dout[16*off2[1] +: 16]};
        endcase
    end

    reg  [31:0] store_data;
    always @(*) begin
    case (funct3)
        3'b000: // SB
            store_data = rs2_data[7:0] << (off1 * 8);
        3'b001: // SH
            store_data = rs2_data[15:0] << (off1[1] * 16);
        3'b010: // SW: full word
            store_data = rs2_data;
        default: // SW
            store_data = rs2_data;
    endcase
    end
    assign dcache_din = store_data;

    always @(*) begin
        case (s2_WBsel)
            2'b00: wb_data = load_data;
            2'b01: wb_data = s2_alu_result;
            2'b10: wb_data = s2_pc_plus_4;
            default: wb_data = 32'b0;
        endcase
    end

// Assertions
    always @(posedge clk) begin
        // 1st assertion: upon reset, the program counter should become PC_RESET
        if (reset) assert(s0_pc_reg == `PC_RESET);

        // 2nd assertion: For store instructions, the write enable mask should have the appropriate number of ones depending on whether the instruction is sb, sh, or sw.
        if (opcode == `OPC_STORE) begin
            case (funct3)
                3'b000: assert(dcache_we == 4'b0001); // sb: write only the lowest byte
                3'b001: assert(dcache_we == 4'b0011); // sh: write the lowest 2 bytes
                3'b010: assert(dcache_we == 4'b1111); // sw: write all 4 bytes
            endcase
        end

        // 3rd assertion: For lb instructions, the upper 24 bits of data written to the regfile should be all 0s or 1s. 
        // For lh instructions, the upper 16 bits of data written to the regfile should be all 0s or 1s.
        if (opcode == `OPC_LOAD) begin
            case (funct3)
                3'b000: assert(&wb_data[31:8] == 1'b0 || &wb_data[31:8] == 1'b1); // uper 24 bits
                3'b001: assert(&wb_data[31:16] == 1'b0 || &wb_data[31:16] == 1'b1); // upper 16 bits
            endcase
        end
// disable any write to reg 0, 
        assert(rf.regs[0] == 0);
    end
endmodule

//REGFILE module
module RegFile(
    input logic clk,                 
    input logic we,                  
    input logic [4:0] rs1_addr,       
    input logic [4:0] rs2_addr,       
    input logic [4:0] rd_addr,        
    input logic [31:0] rd_data,       
    output logic [31:0] rs1_data,     
    output logic [31:0] rs2_data      
);
    logic [31:0] regs [31:0];

    assign rs1_data = (rs1_addr == 5'b0) ? 32'b0 : regs[rs1_addr];
    assign rs2_data = (rs2_addr == 5'b0) ? 32'b0 : regs[rs2_addr];

    always @(posedge clk) begin
        if (we && (rd_addr != 5'd0)) begin
            regs[rd_addr] <= rd_data;
        end
        regs[0] <= 0;
    end
endmodule