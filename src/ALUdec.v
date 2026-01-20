// Module: ALUdecoder
// Desc:   Sets the ALU operation
// Inputs: opcode: the top 6 bits of the instruction
//         funct: the funct, in the case of r-type instructions
//         add_rshift_type: selects whether an ADD vs SUB, or an SRA vs SRL
// Outputs: ALUop: Selects the ALU's operation
//

`include "Opcode.vh"
`include "ALUop.vh"

module ALUdec(
  input [6:0]       opcode,
  input [2:0]       funct,
  input             add_rshift_type,
  output reg [3:0]  ALUop
);

  // Implement your ALU decoder here, then delete this comment
    always @(*) begin
        case (opcode)
            `OPC_ARI_RTYPE, `OPC_ARI_ITYPE: begin // Arithmetic instructions (R-type & I-type)
                case (funct)
                    3'b000: ALUop = (add_rshift_type) ? `ALU_SUB : `ALU_ADD; // ADD / SUB
                    3'b001: ALUop = `ALU_SLL; // SLL / SLLI
                    3'b010: ALUop = `ALU_SLT; // SLT / SLTI
                    3'b011: ALUop = `ALU_SLTU; // SLTU / SLTIU
                    3'b100: ALUop = `ALU_XOR; // XOR / XORI
                    3'b101: ALUop = (add_rshift_type) ? `ALU_SRA : `ALU_SRL; // SRL / SRA
                    3'b110: ALUop = `ALU_OR; // OR / ORI
                    3'b111: ALUop = `ALU_AND; // AND / ANDI
                   // default: ALUop = 4'b0000;
                endcase
            end

            `OPC_BRANCH: begin // Branch Instructions
                case (funct)
                 `FNC_BEQ:  ALUop = `ALU_ADD; // BEQ
           	 `FNC_BNE:  ALUop = `ALU_ADD; // BNE
           	 `FNC_BLT:  ALUop = `ALU_ADD; // BLT
           	 `FNC_BGE:  ALUop = `ALU_ADD; // BGE
           	 `FNC_BLTU: ALUop = `ALU_ADD; // BLTU
           	 `FNC_BGEU: ALUop = `ALU_ADD; // BGEU
                endcase
            end

            `OPC_LOAD, `OPC_STORE: begin // Memory Operations (Address Calculation)
                ALUop = `ALU_ADD; // Effective address = Base Register + Offset
            end

            `OPC_LUI: begin
                ALUop = `ALU_COPY_B; // LUI
            end

            default: begin
                ALUop = 4'b0000; // Default case (NOP)
            end
        endcase
    end


endmodule



