// Module: ALU.v
// Desc:   32-bit ALU for the RISC-V Processor
// Inputs: 
//    A: 32-bit value
//    B: 32-bit value
//    ALUop: Selects the ALU's operation 
// 						
// Outputs:
//    Out: The chosen function mapped to A and B.

`include "Opcode.vh"
`include "ALUop.vh"

module ALU(
    input [31:0] A,B,
    input [3:0] ALUop,
    output reg [31:0] Out
);

    // Implement your ALU here, then delete this comment
    always @(*) begin
        case (ALUop)
            `ALU_ADD:  Out = A + B;  // ADD / ADDI
            `ALU_SUB:  Out = A - B;  // SUB
            `ALU_AND:  Out = A & B;  // AND / ANDI
            `ALU_OR:   Out = A | B;  // OR / ORI
            `ALU_XOR:  Out = A ^ B;  // XOR / XORI
            `ALU_SLT:  Out = ($signed(A) < $signed(B)) ? 32'b1 : 32'b0; // SLT / SLTI
            `ALU_SLTU: Out = (A < B) ? 32'b1 : 32'b0; // SLTU / SLTIU
	        `ALU_SLL:  Out = A << B[4:0]; // SLL / SLLI
	        `ALU_SRA:  Out = $signed(A) >>> B[4:0]; // SRA / SRAI
	        `ALU_SRL:  Out = A >> B[4:0]; // SRL / SRLI
            `ALU_COPY_B: Out = B; // LUI
	        `ALU_XXX: Out = 32'b0; //default
        endcase
        // Zero Flag for Branch Instructions (BEQ, BNE, etc.)
        // ZeroFlag = (Out == 32'b0) ? 1'b1 : 1'b0;
    end
endmodule
