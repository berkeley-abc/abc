module fsm (out);
output out; 

wire [2:0] ns; 
wire [2:0] cs;

always @( ns or cs )
begin
case (cs)
    0 : ns = 3'b010;
    1 : ns = 3'b001;
    2 : ns = 3'b000;
    3 : ns = 3'b101;
    4 : ns = 3'b001;
    5 : ns = 3'b111;
    6 : ns = 3'b001;
    7 : ns = 3'b110;
endcase
end

assign out = cs == 3'b001; 

wire [2:0] const0 = 3'h0;


CPL_FF#3 ff3 ( .q(cs), .qbar(), .d(ns), .clk(), .arst(), .arstval(const0) );

endmodule
