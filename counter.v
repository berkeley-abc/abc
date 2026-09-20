
module adder (
    input  [3:0] a,
    input  [3:0] b,
    output [3:0] sum,
    output       carry
);

    assign {carry, sum} = a + b;

endmodule

module counter (
    input        clock,
    input        reset,
    input        enable,
    output [3:0] count,
    output       carry
);

    reg  [3:0] state;
    wire [3:0] next;

    adder increment (
        .a     (state),
        .b     (4'b0001),
        .sum   (next),
        .carry (carry)
    );

    always @(posedge clock) begin
        if (reset)
            state <= 4'b0000;
        else if (enable)
            state <= next;
    end

    assign count = state;

endmodule
