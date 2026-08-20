module top ( y0, y1, y2, a, b, c );
input a, b, c;
output y0, y1, y2;
wire t_0, t_1;

buf ( y0, t_0 );
buf ( y1, t_1 );
or  ( y2, t_0, c );

endmodule
