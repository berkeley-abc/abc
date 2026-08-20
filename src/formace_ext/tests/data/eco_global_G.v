module top ( y0, y1, y2, a, b, c );
input a, b, c;
output y0, y1, y2;
wire g0;

xor ( g0, a, b );
buf ( y0, g0 );
buf ( y1, g0 );
or  ( y2, g0, c );

endmodule
