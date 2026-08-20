module top ( y1, y2, a, b, c );
input a, b, c;
output y1, y2;
wire g1, g2, g3;
wire t_0;

and ( g1, a, b );
xor ( g2, a, c );
nor ( g3, b, c );
and ( y1, g1, g2 );
or  ( y2, t_0, g3 );

endmodule
