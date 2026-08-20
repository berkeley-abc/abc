module top ( y1, y2, a, b, c );
input a, b, c;
output y1, y2;
wire g1, g2, g3, g4;

not ( g1, c );
and ( g2, a, g1 );
nor ( g3, a, b );
and ( g4, b, c );
and ( y1, b, g2 );
or  ( y2, g2, g3, g4 );

endmodule
