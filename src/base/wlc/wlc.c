/**CFile****************************************************************

  FileName    [wlc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Parses several flavors of word-level Verilog.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlc.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_GenerateCodeMax4( int nBits )
{
    int nWidth, nSteps, i;
    FILE * pFile = fopen( "max4.v", "wb" );
    if ( pFile == NULL )
        return;

    for ( nSteps = 0, nWidth = 1; nWidth < nBits; nWidth *= 3, nSteps++ );

    fprintf( pFile, "module max4 ( a, b, c, d, res, addr );\n\n" );
    fprintf( pFile, "  input [%d:0] a, b, c, d;\n", nBits-1 );
    fprintf( pFile, "  output [%d:0] res;\n", nBits-1 );
    fprintf( pFile, "  output [1:0] addr;\n\n" );

    fprintf( pFile, "  wire [%d:0] A = a;\n", nWidth-1 );
    fprintf( pFile, "  wire [%d:0] B = b;\n", nWidth-1 );
    fprintf( pFile, "  wire [%d:0] C = c;\n", nWidth-1 );
    fprintf( pFile, "  wire [%d:0] D = d;\n\n", nWidth-1 );

    fprintf( pFile, "  wire AB, AC, AD, BC, BD, CD;\n\n" );

    fprintf( pFile, "  comp( A, B, AB );\n" );
    fprintf( pFile, "  comp( A, C, AC );\n" );
    fprintf( pFile, "  comp( A, D, AD );\n" );
    fprintf( pFile, "  comp( B, C, BC );\n" );
    fprintf( pFile, "  comp( B, D, BD );\n" );
    fprintf( pFile, "  comp( C, D, CD );\n\n" );

    fprintf( pFile, "  assign addr = AB ?  (CD ? (AC ? 2\'b00 : 2\'b10) : (AD ? 2\'b00 : 2\'b11))  :  (CD ? (BC ? 2\'b01 : 2\'b10) : (BD ? 2\'b01 : 2\'b11));\n\n" );
    fprintf( pFile, "  assign res = addr[1] ? (addr[1] ? d : c) : (addr[0] ? b : a);\n\n" );
    fprintf( pFile, "endmodule\n\n\n" );


    fprintf( pFile, "module comp ( a, b, res );\n\n" );
    fprintf( pFile, "  input [%d:0] a, b;\n", nWidth-1 );
    fprintf( pFile, "  output res;\n" );
    fprintf( pFile, "  wire res2;\n\n" );

    fprintf( pFile, "  wire [%d:0] A =  a & ~b;\n", nWidth-1 );
    fprintf( pFile, "  wire [%d:0] B = ~a &  b;\n\n", nWidth-1 );

    fprintf( pFile, "  comp0( A, B, res, res2 );\n\n" );

    fprintf( pFile, "endmodule\n\n\n" );


    for ( i = 0; i < nSteps; i++ )
    {
        fprintf( pFile, "module comp%d ( a, b, yes, no );\n\n", i );
        fprintf( pFile, "  input [%d:0] a, b;\n", nWidth-1 );
        fprintf( pFile, "  output yes, no;\n\n", nWidth/3-1 );

        fprintf( pFile, "  wire [2:0] y, n;\n\n" );

        if ( i == nSteps - 1 )
        {
            fprintf( pFile, "  assign y = a;\n" );
            fprintf( pFile, "  assign n = b;\n\n" );
        }
        else
        {
            fprintf( pFile, "  wire [%d:0] A0 = a[%d:%d];\n", nWidth/3-1, nWidth/3-1, 0 );
            fprintf( pFile, "  wire [%d:0] A1 = a[%d:%d];\n", nWidth/3-1, 2*nWidth/3-1, nWidth/3 );
            fprintf( pFile, "  wire [%d:0] A2 = a[%d:%d];\n\n", nWidth/3-1, nWidth-1, 2*nWidth/3 );

            fprintf( pFile, "  wire [%d:0] B0 = b[%d:%d];\n", nWidth/3-1, nWidth/3-1, 0 );
            fprintf( pFile, "  wire [%d:0] B1 = b[%d:%d];\n", nWidth/3-1, 2*nWidth/3-1, nWidth/3 );
            fprintf( pFile, "  wire [%d:0] B2 = b[%d:%d];\n\n", nWidth/3-1, nWidth-1, 2*nWidth/3 );

            fprintf( pFile, "  comp%d( A0, B0, y[0], n[0] );\n", i+1 );
            fprintf( pFile, "  comp%d( A1, B1, y[1], n[1] );\n", i+1 );
            fprintf( pFile, "  comp%d( A2, B2, y[2], n[2] );\n\n", i+1 );
        }

        fprintf( pFile, "  assign yes = y[0] | (~y[0] & ~n[0] & y[1]) | (~y[0] & ~n[0] & ~y[1] & ~n[1] & y[2]);\n" );
        fprintf( pFile, "  assign no  = n[0] | (~y[0] & ~n[0] & n[1]) | (~y[0] & ~n[0] & ~y[1] & ~n[1] & n[2]);\n\n" );

        fprintf( pFile, "endmodule\n\n\n" );

        nWidth /= 3;
    }
    fclose( pFile );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

