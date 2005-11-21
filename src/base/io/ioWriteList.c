/**CFile****************************************************************

  FileName    [ioWriteList.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write the graph structure of sequential AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioWriteList.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "io.h"
#include "seqInt.h"

/*
-------- Original Message --------
Subject: Re: abc release and retiming
Date:    Sun, 13 Nov 2005 20:31:18 -0500 (EST)
From:    Luca Carloni <luca@cs.columbia.edu>
To:      Alan Mishchenko <alanmi@eecs.berkeley.edu>

Alan,

My graph-representation file format is based on an adjacency list
representation and is indeed quite simple, in fact maybe too simple... I
used it in order to reason on relatively small weighed direct graphs. I
simply list all vertices, one per line and for each vertex "V_source" I
list all vertices that are "sinks" with respect to it, i.e. such that
there is a distinct arc between "V_source" and each of them (in
paranthesis I list the name of the edge and its weight (number of latency
on that path). For instance, if you look at the following graph, you have
that vertex "v_5" is connected to vertex "v_6" through a directed arc
called "v_5_to_v_6" whose latency is equal to 3, i.e. there are three
flip-flops on this arc. Still, notice that I sometime interpret the graph
also as the representation of a  LIS where each node corresponds to a
shell encapsulating a sequential core module (i.e. a module which does not
contain any combinational path between its inputs and its outputs). With
this representation an arc of latency 3 is interpreted as a wire where two
relay stations have been inserted in addition to the flip-flop terminating
the output of the core module.

Finally, notice that the name of the arc does not necessarily have to be
"v_5_to_v_6", but it could have been something like "arc_222" or "xyz" as
long as it is a unique name in the graph.

Thanks,
Luca

Example of graph representation
-----------------------------------------------------------------------------
v_5    >    v_6 ([v_5_to_v_6] = 3), v_12 ([v_5_to_v_12] = 2).
v_2    >    v_4 ([v_2_to_v_4] = 1), v_10_s0 ([v_2_to_v_10_s0] = 6), v_12 ([v_2_to_v_12] = 3).
v_9    >    v_10_s0 ([v_9_to_v_10_s0] = 5), v_12 ([v_9_to_v_12] = 2).
v_12    >    v_13 ([v_12_to_v_13] = 5).
v_13    >    v_14 ([v_13_to_v_14] = 1).
v_6    >    v_7 ([v_6_to_v_7] = 2).
v_4    >    v_5 ([v_4_to_v_5] = 2).
v_1    >    v_2 ([v_1_to_v_2] = 1).
v_7    >    v_8 ([v_7_to_v_8] = 2).
t    >    .
v_14    >    t ([v_14_to_t] = 1), v_5 ([v_14_to_v_5] = 1).
v_8    >    v_9 ([v_8_to_v_9] = 2).
s    >    v_1 ([s_to_v_1] = 1).
v_10_s0    >    v_10_s1 ([v_10_s0_to_v_10_s1] = 1).
v_10_s1    >    v_4 ([v_10_s1__v_4] = 1), v_8 ([v_10_s1__v_8] = 1).
-----------------------------------------------------------------------------
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Io_WriteListEdge( FILE * pFile, Abc_Obj_t * pObj );
static void Io_WriteListHost( FILE * pFile, Abc_Ntk_t * pNtk );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Writes the adjacency list for a sequential AIG.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteList( Abc_Ntk_t * pNtk, char * pFileName, int fUseHost )
{
    FILE * pFile;
    Abc_Obj_t * pObj;
    int i;

    assert( Abc_NtkIsSeq(pNtk)  );

    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Io_WriteList(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    fprintf( pFile, "# Adjacency list for sequential AIG \"%s\"\n", pNtk->pName );
    fprintf( pFile, "# written by ABC on %s\n", Extra_TimeStamp() );

    // write the constant node
    if ( Abc_ObjFanoutNum( Abc_NtkConst1(pNtk) ) > 0 )
        Io_WriteListEdge( pFile, Abc_NtkConst1(pNtk) );

    // write the PO edges
    Abc_NtkForEachCi( pNtk, pObj, i )
        Io_WriteListEdge( pFile, pObj );

    // write the internal nodes
    Abc_AigForEachAnd( pNtk, pObj, i )
        Io_WriteListEdge( pFile, pObj );

    // write the host node
    if ( fUseHost )
        Io_WriteListHost( pFile, pNtk );
    else
        Abc_NtkForEachCo( pNtk, pObj, i )
            Io_WriteListEdge( pFile, pObj );

    fprintf( pFile, "\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Writes the adjacency list for one edge in a sequential AIG.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteListEdge( FILE * pFile, Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i;
    fprintf( pFile, "%-10s >    ", Abc_ObjName(pObj) );
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        fprintf( pFile, " %s ([%s_to_%s] = %d)", Abc_ObjName(pFanout), Abc_ObjName(pObj), Abc_ObjName(pFanout), Seq_ObjFanoutL(pObj, pFanout) );
        if ( i == Abc_ObjFanoutNum(pObj) - 1 )
            fprintf( pFile, "." );
        else
            fprintf( pFile, "," );
    }
    fprintf( pFile, "\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the adjacency list for one edge in a sequential AIG.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Io_WriteListHost( FILE * pFile, Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i;

    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        fprintf( pFile, "%-10s >    ", Abc_ObjName(pObj) );
        fprintf( pFile, " %s ([%s_to_%s] = %d)", "HOST", Abc_ObjName(pObj), "HOST", 0 );
        if ( i == Abc_NtkPoNum(pNtk) - 1 )
            fprintf( pFile, "." );
        else
            fprintf( pFile, "," );
    }
    fprintf( pFile, "\n" );

    fprintf( pFile, "%-10s >    ", "HOST" );
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        fprintf( pFile, " %s ([%s_to_%s] = %d)", Abc_ObjName(pObj), "HOST", Abc_ObjName(pObj), 0 );
        if ( i == Abc_NtkPiNum(pNtk) - 1 )
            fprintf( pFile, "." );
        else
            fprintf( pFile, "," );
    }
    fprintf( pFile, "\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


