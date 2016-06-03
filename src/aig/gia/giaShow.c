/**CFile****************************************************************

  FileName    [giaShow.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [AIG visualization.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: giaShow.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "proof/cec/cec.h"
#include "proof/acec/acec.h"

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
/*
Vec_Int_t * Gia_WriteDotAigMarks( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vHadds )
{
    int i;
    Vec_Int_t * vMarks = Vec_IntStart( Gia_ManObjNum(p) );
    for ( i = 0; i < Vec_IntSize(vHadds)/2; i++ )
    {
        Vec_IntWriteEntry( vMarks, Vec_IntEntry(vHadds, 2*i+0), Abc_Var2Lit(i+1, 0) );
        Vec_IntWriteEntry( vMarks, Vec_IntEntry(vHadds, 2*i+1), Abc_Var2Lit(i+1, 0) );
    }
    for ( i = 0; i < Vec_IntSize(vFadds)/5; i++ )
    {
        Vec_IntWriteEntry( vMarks, Vec_IntEntry(vFadds, 5*i+3), Abc_Var2Lit(i+1, 1) );
        Vec_IntWriteEntry( vMarks, Vec_IntEntry(vFadds, 5*i+4), Abc_Var2Lit(i+1, 1) );
    }
    return vMarks;
}
int Gia_WriteDotAigLevel_rec( Gia_Man_t * p, Vec_Int_t * vMarks, Vec_Int_t * vFadds, Vec_Int_t * vHadds, int Id, Vec_Int_t * vLevel )
{
    int Level = Vec_IntEntry(vLevel, Id), Mark = Vec_IntEntry(vMarks, Id);
    if ( Level || Mark == -1 )
        return Level;
    if ( Mark == 0 )
    {
        Gia_Obj_t * pObj = Gia_ManObj( p, Id );
        int Level0 = Gia_WriteDotAigLevel_rec( p, vMarks, vFadds, vHadds, Gia_ObjFaninId0(pObj, Id), vLevel );
        int Level1 = Gia_WriteDotAigLevel_rec( p, vMarks, vFadds, vHadds, Gia_ObjFaninId1(pObj, Id), vLevel );
        Level = Abc_MaxInt(Level0, Level1) + 1;
        Vec_IntWriteEntry( vLevel, Id, Level );
        Vec_IntWriteEntry( vMarks, Id, -1 );
    }
    else if ( Abc_LitIsCompl(Mark) ) // FA
    {
        int i, * pFanins = Vec_IntEntryP( vFadds, 5*(Abc_Lit2Var(Mark)-1) );
        assert( pFanins[3] == Id || pFanins[4] == Id );
        for ( i = 0; i < 3; i++ )
            Level = Abc_MaxInt( Level, Gia_WriteDotAigLevel_rec( p, vMarks, vFadds, vHadds, pFanins[i], vLevel ) );
        Vec_IntWriteEntry( vLevel, pFanins[3], Level+1 );
        Vec_IntWriteEntry( vLevel, pFanins[4], Level+1 );
    }
    else  // HA
    {
        int * pFanins = Vec_IntEntryP( vHadds, 2*(Abc_Lit2Var(Mark)-1) );
        Gia_Obj_t * pObj = Gia_ManObj( p, pFanins[1] );
        int Level0 = Gia_WriteDotAigLevel_rec( p, vMarks, vFadds, vHadds, Gia_ObjFaninId0(pObj, Id), vLevel );
        int Level1 = Gia_WriteDotAigLevel_rec( p, vMarks, vFadds, vHadds, Gia_ObjFaninId1(pObj, Id), vLevel );
        assert( pFanins[0] == Id || pFanins[1] == Id );
        Level = Abc_MaxInt(Level0, Level1) + 1;
        Vec_IntWriteEntry( vLevel, pFanins[0], Level );
        Vec_IntWriteEntry( vLevel, pFanins[1], Level );
    }
    return Level;
}
int Gia_WriteDotAigLevel( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vHadds, Vec_Int_t ** pvMarks, Vec_Int_t ** pvLevel )
{
    Vec_Int_t * vMarks = Gia_WriteDotAigMarks( p, vFadds, vHadds );
    Vec_Int_t * vLevel = Vec_IntStart( Gia_ManObjNum(p) );
    int i, Id, Level = 0;
    Vec_IntWriteEntry( vMarks, 0, -1 );
    Gia_ManForEachCiId( p, Id, i )
        Vec_IntWriteEntry( vMarks, Id, -1 );
    Gia_ManForEachCoDriverId( p, Id, i )
        Level = Abc_MaxInt( Level, Gia_WriteDotAigLevel_rec(p, vMarks, vFadds, vHadds, Id, vLevel) );
    Gia_ManForEachCoId( p, Id, i )
        Vec_IntWriteEntry( vMarks, Id, -1 );
    *pvMarks = vMarks;
    *pvLevel = vLevel;
    return Level;
}
*/
int Gia_WriteDotAigLevel( Gia_Man_t * p, Vec_Int_t * vFadds, Vec_Int_t * vHadds, Vec_Int_t * vRecord, Vec_Int_t ** pvLevel, Vec_Int_t ** pvMarks, Vec_Int_t ** pvRemap )
{
    Vec_Int_t * vLevel = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_Int_t * vMarks = Vec_IntStart( Gia_ManObjNum(p) );
    Vec_Int_t * vRemap = Vec_IntStartNatural( Gia_ManObjNum(p) );
    int i, k, Id, Entry, LevelMax = 0;

    Vec_IntWriteEntry( vMarks, 0, -1 );
    Gia_ManForEachCiId( p, Id, i )
        Vec_IntWriteEntry( vMarks, Id, -1 );
    Gia_ManForEachCoId( p, Id, i )
        Vec_IntWriteEntry( vMarks, Id, -1 );

    Vec_IntForEachEntry( vRecord, Entry, i )
    {
        int Level = 0;
        int Node = Abc_Lit2Var2(Entry);
        int Attr = Abc_Lit2Att2(Entry);
        if ( Attr == 2 )
        {
            int * pFanins = Vec_IntEntryP( vFadds, 5*Node );
            for ( k = 0; k < 3; k++ )
                Level = Abc_MaxInt( Level, Vec_IntEntry(vLevel, pFanins[k]) );
            Vec_IntWriteEntry( vLevel, pFanins[3], Level+1 );
            Vec_IntWriteEntry( vLevel, pFanins[4], Level+1 );
            Vec_IntWriteEntry( vMarks, pFanins[4], Entry );
            Vec_IntWriteEntry( vRemap, pFanins[3], pFanins[4] );
            //printf( "Making FA output %d.\n", pFanins[4] );
        }
        else if ( Attr == 1 )
        {
            int * pFanins = Vec_IntEntryP( vHadds, 2*Node );
            Gia_Obj_t * pObj = Gia_ManObj( p, pFanins[1] );
            int pFaninsIn[2] = { Gia_ObjFaninId0(pObj, pFanins[1]), Gia_ObjFaninId1(pObj, pFanins[1]) };
            for ( k = 0; k < 2; k++ )
                Level = Abc_MaxInt( Level, Vec_IntEntry(vLevel, pFaninsIn[k]) );
            Vec_IntWriteEntry( vLevel, pFanins[0], Level+1 );
            Vec_IntWriteEntry( vLevel, pFanins[1], Level+1 );
            Vec_IntWriteEntry( vMarks, pFanins[1], Entry );
            Vec_IntWriteEntry( vRemap, pFanins[0], pFanins[1] );
            //printf( "Making HA output %d.\n", pFanins[1] );
        }
        else // if ( Attr == 3 || Attr == 0 )
        {
            Gia_Obj_t * pObj = Gia_ManObj( p, Node );
            int pFaninsIn[2] = { Gia_ObjFaninId0(pObj, Node), Gia_ObjFaninId1(pObj, Node) };
            for ( k = 0; k < 2; k++ )
                Level = Abc_MaxInt( Level, Vec_IntEntry(vLevel, pFaninsIn[k]) );
            Vec_IntWriteEntry( vLevel, Node, Level+1 );
            Vec_IntWriteEntry( vMarks, Node, -1 );
            //printf( "Making node %d.\n", Node );
        }
        LevelMax = Abc_MaxInt( LevelMax, Level+1 );
    }
    *pvLevel = vLevel;
    *pvMarks = vMarks;
    *pvRemap = vRemap;
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    [Writes the graph structure of AIG for DOT.]

  Description [Useful for graph visualization using tools such as GraphViz: 
  http://www.graphviz.org/]
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_WriteDotAig( Gia_Man_t * pMan, char * pFileName, Vec_Int_t * vBold, int fAdders )
{
    Vec_Int_t * vFadds = NULL, * vHadds = NULL, * vRecord = NULL, * vMarks = NULL, * vRemap = NULL;
    FILE * pFile;
    Gia_Obj_t * pNode;//, * pTemp, * pPrev;
    int LevelMax, Prev, Level, i;
    int fConstIsUsed = 0;

    if ( Gia_ManAndNum(pMan) > 1000 )
    {
        fprintf( stdout, "Cannot visualize AIG with more than 1000 nodes.\n" );
        return;
    }
    if ( (pFile = fopen( pFileName, "w" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", pFileName );
        return;
    }

    // mark the nodes
    if ( vBold )
        Gia_ManForEachObjVec( vBold, pMan, pNode, i )
            pNode->fMark0 = 1;
    else if ( pMan->nXors || pMan->nMuxes )
        Gia_ManForEachObj( pMan, pNode, i )
            if ( Gia_ObjIsXor(pNode) || Gia_ObjIsMux(pMan, pNode) )
                pNode->fMark0 = 1;

    // compute levels
    if ( fAdders )
    {
        Vec_IntFreeP( &pMan->vLevels );
        vFadds   = Gia_ManDetectFullAdders( pMan, 0 );
        vHadds   = Gia_ManDetectHalfAdders( pMan, 0 );
        vRecord  = Gia_PolynFindOrder( pMan, vFadds, vHadds, 0, 0 );
        LevelMax = 1 + Gia_WriteDotAigLevel( pMan, vFadds, vHadds, vRecord, &pMan->vLevels, &vMarks, &vRemap );
    }
    else
        LevelMax = 1 + Gia_ManLevelNum( pMan );

    // set output levels
    Gia_ManForEachCo( pMan, pNode, i )
        Vec_IntWriteEntry( pMan->vLevels, Gia_ObjId(pMan, pNode), LevelMax );

    // write the DOT header
    fprintf( pFile, "# %s\n",  "AIG structure generated by IVY package" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "digraph AIG {\n" );
    fprintf( pFile, "size = \"7.5,10\";\n" );
//  fprintf( pFile, "ranksep = 0.5;\n" );
//  fprintf( pFile, "nodesep = 0.5;\n" );
    fprintf( pFile, "center = true;\n" );
//  fprintf( pFile, "orientation = landscape;\n" );
//  fprintf( pFile, "edge [fontsize = 10];\n" );
//  fprintf( pFile, "edge [dir = none];\n" );
    fprintf( pFile, "edge [dir = back];\n" );
    fprintf( pFile, "\n" );

    // labels on the left of the picture
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  node [shape = plaintext];\n" );
    fprintf( pFile, "  edge [style = invis];\n" );
    fprintf( pFile, "  LevelTitle1 [label=\"\"];\n" );
    fprintf( pFile, "  LevelTitle2 [label=\"\"];\n" );
    // generate node names with labels
    for ( Level = LevelMax; Level >= 0; Level-- )
    {
        // the visible node name
        fprintf( pFile, "  Level%d", Level );
        fprintf( pFile, " [label = " );
        // label name
        fprintf( pFile, "\"" );
        fprintf( pFile, "\"" );
        fprintf( pFile, "];\n" );
    }

    // genetate the sequence of visible/invisible nodes to mark levels
    fprintf( pFile, "  LevelTitle1 ->  LevelTitle2 ->" );
    for ( Level = LevelMax; Level >= 0; Level-- )
    {
        // the visible node name
        fprintf( pFile, "  Level%d",  Level );
        // the connector
        if ( Level != 0 )
            fprintf( pFile, " ->" );
        else
            fprintf( pFile, ";" );
    }
    fprintf( pFile, "\n" );
    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );

    // generate title box on top
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  rank = same;\n" );
    fprintf( pFile, "  LevelTitle1;\n" );
    fprintf( pFile, "  title1 [shape=plaintext,\n" );
    fprintf( pFile, "          fontsize=20,\n" );
    fprintf( pFile, "          fontname = \"Times-Roman\",\n" );
    fprintf( pFile, "          label=\"" );
    fprintf( pFile, "%s", "AIG structure visualized by ABC" );
    fprintf( pFile, "\\n" );
    fprintf( pFile, "Benchmark \\\"%s\\\". ", "aig" );
//    fprintf( pFile, "Time was %s. ",  Extra_TimeStamp() );
    fprintf( pFile, "\"\n" );
    fprintf( pFile, "         ];\n" );
    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );

    // generate statistics box
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  rank = same;\n" );
    fprintf( pFile, "  LevelTitle2;\n" );
    fprintf( pFile, "  title2 [shape=plaintext,\n" );
    fprintf( pFile, "          fontsize=18,\n" );
    fprintf( pFile, "          fontname = \"Times-Roman\",\n" );
    fprintf( pFile, "          label=\"" );
    fprintf( pFile, "The set contains %d logic nodes and spans %d levels.", Gia_ManAndNum(pMan), LevelMax );
    fprintf( pFile, "\\n" );
    fprintf( pFile, "\"\n" );
    fprintf( pFile, "         ];\n" );
    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );

    // generate the COs
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  rank = same;\n" );
    // the labeling node of this level
    fprintf( pFile, "  Level%d;\n",  LevelMax );
    // generate the CO nodes
    Gia_ManForEachCo( pMan, pNode, i )
    {
        if ( Gia_ObjFaninId0p(pMan, pNode) == 0 )
            fConstIsUsed = 1;
/*
        if ( fHaig || pNode->pEquiv == NULL )
            fprintf( pFile, "  Node%d%s [label = \"%d%s\"", pNode->Id, 
                (Gia_ObjIsLatch(pNode)? "_in":""), pNode->Id, (Gia_ObjIsLatch(pNode)? "_in":"") );
        else
            fprintf( pFile, "  Node%d%s [label = \"%d%s(%d%s)\"", pNode->Id, 
                (Gia_ObjIsLatch(pNode)? "_in":""), pNode->Id, (Gia_ObjIsLatch(pNode)? "_in":""), 
                    Gia_Regular(pNode->pEquiv)->Id, Gia_IsComplement(pNode->pEquiv)? "\'":"" );
*/
        fprintf( pFile, "  Node%d [label = \"%d\"", Gia_ObjId(pMan, pNode), Gia_ObjId(pMan, pNode) ); 

        fprintf( pFile, ", shape = %s", "invtriangle" );
        fprintf( pFile, ", color = coral, fillcolor = coral" );
        fprintf( pFile, "];\n" );
    }
    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );

    // generate nodes of each rank
    for ( Level = LevelMax - 1; Level > 0; Level-- )
    {
        fprintf( pFile, "{\n" );
        fprintf( pFile, "  rank = same;\n" );
        // the labeling node of this level
        fprintf( pFile, "  Level%d;\n",  Level );
        Gia_ManForEachObj( pMan, pNode, i )
        {
            if ( vMarks && Vec_IntEntry(vMarks, i) == 0 )
                continue;
            if ( (int)Gia_ObjLevel(pMan, pNode) != Level )
                continue;
/*
            if ( fHaig || pNode->pEquiv == NULL )
                fprintf( pFile, "  Node%d [label = \"%d\"", pNode->Id, pNode->Id );
            else 
                fprintf( pFile, "  Node%d [label = \"%d(%d%s)\"", pNode->Id, pNode->Id, 
                    Gia_Regular(pNode->pEquiv)->Id, Gia_IsComplement(pNode->pEquiv)? "\'":"" );
*/
            if ( vMarks && Vec_IntEntry(vMarks, i) > 0 )
            {
                fprintf( pFile, "  Node%d [label = \"%d_%d\"", i, Vec_IntFind(vRemap, i), i ); 
                if ( Abc_Lit2Att2(Vec_IntEntry(vMarks, i)) == 2 )
                    fprintf( pFile, ", shape = doubleoctagon" );
                else 
                    fprintf( pFile, ", shape = octagon" );
            }
            else if ( Gia_ObjIsXor(pNode) )
            {
                fprintf( pFile, "  Node%d [label = \"%d\"", i, i ); 
                fprintf( pFile, ", shape = doublecircle" );
            }
            else if ( Gia_ObjIsMux(pMan, pNode) )
            {
                fprintf( pFile, "  Node%d [label = \"%d\"", i, i ); 
                fprintf( pFile, ", shape = trapezium" );
            }
            else
            {
                fprintf( pFile, "  Node%d [label = \"%d\"", i, i ); 
                fprintf( pFile, ", shape = ellipse" );
            }

            if ( pNode->fMark0 )
                fprintf( pFile, ", style = filled" );
            fprintf( pFile, "];\n" );
        }
        fprintf( pFile, "}" );
        fprintf( pFile, "\n" );
        fprintf( pFile, "\n" );
    }

    // generate the CI nodes
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  rank = same;\n" );
    // the labeling node of this level
    fprintf( pFile, "  Level%d;\n",  0 );
    // generate constant node
    if ( fConstIsUsed || pMan->fGiaSimple )
    {
        // check if the costant node is present
        fprintf( pFile, "  Node%d [label = \"Const0\"", 0 );
        fprintf( pFile, ", shape = ellipse" );
        fprintf( pFile, ", color = coral, fillcolor = coral" );
        fprintf( pFile, "];\n" );
    }
    // generate the CI nodes
    Gia_ManForEachCi( pMan, pNode, i )
    {
/*
        if ( fHaig || pNode->pEquiv == NULL )
            fprintf( pFile, "  Node%d%s [label = \"%d%s\"", pNode->Id, 
                (Gia_ObjIsLatch(pNode)? "_out":""), pNode->Id, (Gia_ObjIsLatch(pNode)? "_out":"") );
        else
            fprintf( pFile, "  Node%d%s [label = \"%d%s(%d%s)\"", pNode->Id, 
                (Gia_ObjIsLatch(pNode)? "_out":""), pNode->Id, (Gia_ObjIsLatch(pNode)? "_out":""), 
                    Gia_Regular(pNode->pEquiv)->Id, Gia_IsComplement(pNode->pEquiv)? "\'":"" );
*/
        fprintf( pFile, "  Node%d [label = \"%d\"", Gia_ObjId(pMan, pNode), Gia_ObjId(pMan, pNode) ); 

        fprintf( pFile, ", shape = %s", "triangle" );
        fprintf( pFile, ", color = coral, fillcolor = coral" );
        fprintf( pFile, "];\n" );
    }
    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );

    // generate invisible edges from the square down
    fprintf( pFile, "title1 -> title2 [style = invis];\n" );
    Gia_ManForEachCo( pMan, pNode, i )
        fprintf( pFile, "title2 -> Node%d [style = invis];\n", Gia_ObjId(pMan, pNode) );
    // generate invisible edges among the COs
    Prev = -1;
    Gia_ManForEachCo( pMan, pNode, i )
    {
        if ( i > 0 )
            fprintf( pFile, "Node%d -> Node%d [style = invis];\n", Prev, Gia_ObjId(pMan, pNode) );
        Prev = Gia_ObjId(pMan, pNode);
    }

    // generate edges
    Gia_ManForEachObj( pMan, pNode, i )
    {
        if ( !Gia_ObjIsAnd(pNode) && !Gia_ObjIsCo(pNode) && !Gia_ObjIsBuf(pNode) )
            continue;
        if ( vMarks && Vec_IntEntry(vMarks, i) == 0 )
            continue;
        // consider half/full-adder
        if ( vMarks && Vec_IntEntry(vMarks, i) > 0 )
        {
            int k, Mark = Vec_IntEntry(vMarks, i);
            if ( Abc_Lit2Att2(Mark) == 2 ) // FA
            {
                int * pFanins = Vec_IntEntryP( vFadds, 5*Abc_Lit2Var2(Mark) );
                if ( pFanins[3] == i )
                    continue;
                assert( pFanins[4] == i );
                // generate the edge from this node to the next
                for ( k = 0; k < 3; k++ )
                {
                    fprintf( pFile, "Node%d",  i );
                    fprintf( pFile, " -> " );
                    fprintf( pFile, "Node%d",  Vec_IntEntry(vRemap, pFanins[k]) );
                    fprintf( pFile, " [" );
                    fprintf( pFile, "style = %s", "bold" );
                    fprintf( pFile, "]" );
                    fprintf( pFile, ";\n" );
                }
            }
            else  // HA
            {
                int * pFanins = Vec_IntEntryP( vHadds, 2*Abc_Lit2Var2(Mark) );
                int pFaninsIn[2] = { Vec_IntEntry(vRemap, Gia_ObjFaninId0(pNode, i)), Vec_IntEntry(vRemap, Gia_ObjFaninId1(pNode, i)) };
                if ( pFanins[0] == i )
                    continue;
                assert( pFanins[1] == i );
                for ( k = 0; k < 2; k++ )
                {
                    fprintf( pFile, "Node%d",  i );
                    fprintf( pFile, " -> " );
                    fprintf( pFile, "Node%d",  Vec_IntEntry(vRemap, pFaninsIn[k]) );
                    fprintf( pFile, " [" );
                    fprintf( pFile, "style = %s", "bold" );
                    fprintf( pFile, "]" );
                    fprintf( pFile, ";\n" );
                }
            }
            continue;
        }
        // generate the edge from this node to the next
        fprintf( pFile, "Node%d",  i );
        fprintf( pFile, " -> " );
        fprintf( pFile, "Node%d",  vRemap ? Vec_IntEntry(vRemap, Gia_ObjFaninId0(pNode, i)) : Gia_ObjFaninId0(pNode, i) );
        fprintf( pFile, " [" );
        fprintf( pFile, "style = %s", Gia_ObjFaninC0(pNode)? "dotted" : "bold" );
//        if ( Gia_NtkIsSeq(pNode->pMan) && Seq_ObjFaninL0(pNode) > 0 )
//        fprintf( pFile, ", label = \"%s\"", Seq_ObjFaninGetInitPrintable(pNode,0) );
        fprintf( pFile, "]" );
        fprintf( pFile, ";\n" );
        if ( !Gia_ObjIsAnd(pNode) )
            continue;
        // generate the edge from this node to the next
        fprintf( pFile, "Node%d",  i );
        fprintf( pFile, " -> " );
        fprintf( pFile, "Node%d",  vRemap ? Vec_IntEntry(vRemap, Gia_ObjFaninId1(pNode, i)) : Gia_ObjFaninId1(pNode, i) );
        fprintf( pFile, " [" );
        fprintf( pFile, "style = %s", Gia_ObjFaninC1(pNode)? "dotted" : "bold" );
//        if ( Gia_NtkIsSeq(pNode->pMan) && Seq_ObjFaninL1(pNode) > 0 )
//        fprintf( pFile, ", label = \"%s\"", Seq_ObjFaninGetInitPrintable(pNode,1) );
        fprintf( pFile, "]" );
        fprintf( pFile, ";\n" );

        if ( !Gia_ObjIsMux(pMan, pNode) )
            continue;
        // generate the edge from this node to the next
        fprintf( pFile, "Node%d",  i );
        fprintf( pFile, " -> " );
        fprintf( pFile, "Node%d",  vRemap ? Vec_IntEntry(vRemap, Gia_ObjFaninId2(pMan, i)) : Gia_ObjFaninId2(pMan, i) );
        fprintf( pFile, " [" );
        fprintf( pFile, "style = %s", Gia_ObjFaninC2(pMan, pNode)? "dotted" : "bold" );
//        if ( Gia_NtkIsSeq(pNode->pMan) && Seq_ObjFaninL1(pNode) > 0 )
//        fprintf( pFile, ", label = \"%s\"", Seq_ObjFaninGetInitPrintable(pNode,1) );
        fprintf( pFile, "]" );
        fprintf( pFile, ";\n" );

/*
        // generate the edges between the equivalent nodes
        if ( fHaig && pNode->pEquiv && Gia_ObjRefs(pNode) > 0 )
        {
            pPrev = pNode;
            for ( pTemp = pNode->pEquiv; pTemp != pNode; pTemp = Gia_Regular(pTemp->pEquiv) )
            {
                fprintf( pFile, "Node%d",  pPrev->Id );
                fprintf( pFile, " -> " );
                fprintf( pFile, "Node%d",  pTemp->Id );
                fprintf( pFile, " [style = %s]", Gia_IsComplement(pTemp->pEquiv)? "dotted" : "bold" );
                fprintf( pFile, ";\n" );
                pPrev = pTemp;
            }
            // connect the last node with the first
            fprintf( pFile, "Node%d",  pPrev->Id );
            fprintf( pFile, " -> " );
            fprintf( pFile, "Node%d",  pNode->Id );
            fprintf( pFile, " [style = %s]", Gia_IsComplement(pPrev->pEquiv)? "dotted" : "bold" );
            fprintf( pFile, ";\n" );
        }
*/
    }

    fprintf( pFile, "}" );
    fprintf( pFile, "\n" );
    fprintf( pFile, "\n" );
    fclose( pFile );

    // unmark nodes
    if ( vBold )
        Gia_ManForEachObjVec( vBold, pMan, pNode, i )
            pNode->fMark0 = 0;
    else if ( pMan->nXors || pMan->nMuxes )
        Gia_ManCleanMark0( pMan );

    Vec_IntFreeP( &vFadds );
    Vec_IntFreeP( &vHadds );
    Vec_IntFreeP( &vRecord );

    Vec_IntFreeP( &pMan->vLevels );
    Vec_IntFreeP( &vMarks );
    Vec_IntFreeP( &vRemap );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManShow( Gia_Man_t * pMan, Vec_Int_t * vBold, int fAdders )
{
    extern void Abc_ShowFile( char * FileNameDot );
    static int Counter = 0;
    char FileNameDot[200];
    FILE * pFile;
    // create the file name
//    Gia_ShowGetFileName( pMan->pName, FileNameDot );
    sprintf( FileNameDot, "temp%02d.dot", Counter++ );
    // check that the file can be opened
    if ( (pFile = fopen( FileNameDot, "w" )) == NULL )
    {
        fprintf( stdout, "Cannot open the intermediate file \"%s\".\n", FileNameDot );
        return;
    }
    fclose( pFile );
    // generate the file
    Gia_WriteDotAig( pMan, FileNameDot, vBold, fAdders );
    // visualize the file 
    Abc_ShowFile( FileNameDot );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

