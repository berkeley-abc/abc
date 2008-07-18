/**CFile****************************************************************

  FileName    [ntlWriteBlif.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to write BLIF files.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlWriteBlif.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

// The code in this file is developed in collaboration with Mark Jarvin of Toronto.

#include "ntl.h"
#include "ioa.h"

#include <stdarg.h>
#include "bzlib.h"
#include "zlib.h"

#ifdef _WIN32
#define vsnprintf _vsnprintf
#endif

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Writes one model into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifModel( FILE * pFile, Ntl_Mod_t * pModel, int fMain )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    float Delay;
    int i, k;
    fprintf( pFile, ".model %s\n", pModel->pName );
    if ( pModel->attrWhite || pModel->attrBox || pModel->attrComb || pModel->attrKeep )
    {
        fprintf( pFile, ".attrib" );
        fprintf( pFile, " %s", pModel->attrWhite? "white": "black" );
        fprintf( pFile, " %s", pModel->attrBox?   "box"  : "logic" );
        fprintf( pFile, " %s", pModel->attrComb?  "comb" : "seq"   );
//        fprintf( pFile, " %s", pModel->attrKeep?  "keep" : "sweep" );
        fprintf( pFile, "\n" );
    }
    if ( pModel->attrNoMerge )
        fprintf( pFile, ".no_merge\n" );
    fprintf( pFile, ".inputs" );
    Ntl_ModelForEachPi( pModel, pObj, i )
        fprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    Ntl_ModelForEachPo( pModel, pObj, i )
        fprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
    fprintf( pFile, "\n" );
    // write delays
    if ( pModel->vDelays )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vDelays); i += 3 )
        {
            fprintf( pFile, ".delay" );
            if ( Vec_IntEntry(pModel->vDelays,i) != -1 )
                fprintf( pFile, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vDelays,i)))->pName );
            if ( Vec_IntEntry(pModel->vDelays,i+1) != -1 )
                fprintf( pFile, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vDelays,i+1)))->pName );
            fprintf( pFile, " %.3f", Aig_Int2Float(Vec_IntEntry(pModel->vDelays,i+2)) );
            fprintf( pFile, "\n" );
        }
    }
    if ( pModel->vTimeInputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeInputs); i += 2 )
        {
            if ( fMain )
                fprintf( pFile, ".input_arrival" );
            else
                fprintf( pFile, ".input_required" );
            if ( Vec_IntEntry(pModel->vTimeInputs,i) != -1 )
                fprintf( pFile, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vTimeInputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeInputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                fprintf( pFile, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                fprintf( pFile, " inf" );
            else
                fprintf( pFile, " %.3f", Delay );
            fprintf( pFile, "\n" );
        }
    }
    if ( pModel->vTimeOutputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeOutputs); i += 2 )
        {
            if ( fMain )
                fprintf( pFile, ".output_required" );
            else
                fprintf( pFile, ".output_arrival" );
            if ( Vec_IntEntry(pModel->vTimeOutputs,i) != -1 )
                fprintf( pFile, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vTimeOutputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeOutputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                fprintf( pFile, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                fprintf( pFile, " inf" );
            else
                fprintf( pFile, " %.3f", Delay );
            fprintf( pFile, "\n" );
        }
    }
    // write objects
    Ntl_ModelForEachObj( pModel, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
        {
            fprintf( pFile, ".names" );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintf( pFile, " %s", pNet->pName );
            fprintf( pFile, " %s\n", Ntl_ObjFanout0(pObj)->pName );
            fprintf( pFile, "%s", pObj->pSop );
        }
        else if ( Ntl_ObjIsLatch(pObj) )
        {
            fprintf( pFile, ".latch" );
            fprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
            fprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
            assert( pObj->LatchId.regType == 0 || pObj->LatchId.regClass == 0 );
            if ( pObj->LatchId.regType )
            {
                if ( pObj->LatchId.regType == 1 )
                    fprintf( pFile, " fe" );
                else if ( pObj->LatchId.regType == 2 )
                    fprintf( pFile, " re" );
                else if ( pObj->LatchId.regType == 3 )
                    fprintf( pFile, " ah" );
                else if ( pObj->LatchId.regType == 4 )
                    fprintf( pFile, " al" );
                else if ( pObj->LatchId.regType == 5 )
                    fprintf( pFile, " as" );
                else
                    assert( 0 );
            }
            else if ( pObj->LatchId.regClass )
                fprintf( pFile, " %d", pObj->LatchId.regClass );
            if ( pObj->pClock )
                fprintf( pFile, " %s", pObj->pClock->pName );
            fprintf( pFile, " %d", pObj->LatchId.regInit );
            fprintf( pFile, "\n" );
        }
        else if ( Ntl_ObjIsBox(pObj) )
        {
            fprintf( pFile, ".subckt %s", pObj->pImplem->pName );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintf( pFile, " %s=%s", Ntl_ModelPiName(pObj->pImplem, k), pNet->pName );
            Ntl_ObjForEachFanout( pObj, pNet, k )
                fprintf( pFile, " %s=%s", Ntl_ModelPoName(pObj->pImplem, k), pNet->pName );
            fprintf( pFile, "\n" );
        }
    }
    fprintf( pFile, ".end\n\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the netlist into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlif_old( Ntl_Man_t * p, char * pFileName )
{
    FILE * pFile;
    Ntl_Mod_t * pModel;
    int i;
    // start the output stream
    pFile = fopen( pFileName, "w" );
    if ( pFile == NULL )
    {
        fprintf( stdout, "Ioa_WriteBlif(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "# Benchmark \"%s\" written by ABC-8 on %s\n", p->pName, Ioa_TimeStamp() );
    // write the models
    Ntl_ManForEachModel( p, pModel, i )
        Ioa_WriteBlifModel( pFile, pModel, i==0 );
    // close the file
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Writes the logic network into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifLogic( Nwk_Man_t * pNtk, Ntl_Man_t * p, char * pFileName )
{
    Ntl_Man_t * pNew;
    pNew = Ntl_ManInsertNtk( p, pNtk );
    Ioa_WriteBlif( pNew, pFileName );
    Ntl_ManFree( pNew );
}


 
/**Function*************************************************************

  Synopsis    [Procedure to write data into BZ2 file.]

  Description [Based on the vsnprintf() man page.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct bz2file {
  FILE   * f;
  BZFILE * b;
  char   * buf;
  int      nBytes;
  int      nBytesMax;
} bz2file;

int fprintfBz2(bz2file * b, char * fmt, ...) {
    if (b->b) {
        char * newBuf;
        int bzError;
        va_list ap;
        while (1) {
            va_start(ap,fmt);
            b->nBytes = vsnprintf(b->buf,b->nBytesMax,fmt,ap);
            va_end(ap);
            if (b->nBytes > -1 && b->nBytes < b->nBytesMax)
                break;
            if (b->nBytes > -1)
                b->nBytesMax = b->nBytes + 1;
            else
                b->nBytesMax *= 2;
            if ((newBuf = REALLOC( char,b->buf,b->nBytesMax )) == NULL)
                return -1;
            else
                b->buf = newBuf;
        }
        BZ2_bzWrite( &bzError, b->b, b->buf, b->nBytes );
        if (bzError == BZ_IO_ERROR) {
            fprintf( stdout, "Ioa_WriteBlif(): I/O error writing to compressed stream.\n" );
            return -1;
        }
        return b->nBytes;
    } else {
        int n;
        va_list ap;
        va_start(ap,fmt);
        n = vfprintf( b->f, fmt, ap);
        va_end(ap);
        return n;
    }
}

/**Function*************************************************************

  Synopsis    [Writes one model into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifModelGz( gzFile pFile, Ntl_Mod_t * pModel, int fMain )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    float Delay;
    int i, k;
    gzprintf( pFile, ".model %s\n", pModel->pName );
    if ( pModel->attrWhite || pModel->attrBox || pModel->attrComb || pModel->attrKeep )
    {
        gzprintf( pFile, ".attrib" );
        gzprintf( pFile, " %s", pModel->attrWhite? "white": "black" );
        gzprintf( pFile, " %s", pModel->attrBox?   "box"  : "logic" );
        gzprintf( pFile, " %s", pModel->attrComb?  "comb" : "seq"   );
//        gzprintf( pFile, " %s", pModel->attrKeep?  "keep" : "sweep" );
        gzprintf( pFile, "\n" );
    }
    gzprintf( pFile, ".inputs" );
    Ntl_ModelForEachPi( pModel, pObj, i )
        gzprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
    gzprintf( pFile, "\n" );
    gzprintf( pFile, ".outputs" );
    Ntl_ModelForEachPo( pModel, pObj, i )
        gzprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
    gzprintf( pFile, "\n" );
    // write delays
    if ( pModel->vDelays )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vDelays); i += 3 )
        {
            gzprintf( pFile, ".delay" );
            if ( Vec_IntEntry(pModel->vDelays,i) != -1 )
                gzprintf( pFile, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vDelays,i)))->pName );
            if ( Vec_IntEntry(pModel->vDelays,i+1) != -1 )
                gzprintf( pFile, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vDelays,i+1)))->pName );
            gzprintf( pFile, " %.3f", Aig_Int2Float(Vec_IntEntry(pModel->vDelays,i+2)) );
            gzprintf( pFile, "\n" );
        }
    }
    if ( pModel->vTimeInputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeInputs); i += 2 )
        {
            if ( fMain )
                gzprintf( pFile, ".input_arrival" );
            else
                gzprintf( pFile, ".input_required" );
            if ( Vec_IntEntry(pModel->vTimeInputs,i) != -1 )
                gzprintf( pFile, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vTimeInputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeInputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                gzprintf( pFile, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                gzprintf( pFile, " inf" );
            else
                gzprintf( pFile, " %.3f", Delay );
            gzprintf( pFile, "\n" );
        }
    }
    if ( pModel->vTimeOutputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeOutputs); i += 2 )
        {
            if ( fMain )
                gzprintf( pFile, ".output_required" );
            else
                gzprintf( pFile, ".output_arrival" );
            if ( Vec_IntEntry(pModel->vTimeOutputs,i) != -1 )
                gzprintf( pFile, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vTimeOutputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeOutputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                gzprintf( pFile, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                gzprintf( pFile, " inf" );
            else
                gzprintf( pFile, " %.3f", Delay );
            gzprintf( pFile, "\n" );
        }
    }
    // write objects
    Ntl_ModelForEachObj( pModel, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
        {
            gzprintf( pFile, ".names" );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                gzprintf( pFile, " %s", pNet->pName );
            gzprintf( pFile, " %s\n", Ntl_ObjFanout0(pObj)->pName );
            gzprintf( pFile, "%s", pObj->pSop );
        }
        else if ( Ntl_ObjIsLatch(pObj) )
        {
            gzprintf( pFile, ".latch" );
            gzprintf( pFile, " %s", Ntl_ObjFanin0(pObj)->pName );
            gzprintf( pFile, " %s", Ntl_ObjFanout0(pObj)->pName );
            assert( pObj->LatchId.regType == 0 || pObj->LatchId.regClass == 0 );
            if ( pObj->LatchId.regType )
            {
                if ( pObj->LatchId.regType == 1 )
                    gzprintf( pFile, " fe" );
                else if ( pObj->LatchId.regType == 2 )
                    gzprintf( pFile, " re" );
                else if ( pObj->LatchId.regType == 3 )
                    gzprintf( pFile, " ah" );
                else if ( pObj->LatchId.regType == 4 )
                    gzprintf( pFile, " al" );
                else if ( pObj->LatchId.regType == 5 )
                    gzprintf( pFile, " as" );
                else
                    assert( 0 );
            }
            else if ( pObj->LatchId.regClass )
                gzprintf( pFile, " %d", pObj->LatchId.regClass );
            if ( pObj->pClock )
                gzprintf( pFile, " %s", pObj->pClock->pName );
            gzprintf( pFile, " %d", pObj->LatchId.regInit );
            gzprintf( pFile, "\n" );
        }
        else if ( Ntl_ObjIsBox(pObj) )
        {
            gzprintf( pFile, ".subckt %s", pObj->pImplem->pName );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                gzprintf( pFile, " %s=%s", Ntl_ModelPiName(pObj->pImplem, k), pNet->pName );
            Ntl_ObjForEachFanout( pObj, pNet, k )
                gzprintf( pFile, " %s=%s", Ntl_ModelPoName(pObj->pImplem, k), pNet->pName );
            gzprintf( pFile, "\n" );
        }
    }
    gzprintf( pFile, ".end\n\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the logic network into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifGz( Ntl_Man_t * p, char * pFileName )
{
    Ntl_Mod_t * pModel;
    int i;
    gzFile pFile;

    // start the output stream
    pFile = gzopen( pFileName, "wb" ); // if pFileName doesn't end in ".gz" then this acts as a passthrough to fopen
    if ( pFile == NULL )
    {
        fprintf( stdout, "Ioa_WriteBlif(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }

    gzprintf( pFile, "# Benchmark \"%s\" written by ABC-8 on %s\n", p->pName, Ioa_TimeStamp() );
    // write the models
    Ntl_ManForEachModel( p, pModel, i )
        Ioa_WriteBlifModelGz( pFile, pModel, i==0 );
    // close the file
    gzclose( pFile );
}


/**Function*************************************************************

  Synopsis    [Writes one model into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlifModelBz2( bz2file * b, Ntl_Mod_t * pModel, int fMain )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    float Delay;
    int i, k;
    fprintfBz2( b, ".model %s\n", pModel->pName );
    if ( pModel->attrWhite || pModel->attrBox || pModel->attrComb || pModel->attrKeep )
    {
        fprintfBz2( b, ".attrib" );
        fprintfBz2( b, " %s", pModel->attrWhite? "white": "black" );
        fprintfBz2( b, " %s", pModel->attrBox?   "box"  : "logic" );
        fprintfBz2( b, " %s", pModel->attrComb?  "comb" : "seq"   );
//        fprintfBz2( b, " %s", pModel->attrKeep?  "keep" : "sweep" );
        fprintfBz2( b, "\n" );
    }
    fprintfBz2( b, ".inputs" );
    Ntl_ModelForEachPi( pModel, pObj, i )
        fprintfBz2( b, " %s", Ntl_ObjFanout0(pObj)->pName );
    fprintfBz2( b, "\n" );
    fprintfBz2( b, ".outputs" );
    Ntl_ModelForEachPo( pModel, pObj, i )
        fprintfBz2( b, " %s", Ntl_ObjFanin0(pObj)->pName );
    fprintfBz2( b, "\n" );
    // write delays
    if ( pModel->vDelays )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vDelays); i += 3 )
        {
            fprintfBz2( b, ".delay" );
            if ( Vec_IntEntry(pModel->vDelays,i) != -1 )
                fprintfBz2( b, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vDelays,i)))->pName );
            if ( Vec_IntEntry(pModel->vDelays,i+1) != -1 )
                fprintfBz2( b, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vDelays,i+1)))->pName );
            fprintfBz2( b, " %.3f", Aig_Int2Float(Vec_IntEntry(pModel->vDelays,i+2)) );
            fprintfBz2( b, "\n" );
        }
    }
    if ( pModel->vTimeInputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeInputs); i += 2 )
        {
            if ( fMain )
                fprintfBz2( b, ".input_arrival" );
            else
                fprintfBz2( b, ".input_required" );
            if ( Vec_IntEntry(pModel->vTimeInputs,i) != -1 )
                fprintfBz2( b, " %s", Ntl_ObjFanout0(Ntl_ModelPi(pModel, Vec_IntEntry(pModel->vTimeInputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeInputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                fprintfBz2( b, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                fprintfBz2( b, " inf" );
            else
                fprintfBz2( b, " %.3f", Delay );
            fprintfBz2( b, "\n" );
        }
    }
    if ( pModel->vTimeOutputs )
    {
        for ( i = 0; i < Vec_IntSize(pModel->vTimeOutputs); i += 2 )
        {
            if ( fMain )
                fprintfBz2( b, ".output_required" );
            else
                fprintfBz2( b, ".output_arrival" );
            if ( Vec_IntEntry(pModel->vTimeOutputs,i) != -1 )
                fprintfBz2( b, " %s", Ntl_ObjFanin0(Ntl_ModelPo(pModel, Vec_IntEntry(pModel->vTimeOutputs,i)))->pName );
            Delay = Aig_Int2Float(Vec_IntEntry(pModel->vTimeOutputs,i+1));
            if ( Delay == -TIM_ETERNITY )
                fprintfBz2( b, " -inf" );
            else if ( Delay == TIM_ETERNITY )
                fprintfBz2( b, " inf" );
            else
                fprintfBz2( b, " %.3f", Delay );
            fprintfBz2( b, "\n" );
        }
    }
    // write objects
    Ntl_ModelForEachObj( pModel, pObj, i )
    {
        if ( Ntl_ObjIsNode(pObj) )
        {
            fprintfBz2( b, ".names" );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintfBz2( b, " %s", pNet->pName );
            fprintfBz2( b, " %s\n", Ntl_ObjFanout0(pObj)->pName );
            fprintfBz2( b, "%s", pObj->pSop );
        }
        else if ( Ntl_ObjIsLatch(pObj) )
        {
            fprintfBz2( b, ".latch" );
            fprintfBz2( b, " %s", Ntl_ObjFanin0(pObj)->pName );
            fprintfBz2( b, " %s", Ntl_ObjFanout0(pObj)->pName );
            assert( pObj->LatchId.regType == 0 || pObj->LatchId.regClass == 0 );
            if ( pObj->LatchId.regType )
            {
                if ( pObj->LatchId.regType == 1 )
                    fprintfBz2( b, " fe" );
                else if ( pObj->LatchId.regType == 2 )
                    fprintfBz2( b, " re" );
                else if ( pObj->LatchId.regType == 3 )
                    fprintfBz2( b, " ah" );
                else if ( pObj->LatchId.regType == 4 )
                    fprintfBz2( b, " al" );
                else if ( pObj->LatchId.regType == 5 )
                    fprintfBz2( b, " as" );
                else
                    assert( 0 );
            }
            else if ( pObj->LatchId.regClass )
                fprintfBz2( b, " %d", pObj->LatchId.regClass );
            if ( pObj->pClock )
                fprintfBz2( b, " %s", pObj->pClock->pName );
            fprintfBz2( b, " %d", pObj->LatchId.regInit );
            fprintfBz2( b, "\n" );
        }
        else if ( Ntl_ObjIsBox(pObj) )
        {
            fprintfBz2( b, ".subckt %s", pObj->pImplem->pName );
            Ntl_ObjForEachFanin( pObj, pNet, k )
                fprintfBz2( b, " %s=%s", Ntl_ModelPiName(pObj->pImplem, k), pNet->pName );
            Ntl_ObjForEachFanout( pObj, pNet, k )
                fprintfBz2( b, " %s=%s", Ntl_ModelPoName(pObj->pImplem, k), pNet->pName );
            fprintfBz2( b, "\n" );
        }
    }
    fprintfBz2( b, ".end\n\n" );
}

/**Function*************************************************************

  Synopsis    [Writes the logic network into the BLIF file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ioa_WriteBlif( Ntl_Man_t * p, char * pFileName )
{
    Ntl_Mod_t * pModel;
    int i, bzError;
    bz2file b;

    // write the GZ file
    if (!strncmp(pFileName+strlen(pFileName)-3,".gz",3)) 
    {
        Ioa_WriteBlifGz( p, pFileName );
        return;
    }

    memset(&b,0,sizeof(b));
    b.nBytesMax = (1<<12);
    b.buf = ALLOC( char,b.nBytesMax );

    // start the output stream
    b.f = fopen( pFileName, "wb" ); 
    if ( b.f == NULL )
    {
        fprintf( stdout, "Ioa_WriteBlif(): Cannot open the output file \"%s\".\n", pFileName );
        FREE(b.buf);
        return;
    }
    if (!strncmp(pFileName+strlen(pFileName)-4,".bz2",4)) {
        b.b = BZ2_bzWriteOpen( &bzError, b.f, 9, 0, 0 );
        if ( bzError != BZ_OK ) {
            BZ2_bzWriteClose( &bzError, b.b, 0, NULL, NULL );
            fprintf( stdout, "Ioa_WriteBlif(): Cannot start compressed stream.\n" );
            fclose( b.f );
            FREE(b.buf);
            return;
        }
    }

    fprintfBz2( &b, "# Benchmark \"%s\" written by ABC-8 on %s\n", p->pName, Ioa_TimeStamp() );
    // write the models
    Ntl_ManForEachModel( p, pModel, i )
        Ioa_WriteBlifModelBz2( &b, pModel, i==0 );
    // close the file
    if (b.b) {
        BZ2_bzWriteClose( &bzError, b.b, 0, NULL, NULL );
        if (bzError == BZ_IO_ERROR) {
            fprintf( stdout, "Ioa_WriteBlif(): I/O error closing compressed stream.\n" );
            fclose( b.f );
            FREE(b.buf);
            return;
        }
    }
    fclose( b.f );
    FREE(b.buf);
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


