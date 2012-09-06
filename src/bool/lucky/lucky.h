/**CFile****************************************************************

  FileName    [lucky.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Semi-canonical form computation package.]

  Synopsis    [External declarations.]

  Author      [Jake]

  Date        [Started - August 2012]

***********************************************************************/

#ifndef ABC__bool__lucky__LUCKY_H_
#define ABC__bool__lucky__LUCKY_H_


ABC_NAMESPACE_HEADER_START

extern unsigned Kit_TruthSemiCanonicize_new( unsigned * pInOut, unsigned * pAux, int nVars, char * pCanonPerm );
extern int      luckyCanonicizer_final_fast( word * pInOut, int nVars, char * pCanonPerm );
extern void     resetPCanonPermArray(char* x, int nVars); 

ABC_NAMESPACE_HEADER_END

#endif /* LUCKY_H_ */