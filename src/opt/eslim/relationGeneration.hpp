/**CFile****************************************************************

  FileName    [relationGeneration.hpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Procedures for computing Boolean relations.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - March 2025.]

  Revision    [$Id: relationGeneration.hpp,v 1.00 2025/03/17 00:00:00 Exp $]

***********************************************************************/

#ifndef ABC__OPT__ESLIM__RELATIONGENERATION_h
#define ABC__OPT__ESLIM__RELATIONGENERATION_h

#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "misc/util/abc_namespaces.h"
#include <misc/util/abc_global.h>
#include "aig/gia/gia.h"

#include "utils.hpp"
// #include "satInterfaces.hpp"


ABC_NAMESPACE_CXX_HEADER_START

namespace eSLIM {

  template<class Derived>
  class RelationGenerator {

    public:
      static Vec_Int_t* computeRelation(Gia_Man_t* gia_man, const Subcircuit& subcir);

    private:
      Gia_Man_t* pGia;
      const Subcircuit& subcir; 
      
      RelationGenerator(Gia_Man_t* pGia, const Subcircuit& subcir);
      void setup();
      Vec_Int_t* getRelation();

    friend Derived;
  };

  // The class almost entirely duplicates the functionality provided by Gia_ManGenIoCombs in giaQBF.c
  // But the implementation in this class allows to take forbidden pairs into account.
  class RelationGeneratorABC : public RelationGenerator<RelationGeneratorABC> {
      
    private:
      RelationGeneratorABC(Gia_Man_t* pGia, const Subcircuit& subcir);
      void setupImpl() {};
      Vec_Int_t* getRelationImpl();
      Gia_Man_t * generateMiter();

      std::unordered_set<int> inputs_in_forbidden_pairs;
    
    friend RelationGenerator;
  };


  // Add other engine for the generation of relations
  // class MyRelationGenerator : public RelationGenerator<MyRelationGenerator> {
  //   private:
  //     void setupImpl()
  //     Vec_Int_t* getRelationImpl();
  //   friend RelationGenerator;
  // };


  template <typename T>
  inline RelationGenerator<T>::RelationGenerator(Gia_Man_t* pGia, const Subcircuit& subcir)
                      : pGia(pGia), subcir(subcir) {
  }

  template <typename T>
  inline Vec_Int_t* RelationGenerator<T>::computeRelation(Gia_Man_t* gia_man, const Subcircuit& subcir) {
    T generator(gia_man, subcir);
    generator.setup();
    return generator.getRelation();
  }

  template <typename T>
  inline void RelationGenerator<T>::setup() {
    static_cast<T*>(this)->setupImpl();
  }

  template <typename T>
  inline Vec_Int_t* RelationGenerator<T>::getRelation() {
    return static_cast<T*>(this)->getRelationImpl();
  }
}

ABC_NAMESPACE_CXX_HEADER_END

#endif
