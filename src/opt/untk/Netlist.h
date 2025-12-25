//
// Created by ysho on 8/9/16.
//

#ifndef ABC_WAR_NETLIST_H
#define ABC_WAR_NETLIST_H

#include <type_traits>

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_CXX_HEADER_START

typedef struct Wlc_Ntk_t_ Wlc_Ntk_t;

namespace UFAR {

class WNetlist {
public:
    WNetlist();
    WNetlist(Wlc_Ntk_t * pNtk);
    WNetlist(const WNetlist& that);
    ~WNetlist();
    WNetlist(WNetlist && that);
    WNetlist& operator=(const WNetlist& that);
    Wlc_Ntk_t * GetNtk() const {return _pNtk;}
    void Clear();
    bool Empty() const;
    void Reset(Wlc_Ntk_t * pNtk);
private:
    Wlc_Ntk_t * _pNtk;
};


}

ABC_NAMESPACE_CXX_HEADER_END

#endif //ABC_WAR_NETLIST_H
