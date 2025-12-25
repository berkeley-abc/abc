//
// Created by Yen-Sheng Ho on 8/9/16.
//

#include <iostream>

#include <base/wlc/wlc.h>
#include "Netlist.h"

ABC_NAMESPACE_IMPL_START

using namespace std;

namespace UFAR {

WNetlist::WNetlist() {
    _pNtk = Wlc_NtkAlloc("main", 100);
}

WNetlist::WNetlist(Wlc_Ntk_t *pNtk) {
    if (pNtk)
        _pNtk = Wlc_NtkDupDfsSimple(pNtk);
    else
        _pNtk = NULL;
}

WNetlist::WNetlist(const WNetlist& that) {
    _pNtk = Wlc_NtkDupDfsSimple(that._pNtk);
}

WNetlist::WNetlist(WNetlist && that) {
    _pNtk = that._pNtk;
    that._pNtk = NULL;
}

WNetlist& WNetlist::operator=(const WNetlist& that) {
    Wlc_Ntk_t * pTemp = _pNtk;
    _pNtk = Wlc_NtkDupDfsSimple(that._pNtk);
    if (pTemp) Wlc_NtkFree(pTemp);
    return *this;
}

WNetlist::~WNetlist() {
    if (_pNtk) Wlc_NtkFree(_pNtk);
}

void WNetlist::Clear() {
    if (_pNtk) Wlc_NtkFree(_pNtk);
    _pNtk = Wlc_NtkAlloc("main", 100);
}

bool WNetlist::Empty() const {
    if (_pNtk == NULL) return true;

    return Wlc_NtkObjNum(_pNtk) == 0;
}

void WNetlist::Reset(Wlc_Ntk_t *pNtk) {
    Wlc_Ntk_t * pTemp = _pNtk;
    _pNtk = Wlc_NtkDupDfsSimple(pNtk);
    if (pTemp) Wlc_NtkFree(pTemp);
}

}

ABC_NAMESPACE_IMPL_END
