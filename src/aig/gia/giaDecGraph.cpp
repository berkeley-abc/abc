/**CFile****************************************************************

  FileName    [giaDecGraph.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Implementation of circuit learning.]

  Author      [Jiun-Hao Chen]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - 2025.]

  Revision    [$Id: giaDecGraph.c,v 1.00 2025/01/01 00:00:00 Exp $]

***********************************************************************/

#ifdef _WIN32

#ifndef __MINGW32__
#pragma warning(disable : 4786) // warning C4786: identifier was truncated to '255' characters in the browser information
#endif
#endif

#include <cmath>
#include <vector>
#include <string>
#include <sstream>
#include <iostream>
#include <cstdint>
#include <iomanip>
#include <set>
#include <numeric>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <functional>
#include <iterator>

#include "gia.h"
#include "misc/vec/vecHash.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

namespace DecGraph {

template<typename I,
         typename std::enable_if<std::is_integral<I>::value, int>::type = 0>
struct integer_iterator {
    using iterator_category = std::input_iterator_tag;
    using value_type = I;
    using difference_type = I;
    using pointer = I*;
    using reference = I&;

    explicit integer_iterator(I value)
        : value(value) {
    }

    I operator*() const {
        return value;
    }

    I const* operator->() const {
        return &value;
    }

    integer_iterator& operator++() {
        ++value;
        return *this;
    }

    integer_iterator operator++(int) {
        const auto copy = *this;
        ++*this;
        return copy;
    }

    bool operator==(const integer_iterator& other) const {
        return value == other.value;
    }

    bool operator!=(const integer_iterator& other) const {
        return value != other.value;
    }

protected:
    I value;
};

template<typename I, typename std::enable_if<std::is_integral<I>::value,
                                             bool>::type
                     = true>
struct integer_range {
public:
    integer_range(I begin, I end)
        : begin_(begin), end_(end) {
    }
    integer_iterator<I> begin() const {
        return begin_;
    }
    integer_iterator<I> end() const {
        return end_;
    }

private:
    integer_iterator<I> begin_;
    integer_iterator<I> end_;
};

template<typename Integer1, typename Integer2,
         typename std::enable_if<std::is_integral<Integer1>::value,
                                 bool>::type
         = true,
         typename std::enable_if<std::is_integral<Integer2>::value,
                                 bool>::type
         = true>
integer_range<Integer2> irange(Integer1 begin, Integer2 end) {
    return {static_cast<Integer2>(begin),
            std::max(static_cast<Integer2>(begin), end)};
}

template<typename Integer,
         typename std::enable_if<std::is_integral<Integer>::value,
                                 bool>::type
         = true>
integer_range<Integer> irange(Integer end) {
    return {Integer(), std::max(Integer(), end)};
}
// End Iterger Iterator

static int IdToLit(int id, bool fCompl) {
    return (id << 1) | (fCompl ? 1 : 0);
}

static int LitToId(int lit) {
    return lit >> 1;
}

static int LitNot(int lit) {
    return lit ^ 1;
}
static int LitNotCond(int lit, bool cond) {
    return lit ^ (int)cond;
}

static int LitIsComplement(int lit) {
    return (lit & 1);
}

#ifdef _MSC_VER
#include <intrin.h>
#define __builtin_popcount __popcnt
#endif

#ifdef DECTHREAD
#else
static int decGraphXadd(int* addr, int delta) {
    int temp = *addr;
    *addr += delta;
    return temp;
}
#endif

static int neededWords(int num_variables) {
    return num_variables <= 6 ? 1 : 1 << (num_variables - 6);
}

static inline const uint64_t permutation_mask[5][3] = {
    {0x9999999999999999, 0x2222222222222222, 0x4444444444444444},
    {0xC3C3C3C3C3C3C3C3, 0x0C0C0C0C0C0C0C0C, 0x3030303030303030},
    {0xF00FF00FF00FF00F, 0x00F000F000F000F0, 0x0F000F000F000F00},
    {0xFF0000FFFF0000FF, 0x0000FF000000FF00, 0x00FF000000FF0000},
    {0xFFFF00000000FFFF, 0x00000000FFFF0000, 0x0000FFFF00000000}};
static inline const uint64_t swap_mask[6][6] = {
    {0x2222222222222222, 0x0A0A0A0A0A0A0A0A, 0x00AA00AA00AA00AA, 0x0000AAAA0000AAAA, 0x00000000AAAAAAAA, 0xAAAAAAAAAAAAAAAA},
    {0x0000000000000000, 0x0C0C0C0C0C0C0C0C, 0x00CC00CC00CC00CC, 0x0000CCCC0000CCCC, 0x00000000CCCCCCCC, 0xCCCCCCCCCCCCCCCC},
    {0x0000000000000000, 0x0000000000000000, 0x00F000F000F000F0, 0x0000F0F00000F0F0, 0x00000000F0F0F0F0, 0xF0F0F0F0F0F0F0F0},
    {0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000FF000000FF00, 0x00000000FF00FF00, 0xFF00FF00FF00FF00},
    {0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x00000000FFFF0000, 0xFFFF0000FFFF0000},
    {0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xFFFFFFFF00000000}};
static inline const uint64_t elementary_mask[6] = {
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000};
static inline const uint64_t extend_mask[5] = {
    0xC000000000000000,
    0xF000000000000000,
    0xFF00000000000000,
    0xFFFF000000000000,
    0xFFFFFFFF00000000};
static inline const uint64_t ones_mask[7]{
    0x0000000000000001,
    0x0000000000000003,
    0x000000000000000f,
    0x00000000000000ff,
    0x000000000000ffff,
    0x00000000ffffffff,
    0xffffffffffffffff};

struct TruthTableData {
    int refcount;
    std::vector<uint64_t> data;
    std::vector<uint64_t> place_to_variable;
    std::vector<uint64_t> variable_to_place;
};

class TruthTable {
public:
    // empty
    TruthTable();
    // release
    ~TruthTable();
    // copy
    TruthTable(const TruthTable& m);
    // assign
    TruthTable& operator=(const TruthTable& m);
    // deep copy
    TruthTable clone(void) const;
    // deep copy from other truth table, inplace
    void clone_from(const TruthTable& tt);

public:
    // build from bits
    TruthTable(uint64_t bits);

public:
    // allocate truth table
    void create(uint64_t bits);

public:
    // refcount++
    void addref();
    // refcount--
    void release();

public:
    bool operator[](int index);
    bool operator==(const TruthTable& rhs) const;
    bool operator!=(const TruthTable& rhs) const;
    TruthTable operator~(void);

public:
    uint8_t nVars() const;
    uint64_t nBits() const;
    uint32_t nWords() const;
    bool empty() const;

public:
    uint64_t* data() const;
    void set(int index, bool value);
    void rand();
    void readBinary(std::string bitstream);
    void readBinaryReverse(std::string bitstream);
    void readHex(std::string bitstream);
    void readHexReverse(std::string bitstream);

public:
    void resetPosition(void);
    void moveTo(uint32_t variable, uint8_t place, bool adjecent = false);
    void swapVariable(int variable1, int variable2);
    void extend(int nVariable, std::vector<int> variableOrder = {});
    int countCofactor(int nBoundSet, std::vector<TruthTable>& cofactors, std::vector<TruthTable>& boundSetFunctions, bool derive = false);
    TruthTable cofactor(uint32_t variable, bool negative);
    uint64_t countOne(void);
    bool hasVariable(uint32_t variable);
    int supportSize(void);
    int isAndorOr(void);
    void variablePartition(int nMSB, std::vector<int>& MSB, std::vector<int>& LSB);
    uint32_t getVariable(int place);
    void swapAdjacent(uint64_t* rdata, uint64_t* data, int index);
    float cost(void);

public:
    std::string hash_str(void);

private:
    void assign(int offset, uint64_t value);
    void assign(uint64_t value);

public:
    enum class Format {
        BIN,
        HEX
    };
    void print(Format format = Format::BIN);
    void printReverse(Format format = Format::BIN);
    void printPosition(void);
    std::string str(Format format = Format::BIN);
    std::string strReverse(Format format = Format::BIN);

private:
    std::vector<int64_t> fourierTransform_rec(uint64_t begin, uint64_t end);

public:
    std::vector<float> fourierTransform(void);
    std::vector<float> fourierWeight(void);
    float fourierCost(void);

private:
    // pointer to the read data
    TruthTableData* _data;

    // reference counter
    int* _refcount;

    // number of variables
    uint8_t _vars;
    // number of bits
    uint64_t _bits;
};

inline TruthTable::TruthTable()
    : _data(nullptr), _refcount(nullptr), _vars(0), _bits(0) {
}

inline TruthTable::~TruthTable() {
    release();
}

inline TruthTable::TruthTable(const TruthTable& m)
    : _data(m._data), _refcount(m._refcount), _vars(m._vars), _bits(m._bits) {
    addref();
}

inline TruthTable& TruthTable::operator=(const TruthTable& m) {
    if (this == &m)
        return *this;

    if (m._refcount)
        decGraphXadd(m._refcount, 1);

    release();

    _data = m._data;
    _refcount = m._refcount;
    _vars = m._vars;
    _bits = m._bits;

    return *this;
}

inline TruthTable::TruthTable(uint64_t bits)
    : _data(nullptr), _refcount(nullptr), _vars(0), _bits(0) {
    create(bits);
}

inline void TruthTable::addref(void) {
    if (_refcount)
        decGraphXadd(_refcount, 1);
}

inline void TruthTable::release(void) {
    if (_refcount && decGraphXadd(_refcount, -1) == 1) {
        delete _data;
    }

    _data = nullptr;
    _refcount = nullptr;
    _vars = 0;
    _bits = 0;
}

inline uint8_t TruthTable::nVars() const {
    return _vars;
}

inline uint64_t TruthTable::nBits() const {
    return _bits;
}

inline uint32_t TruthTable::nWords() const {
    return _data ? _data->data.size() : 0;
}

inline bool TruthTable::empty() const {
    return (_data == nullptr) || (_bits == 0);
}

inline uint64_t* TruthTable::data() const {
    if (_data)
        return _data->data.data();
    return nullptr;
}

inline bool TruthTable::operator[](int index) {
    if (empty())
        return false;
    return (_data->data[index / (sizeof(uint64_t) * 8)] << (index % (sizeof(uint64_t) * 8))) & 0x8000000000000000;
}

TruthTable TruthTable::clone(void) const {
    if (empty())
        return TruthTable();

    TruthTable tt;

    tt.create(_bits);

    if (tt.empty()) {
        return tt;
    }

    *tt._data = *this->_data;
    *tt._refcount = 1;

    return tt;
}

void TruthTable::clone_from(const TruthTable &tt) {
    *this = tt.clone();
    return;
}

void TruthTable::create(uint64_t bits) {
    if (_bits == bits) {
        resetPosition();
        return;
    }

    release();

    _bits = bits;
    _vars = std::log2(bits);

    _data = new TruthTableData;

    if (_data) {
        _data->data.resize(std::max((uint64_t)(bits / (sizeof(uint64_t) * 8)), (uint64_t)1), 0);
        resetPosition();
        _refcount = &_data->refcount;
        *_refcount = 1;
    }
    return;
}

bool TruthTable::operator==(const TruthTable &rhs) const {
    if (this->_data == rhs._data)
        return true;
    if (nBits() != rhs.nBits())
        return false;

    uint64_t *ldata = this->data();
    uint64_t *rdata = rhs.data();
    for (const auto &i : irange(nWords())) {
        if (ldata[i] != rdata[i])
            return false;
    }
    return true;
}

bool TruthTable::operator!=(const TruthTable &rhs) const {
    return !(*this == rhs);
}

TruthTable TruthTable::operator~(void) {
    TruthTable rtt(nBits());
    uint64_t *ldata = this->data();
    uint64_t *rdata = rtt.data();
    for (const auto &i : irange(nWords())) {
        rdata[i] = ~ldata[i];
    }
    if (nBits() < 64) {
        for (const auto &i : irange(nBits(), 64)) {
            rtt.set(i, false);
        }
    }
    return rtt;
}

void TruthTable::set(int index, bool value) {
    if (empty())
        return;

    uint64_t *data = &_data->data[0];
    if (value) {
        data[index / (sizeof(uint64_t) * 8)] |= (uint64_t)0x8000000000000000 >> (index % (sizeof(uint64_t) * 8));
    } else {
        data[index / (sizeof(uint64_t) * 8)] &= ~((uint64_t)0x8000000000000000 >> (index % (sizeof(uint64_t) * 8)));
    }
    return;
}

void TruthTable::rand(void) {
    if (empty())
        return;

    uint64_t *data = this->data();
    for (const auto &i : irange(nWords())) {
        data[i] = ((uint64_t)std::rand() << 32) | ((uint64_t)std::rand());
    }
    for (const auto &i : irange(nBits(), ((uint64_t)64 * nWords()))) {
        set(i, false);
    }
    return;
}

void TruthTable::readBinary(std::string bitstream) {
    create(bitstream.size());
    for (const auto &i : irange(nBits())) {
        set(i, bitstream[i] == '1');
    }
    return;
}

void TruthTable::readBinaryReverse(std::string bitstream_reverse) {
    std::reverse(bitstream_reverse.begin(), bitstream_reverse.end());
    readBinary(bitstream_reverse);
    return;
}

static char hexToBin(char ch) {
    if (ch >= '0' && ch <= '9') return ch - '0';
    if (ch >= 'A' && ch <= 'F') return ch - 'A' + 10;
    if (ch >= 'a' && ch <= 'f') return ch - 'a' + 10;
    return 0;
}

void TruthTable::readHex(std::string bitstream) {
    create(bitstream.size() * 4);
    for (const auto &i : irange(nBits() / 4)) {
        char value = hexToBin(bitstream[i]);
        for (const auto &j : irange(4)) {
            set(i * 4 + j, (value >> (3 - j)) & 1);
        }
    }
    return;
}

void TruthTable::readHexReverse(std::string bitstream) {
    create(bitstream.size() * 4);
    for (const auto &i : irange(nBits() / 4)) {
        char value = hexToBin(bitstream[i]);
        for (const auto &j : irange(4)) {
            set(nBits() - (i * 4 + j) - 1, (value << j) & 0x8);
        }
    }
    return;
}

void TruthTable::resetPosition(void) {
    if (empty())
        return;

    auto &place_to_variable = _data->place_to_variable;
    auto &variable_to_place = _data->variable_to_place;
    place_to_variable.resize(nVars());
    variable_to_place.resize(nVars());
    for (const auto &i : irange(nVars())) {
        place_to_variable[i] = variable_to_place[i] = i;
    }
    return;
}

void TruthTable::moveTo(uint32_t variable, uint8_t place, bool adjecent) {
    if (empty())
        return;

    auto &place_to_variable = _data->place_to_variable;
    auto &variable_to_place = _data->variable_to_place;

    if (!adjecent) {
        swapVariable(variable_to_place[variable], place);
    }

    TruthTable temp(nBits());
    uint64_t *pData = this->data();
    uint64_t *pOut = temp.data();
    uint64_t *pTemp = nullptr;
    uint32_t iPlace0, iPlace1, Count = 0;
    while (variable_to_place[variable] < place) {
        iPlace0 = variable_to_place[variable];
        iPlace1 = variable_to_place[variable] + 1;
        this->swapAdjacent(pOut, pData, iPlace0);
        pTemp = pData;
        pData = pOut, pOut = pTemp;
        variable_to_place[place_to_variable[iPlace0]]++;
        variable_to_place[place_to_variable[iPlace1]]--;
        std::swap(place_to_variable[iPlace0], place_to_variable[iPlace1]);
        Count++;
    }
    while (variable_to_place[variable] > place) {
        iPlace0 = variable_to_place[variable] - 1;
        iPlace1 = variable_to_place[variable];
        this->swapAdjacent(pOut, pData, iPlace0);
        pTemp = pData;
        pData = pOut, pOut = pTemp;
        variable_to_place[place_to_variable[iPlace0]]++;
        variable_to_place[place_to_variable[iPlace1]]--;
        std::swap(place_to_variable[iPlace0], place_to_variable[iPlace1]);
        Count++;
    }
    uint64_t *data = this->data();
    if (Count & 1) {
        for (const auto &i : irange(nWords())) {
            data[i] = pData[i];
        }
    }
    return;
}

void TruthTable::swapVariable(int variable1, int variable2) {
    if (empty())
        return;

    int nWord = nWords();

    if (variable1 == variable2) {
        return;
    }
    if (variable2 < variable1) {
        std::swap(variable1, variable2);
    }

    auto &place_to_variable = _data->place_to_variable;
    auto &variable_to_place = _data->variable_to_place;
    uint64_t *data = this->data();
    if (variable1 < 6 && variable2 < 6) {
        int nShift = (1 << variable2) - (1 << variable1);
        for (const auto &w : irange(nWord)) {
            uint64_t low2High = (data[w] & swap_mask[variable1][variable2 - 1]) << nShift;
            data[w] &= ~swap_mask[variable1][variable2 - 1];
            uint64_t high2Low = (data[w] & (swap_mask[variable1][variable2 - 1] << nShift)) >> nShift;
            data[w] &= ~(swap_mask[variable1][variable2 - 1] << nShift);
            data[w] = data[w] | low2High | high2Low;
        }
    } else if (variable1 < 6 && variable2 >= 6) {
        int nStep = neededWords(variable2 + 1) / 2;
        int nShift = 1 << variable1;
        for (int w = 0; w < nWord; w += 2 * nStep) {
            for (int j = 0; j < nStep; j++) {
                uint64_t low2High = (data[w + j] & (swap_mask[variable1][5] >> nShift)) << nShift;
                data[w + j] &= ~(swap_mask[variable1][5] >> nShift);
                uint64_t high2Low = (data[w + nStep + j] & (swap_mask[variable1][5])) >> nShift;
                data[w + nStep + j] &= ~(swap_mask[variable1][5]);
                data[w + j] |= high2Low;
                data[w + nStep + j] |= low2High;
            }
        }
    } else {
        int nStep1 = neededWords(variable1 + 1) / 2;
        int nStep2 = neededWords(variable2 + 1) / 2;
        for (int w = 0; w < nWord; w += 2 * nStep2) {
            for (int i = 0; i < nStep2; i += 2 * nStep1) {
                for (int j = 0; j < nStep1; j++) {
                    std::swap(data[w + nStep1 + i + j], data[w + nStep2 + i + j]);
                }
            }
        }
    }

    variable_to_place[place_to_variable[variable1]] = variable2;
    variable_to_place[place_to_variable[variable2]] = variable1;
    std::swap(place_to_variable[variable1], place_to_variable[variable2]);
    return;
}

void TruthTable::extend(int nExtend, std::vector<int> variable_order) {
    if (empty())
        return;

    TruthTable temp(this->nBits() * (((uint64_t)1) << nExtend));

    int vars = this->nVars();
    int bits = this->nBits();
    uint64_t *data = this->data();
    uint64_t *temp_data = temp.data();
    if (vars < 6) {
        for (const auto &i : irange(std::min((((uint64_t)1) << nExtend), (uint64_t)64))) {
            temp_data[0] |= (data[0] & extend_mask[vars - 1]) >> (i * bits);
        }
        if (temp.nWords() > 1) {
            for (const auto &i : irange(1, temp.nWords())) {
                temp_data[i] = temp_data[0];
            }
        }
    } else {
        int nSize = nWords();
        for (const auto &i : irange((((uint64_t)1) << nExtend))) {
            for (const auto &j : irange(nSize)) {
                temp_data[i * nSize + j] = data[j];
            }
        }
    }
    for (const auto &i : irange(variable_order.size())) {
        temp.moveTo(i, variable_order[i]);
    }
    temp.resetPosition();
    this->clone_from(temp);
    return;
}

int TruthTable::countCofactor(int nBoundSet, std::vector<TruthTable> &cofactors, std::vector<TruthTable> &boundSetFunctions, bool derive) {
    if (empty())
        return 0;

    uint64_t nFreeSet = nVars() - nBoundSet;
    uint64_t nMinterm = ((uint64_t)1 << nBoundSet);
    if (derive) {
        cofactors.clear();
        boundSetFunctions.clear();
    }
    if (nFreeSet == 0) {
        if (derive) {
            cofactors.emplace_back(*this);
        }
        return 1;
    }

    std::vector<uint64_t> iCofactor(128, 0);
    uint64_t iShift = 0;
    uint64_t i, c, w;
    uint64_t nCofactor;

    uint64_t *data = this->data();
    if (nFreeSet < 6) {
        uint64_t sCofactor = ((uint64_t)1 << nFreeSet);
        uint64_t mCofactor = (((uint64_t)1) << sCofactor) - 1;
        for (nCofactor = i = 0; i < nMinterm; ++i) {
            uint64_t cofactor = (data[(iShift + i * sCofactor) / 64] >> ((64 - (iShift + (i + 1) * sCofactor)) % 64)) & mCofactor;
            for (c = 0; c < nCofactor; ++c) {
                if (cofactor == iCofactor[c]) {
                    break;
                }
            }
            // record the unique cofactor
            if (c == nCofactor) {
                iCofactor[nCofactor++] = cofactor;
                if (derive) {
                    boundSetFunctions.emplace_back(TruthTable(nMinterm));
                }
            }
            if (derive) {
                // record the bound set function
                for (c = 0; c < nCofactor; ++c) {
                    if (cofactor == iCofactor[c]) {
                        boundSetFunctions[c].set(i, true);
                    }
                }
            }
        }
        if (derive) {
            for (c = 0; c < nCofactor; ++c) {
                TruthTable cofactor(((uint64_t)1 << nFreeSet));
                cofactor.assign(iCofactor[c]);
                cofactors.emplace_back(cofactor);
            }
        }
    } else {
        uint32_t nWords = neededWords(nFreeSet);
        for (nCofactor = i = 0; i < nMinterm; ++i) {
            uint64_t *cofactor_begin = data + (iShift + i * nWords);
            for (c = 0; c < nCofactor; ++c) {
                uint64_t *cofactor_compare = data + (iShift + iCofactor[c] * nWords);
                for (w = 0; w < nWords; ++w) {
                    if (cofactor_begin[w] != cofactor_compare[w]) {
                        break;
                    }
                }
                if (w == nWords) {
                    break;
                }
            }
            // record the index of the unique cofactor
            if (c == nCofactor) {
                iCofactor[nCofactor++] = i;
                if (derive) {
                    boundSetFunctions.emplace_back(TruthTable(nMinterm));
                }
            }
            // record the bound set function
            if (derive) {
                for (c = 0; c < nCofactor; ++c) {
                    uint64_t *cofactor_compare = data + (iShift + iCofactor[c] * nWords);
                    for (w = 0; w < nWords; ++w) {
                        if (cofactor_begin[w] != cofactor_compare[w]) {
                            break;
                        }
                    }
                    if (w == nWords) {
                        boundSetFunctions[c].set(i, true);
                    }
                }
            }
        }
        if (derive) {
            for (c = 0; c < nCofactor; ++c) {
                TruthTable cofactor(((uint64_t)1 << nFreeSet));
                for (w = 0; w < nWords; ++w) {
                    cofactor.assign(w, data[iShift + iCofactor[c] * nWords + w]);
                }
                cofactors.emplace_back(cofactor);
            }
        }
    }

    return nCofactor;
}

TruthTable TruthTable::cofactor(uint32_t variable, bool negative) {
    if (empty())
        return TruthTable();

    TruthTable rtt(nBits());

    if (variable >= nVars()) {
        fprintf(stderr, "[Error] TruthTable::cofactor: variable (%d) must be less than %d\n", variable, nVars());
        exit(-1);
    }

    uint64_t *pdata = this->data();
    uint64_t *rdata = rtt.data();
    if (variable < 6) {
        for (const auto &i : irange(nWords())) {
            uint64_t mask = 0;
            uint64_t data = pdata[i];
            if (negative) {
                mask = (data & elementary_mask[variable]) | ((data & elementary_mask[variable]) >> (1 << variable));
            } else {
                mask = (data & ~elementary_mask[variable]) | ((data & ~elementary_mask[variable]) << (1 << variable));
            }
            rdata[i] = mask;
        }
    } else {
        int nSize = nWords();
        int nMove = 1 << (variable - 6);
        int nLength = 1 << (variable - 5);
        int nSegment = nSize / nLength;
        if (negative) {
            for (const auto &s : irange(nSegment)) {
                int offset = s * nLength;
                for (const auto &i : irange(nMove)) {
                    rdata[offset + i] = rdata[offset + i + nMove] = pdata[offset + i];
                }
            }
        } else {
            for (const auto &s : irange(nSegment)) {
                int offset = s * nLength;
                for (const auto &i : irange(nMove)) {
                    rdata[offset + i] = rdata[offset + i + nMove] = pdata[offset + i + nMove];
                }
            }
        }
    }

    return rtt;
}

uint64_t TruthTable::countOne(void) {
    if (empty())
        return 0;

    uint64_t *data = this->data();
    uint64_t count = 0;
    for (const auto &i : irange(nWords())) {
        count += __builtin_popcount(data[i]);
    }
    return count;
}

bool TruthTable::hasVariable(uint32_t variable) {
    if (empty())
        return false;

    int nSize = nWords();
    uint64_t *data = this->data();

    if (variable < 6) {
        int nShift = 1 << variable;
        for (const auto &i : irange(nSize)) {
            if ((data[i] & ~elementary_mask[variable]) != ((data[i] & elementary_mask[variable]) >> nShift))
                return true;
        }
    } else {
        int nStep = (1 << (variable - 6));
        for (int k = 0; k < nSize; k += 2 * nStep) {
            for (const auto &i : irange(nStep)) {
                if (data[i] != data[i + nStep])
                    return true;
            }
            data += 2 * nStep;
        }
    }
    return false;
}

int TruthTable::supportSize(void) {
    if (empty())
        return 0;

    int nSupport = 0;
    for (const auto &i : irange(nVars())) {
        nSupport += hasVariable(i);
    }
    return nSupport;
}

int TruthTable::isAndorOr(void) {
    if (empty())
        return 0;

    int supportSize = this->supportSize();
    int onSet = this->countOne();
    int offSet = this->nBits() - onSet;
    int condition = ((uint64_t)1 << (nVars() - supportSize));
    if (onSet == condition || offSet == condition) {
        return supportSize - 1;
    }
    return 0;
}

void TruthTable::variablePartition(int nMSB, std::vector<int> &MSB, std::vector<int> &LSB) {
    if (empty())
        return;

    MSB.clear();
    LSB.clear();
    for (const auto &i : irange(nVars())) {
        if (i < nVars() - nMSB) {
            LSB.push_back(getVariable(i));
        } else {
            MSB.push_back(getVariable(i));
        }
    }
    return;
}

uint32_t TruthTable::getVariable(int place) {
    if (empty())
        return 0;

    return _data->place_to_variable[place];
}

void TruthTable::swapAdjacent(uint64_t *rdata, uint64_t *data, int variable) {
    int nSize = nWords();

    if (variable < 5) {
        int shift = 1 << variable;
        for (const auto &i : irange(nSize)) {
            rdata[i] = (data[i] & permutation_mask[variable][0]) | ((data[i] & permutation_mask[variable][1]) << shift) | ((data[i] & permutation_mask[variable][2]) >> shift);
        }
    } else if (variable == 5) {
        for (const auto &i : irange(nSize / 2)) {
            rdata[i * 2 + 0] = (data[i * 2 + 0] & 0x00000000FFFFFFFF) | ((data[i * 2 + 1] & 0x00000000FFFFFFFF) << 32);
            rdata[i * 2 + 1] = (data[i * 2 + 1] & 0xFFFFFFFF00000000) | ((data[i * 2 + 0] & 0xFFFFFFFF00000000) >> 32);
        }
    } else {
        int nMove = (1 << (variable - 6));
        for (int i = 0; i < nSize; i += 4 * nMove) {
            for (const auto &j : irange(nMove)) {
                rdata[j + nMove * 0] = data[j + nMove * 0];
                rdata[j + nMove * 1] = data[j + nMove * 2];
                rdata[j + nMove * 2] = data[j + nMove * 1];
                rdata[j + nMove * 3] = data[j + nMove * 3];
            }
            data += 4 * nMove;
            rdata += 4 * nMove;
        }
    }
}

template< typename T >
std::string int_to_hex( T i )
{
  std::stringstream stream;
  stream << "0x" 
         << std::setfill ('0') << std::setw(sizeof(T)*2) 
         << std::hex << i;
  return stream.str();
}

std::string TruthTable::hash_str(void) {
    if (empty()) {
        return "";
    }

    std::string hash_str = "";
    uint64_t *data = this->data();
    for (const auto &i : irange(nWords())) {
        hash_str += std::to_string(data[i]);
        // hash_str += int_to_hex(data[i]);
    }
    return hash_str;
}

void TruthTable::assign(uint64_t value) {
    if (empty())
        return;
    _data->data[0] = (_bits < 64) ? value << (64 - _bits) : value;
    return;
}

void TruthTable::assign(int offset, uint64_t value) {
    if (empty())
        return;
    _data->data[offset] = value;
    return;
}

void TruthTable::print(Format format) {
    if (empty()) {
        printf("Empty TruthTable\n");
        return;
    }

    if (format == Format::BIN) {
        printf("0b");
    } else if (format == Format::HEX) {
        printf("0x");
    }
    printf("%s\n", str(format).c_str());
    return;
}

void TruthTable::printReverse(Format format) {
    if (empty()) {
        printf("Empty TruthTable\n");
        return;
    }

    if (format == Format::BIN) {
        printf("0b");
    } else if (format == Format::HEX) {
        printf("0x");
    }
    printf("%s\n", strReverse(format).c_str());
    return;
}

void TruthTable::printPosition(void) {
    if (empty()) {
        printf("Empty TruthTable\n");
        return;
    }

    for (const auto &i : irange(nVars())) {
        printf("Place: %d -> Var[%ld]\n", i, _data->place_to_variable[i]);
    }
}

std::string TruthTable::str(Format format) {
    std::string str = "";
    if (format == Format::BIN) {
        for (const auto &i : irange(nBits())) {
            str += (*this)[i] ? "1" : "0";
        }
    } else if (format == Format::HEX) {
        for (const auto &i : irange(nBits() / 4)) {
            char value = 0;
            for (const auto &j : irange(4)) {
                value |= (*this)[i * 4 + j] << (3 - j);
            }
            char buf[2];
            sprintf(buf, "%X", value);
            str += buf[0];
        }
    }
    return str;
}

std::string TruthTable::strReverse(Format format) {
    std::string str;
    int bits = nBits();
    if (format == Format::BIN) {
        for (const auto &i : irange(bits)) {
            str += (*this)[bits - i - 1] ? "1" : "0";
        }
    } else if (format == Format::HEX) {
        for (const auto &i : irange(bits / 4)) {
            char value = 0;
            for (const auto &j : irange(4)) {
                value |= (*this)[bits - (i * 4 + j) - 1] << (3 - j);
            }
            char buf[2];
            sprintf(buf, "%X", value);
            str += buf[0];
        }
    }

    return str;
}

std::vector<int64_t> TruthTable::fourierTransform_rec(uint64_t begin, uint64_t end) {
    if (begin == end) {
        return {operator[](begin) ? 1 : -1};
    }

    int length = end - begin + 1;
    auto mid = begin + length / 2;
    auto left = fourierTransform_rec(begin, mid - 1);
    auto right = fourierTransform_rec(mid, end);
    std::vector<int64_t> result(length);
    for (const auto &i : irange(length / 2)) {
        result[i] = left[i] + right[i];
        result[i + length / 2] = left[i] - right[i];
    }
    return result;
}

std::vector<float> TruthTable::fourierTransform(void) {
    int bits = nBits();
    auto result = fourierTransform_rec(0, bits - 1);
    std::vector<float> result_norm(bits);

    for (const auto &i : irange(bits)) {
        result_norm[i] = (float)result[i] / bits;
    }
    return result_norm;
}

std::vector<float> TruthTable::fourierWeight(void) {
    uint64_t bits = nBits();
    auto coeffs = this->fourierTransform();
    std::vector<float> weights(nVars() + 1);

    weights[0] = std::pow(coeffs[0], 2);
    std::vector<int> index(1, 1);
    for (uint64_t i = 1; i < bits;) {
        for (const auto &j : irange(index.size())) {
            weights[index[j]] += std::pow(coeffs[i++], 2);
        }
        for (const auto &j : irange(index.size())) {
            index.push_back(index[j] + 1);
        }
    }

    return weights;
}

float TruthTable::fourierCost(void) {
    uint64_t bits = nBits();
    auto coeffs = this->fourierTransform();
    std::vector<float> weights(nVars() + 1);

    weights[0] = std::pow(coeffs[0], 2);
    std::vector<int> index(1, 1);
    for (uint64_t i = 1; i < bits;) {
        for (const auto &j : irange(index.size())) {
            weights[index[j]] += std::pow(coeffs[i++], 2);
        }
        for (const auto &j : irange(index.size())) {
            index.push_back(index[j] + 1);
        }
    }

    int sparsity_of_coeffs = 0;
    for (const auto &i : irange(nBits())) {
        sparsity_of_coeffs += coeffs[i] != 0;
    }
    int sparsity_of_weights = 0;
    for (const auto &i : irange(nVars() + 1)) {
        sparsity_of_weights += weights[i] != 0;
    }

    // ::print(weights);
    float cost = 0;
    for (const auto &i : irange(nVars() + 1)) {
        // cost += weights[i] * ((i + 1) * 3);
        cost += weights[i] * ((i) * 3);
        // cost += weights[i] * ((i));
    }
    cost += (float)sparsity_of_coeffs / sparsity_of_weights;
    return cost;
}

uint64_t reverseBits(uint64_t n) {
    uint64_t rev = 0;

    for (int i = 0; i < 64; i++)
        rev = (rev << (uint64_t)1) | ((n >> i) & (uint64_t)1);

    return rev;
}

float TruthTable::cost(void) {
    if (nVars() == 4) {
        // return func2node[reverseBits(data()[0])];
    }
    return fourierCost();
}

class Combination {
public:
    Combination(int n, int r);
    bool next(void);
    void next(int n);
    std::vector<int>& get(void);
    std::vector<int> get_reverse(void);
    std::vector<int> get_reverse(int n);
    int count(void);
    int getN(void);
    int getR(void);

private:
    int n;
    int r;
    std::vector<int> data;
};

inline Combination::Combination(int n, int r)
    : n(n), r(r), data(r) {
    for (const auto& i : irange(r)) {
        data[i] = i;
    }
}

inline std::vector<int>& Combination::get(void) {
    return data;
}

inline int Combination::getN(void) {
    return n;
}

inline int Combination::getR(void) {
    return r;
}

bool Combination::next(void) {
    for (int i = r - 1; i >= 0; i--) {
        if (data[i] < n - r + i) {
            data[i]++;
            for (int j = i + 1; j < r; j++) {
                data[j] = data[j - 1] + 1;
            }
            return true;
        }
    }
    return false;
}

void Combination::next(int n) {
    for (const auto& i : irange(n)) {
        (void)i;
        next();
    }
}

int Combination::count(void) {
    if (r > n - r) r = n - r;
    int ans = 1;

    for (const auto& i : irange(1, r + 1)) {
        ans *= n - r + i;
        ans /= i;
    }

    return ans;
}

std::vector<int> Combination::get_reverse(void) {
    std::vector<int> reverse_data = data;
    for (const auto& i : irange(r)) {
        reverse_data[i] = n - 1 - data[i];
    }
    return reverse_data;
}

std::vector<int> Combination::get_reverse(int n) {
    next(n);
    return get_reverse();
}

void doDecomposition(TruthTable tt_, int nBoundSet, std::vector<int>& supportSet, std::vector<int>& record, std::vector<std::set<std::string> >& recordCof) {
    assert(nBoundSet <= supportSet.size());
    TruthTable tt = tt_.clone();
    Combination generator(supportSet.size(), nBoundSet);

    int genIndex = 0;
    do {
        std::vector<int> combination = generator.get_reverse();
        // move bound set to MSB
        for (const auto& i : irange(nBoundSet)) {
            tt.moveTo(supportSet[combination[i]], tt.nVars() - i - 1);
        }
        std::vector<TruthTable> cofactors;
        std::vector<TruthTable> boundSetFunctions;
        int nCofactors = tt.countCofactor(nBoundSet, cofactors, boundSetFunctions, true);
        for (auto& cofactor : cofactors) {
            recordCof[genIndex].insert(cofactor.hash_str());
            recordCof[genIndex].insert((~cofactor).hash_str());
        }
        record[genIndex++] += nCofactors;
    } while (generator.next());
}

class DecisionDiagram;

class DecisionNode {
    friend class DecisionDiagram;

public:
    DecisionNode();
    void buildWithDecisionVariable(DecisionDiagram* mgr, int decisionVariable, bool shared = true, int fInv = 0);

public:
    TruthTable& getTruthTable(void);

private:
    static std::vector<float> computeEntropyCost(DecisionDiagram* mgr, TruthTable& tt, std::set<int>& invalid_variables);
    std::set<int> getInvalidVariables(DecisionDiagram* mgr, std::vector<int>& available_variables);

private:
    int decisionVariable;
    TruthTable tt;
    int left;
    int right;
};

inline DecisionNode::DecisionNode()
    : decisionVariable(-1), left(-1), right(-1) {
}

inline TruthTable& DecisionNode::getTruthTable(void) {
    return tt;
}

class DecisionDiagram {
    friend class DecisionNode;

public:
    DecisionDiagram();

public:
    unsigned randomInt(int fReset);
    unsigned randomNum(int nSeed);
    void addOutput(TruthTable& tt);

    void build(void);
    void buildWithDecisionVariable(int node_id, int variable, std::set<int>& newWaitingNodes, int fInv = 0);
    void buildOneCluster(std::vector<int>& cluster);
    std::vector<std::vector<int> > buildClusters(std::vector<int> waitingNodes);
    std::vector<int> computeSupportSet(std::vector<int>& nodes);
    std::vector<int> buildWithTheseSupportWithEntropyAndFourier(std::vector<int>& waitingNodes, std::set<int>& supportSet);

private:
    void init(int nVars);
    DecisionNode& getNode(int id) {
        return node_pool[id];
    }
    void prepareSpace(void);
    int newNode(void);
    int newNode(TruthTable& tt, bool shared = true, int fInv = 0);
    int const0Node(void);
    int const1Node(void);
    float getEntropyCost(TruthTable& tt);
    float getFourierCost(TruthTable& tt);

public:
    void writeVerilog(const char* filename);
    void buildAig(Gia_Man_t *pAig);

private:
    void topoRec(int node, std::set<int>& visited, std::vector<int>& nodes);
    void topoSort(int root, std::vector<int>& nodes);

private:
    void printRec(int node, int space);

public:
    void print(void);
    int nVars(void);
    int nDecomp(void);
    int nNodeAllocated(void) { return _num_node_allocated; }

private:
    int _nVars;
    int _nDecomp;
    int const0;
    int _num_node_allocated;
    std::vector<DecisionNode> node_pool;
    std::vector<int> roots;
    std::unordered_map<std::string, int> hash2node;
    std::unordered_map<std::string, float> hash2cost;
    std::vector<int> sortedNodes;
};

inline DecisionDiagram::DecisionDiagram()
    : _nVars(0), _nDecomp(0), const0(0), _num_node_allocated(0) {
    randomNum(1);
}

inline int DecisionDiagram::nVars(void) {
    return _nVars;
}

inline int DecisionDiagram::nDecomp(void) {
    return _nDecomp;
}

inline int DecisionDiagram::const0Node(void) {
    return const0;
}
inline int DecisionDiagram::const1Node(void) {
    return LitNot(const0);
}

void DecisionDiagram::init(int nVars) {
    _nVars = nVars;
    const0 = newNode();
    getNode(LitToId(const0)).decisionVariable = 0;
    getNode(LitToId(const0)).right = -1;
    getNode(LitToId(const0)).left = -1;
    getNode(LitToId(const0)).tt = TruthTable(((uint64_t)1 << nVars));
    hash2node[getNode(LitToId(const0)).getTruthTable().hash_str()] = const0;
    hash2node[(~(getNode(LitToId(const0)).getTruthTable())).hash_str()] = LitNot(const0);
}

void DecisionDiagram::prepareSpace(void) {
    if (_num_node_allocated + 2 > node_pool.size() / 2) {
        // printf("\n\nPrepare node pool\n\n");
        node_pool.resize(node_pool.size() * 2);
    }
}

int DecisionDiagram::newNode(void) {
    if (_num_node_allocated > node_pool.size() / 2) {
        // printf("\n\nResizing node pool\n\n");
        node_pool.resize(node_pool.size() * 2);
    }

    // printf("\n\nNEW NODE Allocating node %d\n\n", _num_node_allocated);

    return IdToLit(_num_node_allocated++, false);
}

int DecisionDiagram::newNode(TruthTable& tt, bool shared, int fInv) {
    (void)shared;
    std::string hash_pos = tt.hash_str();
    auto iter = hash2node.begin();
    if ((iter = hash2node.find(hash_pos)) != hash2node.end()) {
        return iter->second;
    }

    int new_node = newNode();
    // printf("New node %d for TT ", LitToId(new_node));
    // tt.print(TruthTable::Format::BIN);

    if (fInv && tt.countOne() > tt.nBits() / 2) {
        hash2node[hash_pos] = LitNot(new_node);
        hash2node[(~tt).hash_str()] = new_node;
        getNode(LitToId(new_node)).tt = ~tt;
        return LitNot(new_node);
    } else {
        hash2node[hash_pos] = new_node;
        hash2node[(~tt).hash_str()] = LitNot(new_node);
        getNode(LitToId(new_node)).tt = tt;
        return new_node;
    }
    return const0;
}

void DecisionDiagram::addOutput(TruthTable& tt) {
    if (node_pool.empty()) {
        node_pool.resize((uint64_t)1 << tt.nVars());
        this->init(tt.nVars());
    }
    roots.emplace_back(newNode(tt));
}

unsigned DecisionDiagram::randomInt(int fReset) {
    static unsigned int m_z = 3716960521u;
    static unsigned int m_w = 2174103536u;
    if (fReset) {
        m_z = 3716960521u;
        m_w = 2174103536u;
    }
    m_z = 36969 * (m_z & 65535) + (m_z >> 16);
    m_w = 18000 * (m_w & 65535) + (m_w >> 16);
    return (m_z << 16) + m_w;
}

unsigned DecisionDiagram::randomNum(int Seed) {
    static unsigned RandMask = 0;
    if (Seed == 0)
        return RandMask ^ randomInt(0);
    RandMask = randomInt(1);
    for (int i = 0; i < Seed; i++)
        RandMask = randomInt(0);
    return RandMask;
}

float DecisionDiagram::getFourierCost(TruthTable& tt) {
    std::string hash_str = tt.hash_str();
    std::string neg_hash_str = (~tt).hash_str();
    if (hash2node.find(hash_str) != hash2node.end()) {
        return 0;
    } else if (hash2node.find(neg_hash_str) != hash2node.end()) {
        return 0;
    }
    auto iter = hash2cost.begin();
    if ((iter = hash2cost.find(hash_str)) != hash2cost.end()) {
        return iter->second;
    } else if ((iter = hash2cost.find(neg_hash_str)) != hash2cost.end()) {
        return iter->second;
    }

    return hash2cost[hash_str] = tt.fourierCost();
}

float DecisionDiagram::getEntropyCost(TruthTable& tt) {
    int out1 = tt.countOne();
    float p1 = (float)out1 / tt.nBits();
    float p0 = 1 - p1;
    float entropy = -(((p0 != 0) ? p0 * log2(p0) : 0) + ((p1 != 0) ? p1 * log2(p1) : 0));

    return entropy;
}

std::set<int> getInvalidVariables(DecisionDiagram* mgr, std::vector<int>& available_variables) {
    std::vector<int> all_variable(mgr->nVars());
    std::iota(all_variable.begin(), all_variable.end(), 0);
    std::set<int> all_variable_set(all_variable.begin(), all_variable.end());
    std::set<int> invalid_variables;
    std::set_difference(all_variable_set.begin(), all_variable_set.end(), available_variables.begin(), available_variables.end(), std::inserter(invalid_variables, invalid_variables.begin()));

    return invalid_variables;
}

std::vector<float> DecisionNode::computeEntropyCost(DecisionDiagram* mgr, TruthTable& tt, std::set<int>& invalid_variables) {
    (void)mgr;
    float oriInfo = mgr->getEntropyCost(tt);

    std::vector<float> costs(tt.nVars(), 1024);
    for (const auto& i : irange(tt.nVars())) {
        if (invalid_variables.count(i)) continue;
        auto cofactor0 = tt.cofactor(i, 1);
        auto cofactor1 = tt.cofactor(i, 0);
        if (cofactor0 == tt || cofactor1 == tt) {
            continue;
        }
        int out1_0 = cofactor0.countOne();
        int out0_0 = cofactor0.nBits() - out1_0;
        int out1_1 = cofactor1.countOne();
        int out0_1 = cofactor1.nBits() - out1_1;
        float p1_0 = (float)out1_0 / (out1_0 + out0_0 + 1e-8);
        float p0_0 = (float)out0_0 / (out1_0 + out0_0 + 1e-8);
        float p1_1 = (float)out1_1 / (out1_1 + out0_1 + 1e-8);
        float p0_1 = (float)out0_1 / (out1_1 + out0_1 + 1e-8);
        int n0 = out1_0 + out0_0;
        int n1 = out1_1 + out0_1;
        int nAll = n0 + n1;
        float info0 = ((float)n0 / nAll) * -(((p0_0 != 0) ? p0_0 * log2(p0_0) : 0) + ((p1_0 != 0) ? p1_0 * log2(p1_0) : 0));
        float info1 = ((float)n1 / nAll) * -(((p0_1 != 0) ? p0_1 * log2(p0_1) : 0) + ((p1_1 != 0) ? p1_1 * log2(p1_1) : 0));
        // printf("Decision variable: %d\n", i);
        // printf("Ori: %f, Info0: %f, Info1: %f\n", oriInfo, info0, info1);
        // printf("p0_0: %f, p1_0: %f, p0_1: %f, p1_1: %f\n", p0_0, p1_0, p0_1, p1_1);
        costs[i] = -(oriInfo - info0 - info1);
    }

    return costs;
}

double jaccardSimilarity(const std::unordered_set<int>& a, const std::unordered_set<int>& b) {
    std::unordered_set<int> intersection, unionSet = a;
    for (int num : b) {
        if (a.count(num)) intersection.insert(num);
        unionSet.insert(num);
    }
    return (double)intersection.size() / unionSet.size();
}

std::vector<std::vector<int> > autoClusterIndex(std::vector<std::vector<int> >& sequences, double threshold = 0.95) {
    int n = sequences.size();
    std::vector<std::unordered_set<int> > sets(n);

    for (int i = 0; i < n; i++) {
        sets[i] = std::unordered_set<int>(sequences[i].begin(), sequences[i].end());
    }

    std::vector<std::vector<int> > graph(n);
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            if (jaccardSimilarity(sets[i], sets[j]) >= threshold) {
                graph[i].push_back(j);
                graph[j].push_back(i);
            }
        }
    }

    std::vector<bool> visited(n, false);
    std::vector<std::vector<int> > clusters;

    std::function<void(int, std::vector<int>&)> dfs = [&](int node, std::vector<int>& cluster) {
        visited[node] = true;
        cluster.push_back(node);
        for (int neighbor : graph[node]) {
            if (!visited[neighbor]) {
                dfs(neighbor, cluster);
            }
        }
    };

    for (int i = 0; i < n; i++) {
        if (!visited[i]) {
            std::vector<int> cluster;
            dfs(i, cluster);
            clusters.push_back(cluster);
        }
    }

    return clusters;
}

std::vector<std::vector<int> > DecisionDiagram::buildClusters(std::vector<int> waitingNodes) {
    int nVars = getNode(waitingNodes[0]).getTruthTable().nVars();
    // compute support set
    std::set<int> supportSet;
    std::vector<int> supportCount(nVars, 0);
    std::vector<std::vector<int> > supportSetVec(waitingNodes.size());
    for (const auto& i : irange(waitingNodes.size())) {
        auto& node = getNode(waitingNodes[i]);
        for (const auto& var : irange(nVars)) {
            if (node.getTruthTable().hasVariable(var)) {
                supportSet.insert(var);
                supportCount[var]++;
                supportSetVec[i].push_back(var);
            }
        }
    }

    auto clustersIndex = autoClusterIndex(supportSetVec);
    std::vector<std::vector<int> > clusters;
    for (const auto& cluster : clustersIndex) {
        std::vector<int> newCluster;
        for (const auto& index : cluster) {
            if (waitingNodes[index] == LitToId(const0Node())) { // FIX
                continue;
            }
            newCluster.push_back(waitingNodes[index]);
        }
        if (newCluster.empty()) { // FIX
            continue;
        }
        clusters.push_back(newCluster);
    }

    return clusters;
}

void DecisionNode::buildWithDecisionVariable(DecisionDiagram* mgr, int decisionVariable, bool shared, int fInv) {
    auto& tt = this->tt;
    // terminate condition
    if (this->left != -1 || this->right != -1) {
        return;
    }

    // set the decision variable and calculate the cofactor
    // printf("  with decision variable %d\n", decisionVariable);
    this->decisionVariable = decisionVariable;
    auto ltt = tt.cofactor(decisionVariable, 0);
    auto rtt = tt.cofactor(decisionVariable, 1);
    // printf("  left: "); ltt.print(TruthTable::Format::BIN);
    // printf("  right: "); rtt.print(TruthTable::Format::BIN);
    if (tt == rtt || tt == ltt) {
        return;
    }

    // build the left and right child
    left = mgr->newNode(ltt, shared, fInv);
    right = mgr->newNode(rtt, shared, fInv);
    // printf("  left id: %d, right id: %d\n", LitToId(left), LitToId(right));
    // printf("  left check: "); if (LitToId(left) != 0) { mgr->getNode(LitToId(left)).getTruthTable().print(TruthTable::Format::BIN); } else { printf("NULL\n"); }
    // printf("  right check: "); if (LitToId(right) != 0) { mgr->getNode(LitToId(right)).getTruthTable().print(TruthTable::Format::BIN); } else { printf("NULL\n"); }
}

void DecisionDiagram::buildWithDecisionVariable(int node_id, int variable, std::set<int>& newWaitingNodes, int fInv) {
    prepareSpace();
    auto& node = getNode(node_id);
    if (node.left != -1 || node.right != -1) {
        return;
    }
    // printf("Build node %d: ", node_id); node.getTruthTable().print(TruthTable::Format::BIN);
    node.buildWithDecisionVariable(this, variable, true, fInv);
    if (node.left == -1 && node.right == -1) {
        newWaitingNodes.insert(node_id);
        return;
    }
    if (!fInv) {
        if (!LitIsComplement(node.left) && (node.left != const0Node())) {
            // printf("Insert left node id %d\n", LitToId(node.left));
            newWaitingNodes.insert(LitToId(node.left));
        }
        if (!LitIsComplement(node.right) && (node.right != const0Node())) {
            // printf("Insert right node id %d\n", LitToId(node.right));
            newWaitingNodes.insert(LitToId(node.right));
        }
    } else {
        if (node.left != const0Node() && node.left != const1Node()) {
            newWaitingNodes.insert(LitToId(node.left));
        }
        if (node.right != const0Node() && node.right != const1Node()) {
            newWaitingNodes.insert(LitToId(node.right));
        }
    }

    // printf("  newWaitingNodes: \n");
    // for (const auto& n : newWaitingNodes) {
    //     printf("%d ", n);
    //     getNode(n).getTruthTable().print(TruthTable::Format::BIN);
    // }
    // printf("\n");
}

std::vector<int> DecisionDiagram::computeSupportSet(std::vector<int>& nodes) {
    std::set<int> supportSet;
    for (const auto& node_id : nodes) {
        auto& node = getNode(node_id);
        for (const auto& var : irange(node.getTruthTable().nVars())) {
            if (node.getTruthTable().hasVariable(var)) {
                supportSet.insert(var);
            }
        }
    }
    return std::vector<int>(supportSet.begin(), supportSet.end());
}

template<typename T>
float min(std::vector<T>& array) {
    return *std::min_element(array.begin(), array.end());
}

void DecisionDiagram::build(void) {
    std::vector<int> trueNodeIds;
    for (const auto& root : roots) {
        int root_id = LitToId(root);
        if (std::find(trueNodeIds.begin(), trueNodeIds.end(), root) == trueNodeIds.end())
            trueNodeIds.emplace_back(root_id);
    }
    std::vector<int> waitingNodes = trueNodeIds;

    auto clusters = buildClusters(waitingNodes);
    for (auto& cluster : clusters) {
        // printf("cluster: ");
        // for (auto& c : cluster) {
        //     printf("%d ", c);
        // }
        // printf("\n");
        buildOneCluster(cluster);
    }

    // topo sort
    std::set<int> visited;
    for (const auto& root : roots) {
        this->topoRec(LitToId(root), visited, this->sortedNodes);
    }
}

std::vector<int> DecisionDiagram::buildWithTheseSupportWithEntropyAndFourier(std::vector<int>& waitingNodes, std::set<int>& supportSet) {
    int nVars = getNode(waitingNodes[0]).getTruthTable().nVars();
    std::set<int> invalid_variables;
    for (const auto& i : irange(nVars)) {
        if (supportSet.find(i) == supportSet.end()) {
            invalid_variables.insert(i);
        }
    }
    while (!waitingNodes.empty() && !supportSet.empty()) {
        // compute gain
        std::vector<float> costs(nVars, 1024);
        for (const auto& nodeId : waitingNodes) {
            auto& node = getNode(nodeId);
            auto cost = DecisionNode::computeEntropyCost(this, node.getTruthTable(), invalid_variables);
            // ::print(cost);
            for (const auto& i : irange(nVars)) {
                costs[i] += (cost[i] == 1024) ? 0 : cost[i];
            }
        }

        // find decision variable
        std::vector<int> decisionSet;
        int decisionVariable = std::distance(costs.begin(), std::min_element(costs.begin(), costs.end()));
        float decisionCost = costs[decisionVariable];
        for (const auto& i : irange(nVars)) {
            if (costs[i] == decisionCost && !invalid_variables.count(i)) {
                decisionSet.push_back(i);
            }
        }
        if (min(costs) == 1024) {
            decisionVariable = *supportSet.begin();
        }
        if (decisionSet.size() > 1) {
            std::vector<float> fouerierCost(decisionSet.size(), 0);
            for (const auto& nodeId : waitingNodes) {
                auto& node = getNode(nodeId);
                std::vector<float> cost(decisionSet.size(), 8192);
                for (const auto& i : irange(decisionSet.size())) {
                    if (invalid_variables.find(decisionSet[i]) != invalid_variables.end()) continue;
                    // consider two childs
                    auto cofactor0 = node.getTruthTable().cofactor(decisionSet[i], 1);
                    auto cofactor1 = node.getTruthTable().cofactor(decisionSet[i], 0);
                    if (cofactor0 == node.getTruthTable() || cofactor1 == node.getTruthTable()) {
                        continue;
                    }
                    cost[i] = getFourierCost(cofactor0) + getFourierCost(cofactor1);
                }
                for (const auto& i : irange(decisionSet.size())) {
                    fouerierCost[i] += cost[i];
                }
            }
            int decisionIndex = std::distance(fouerierCost.begin(), std::min_element(fouerierCost.begin(), fouerierCost.end()));
            decisionVariable = decisionSet[decisionIndex];
        }
        std::set<int> new_waiting_nodes;
        for (const auto& nodeId : waitingNodes) {
            buildWithDecisionVariable(nodeId, decisionVariable, new_waiting_nodes);
        }
        waitingNodes = std::vector<int>(new_waiting_nodes.begin(), new_waiting_nodes.end());
        invalid_variables.insert(decisionVariable);
        supportSet.erase(decisionVariable);
    }
    return waitingNodes;
}

void DecisionDiagram::buildOneCluster(std::vector<int>& cluster) {
    int enableFourier = 1;
    int enableDecompose = 1;

    std::vector<int> waiting_nodes = cluster;

    int nVars = getNode(cluster[0]).getTruthTable().nVars();
    while (!waiting_nodes.empty()) {
        // printf("=========================\n");
        // printf("construct nodes: \n");
        // for (auto node : waiting_nodes) {
        //     printf("Node %d: ", node);
        //     getNode(node).getTruthTable().print(TruthTable::Format::BIN);
        // }
        // printf("-------------------------\n");
        // compute support set
        std::vector<int> supportSet = computeSupportSet(waiting_nodes);
        std::set<int> invalid_variables = getInvalidVariables(this, supportSet);
        // printf("Support set: ");
        // for (const auto& var : supportSet) {
        //     printf("%d ", var);
        // }
        // printf("\n");
        // printf("Invalid set: ");
        // for (const auto& var : invalid_variables) {
        //     printf("%d ", var);
        // }
        // printf("\n");

        // compute multi-output decomposition
        // if the multi-output decomposition exist, then build the nodes
        int nBoundSet = std::max(2, std::min(4, (int)supportSet.size()));
        if (supportSet.size() > nBoundSet && enableDecompose) {
            // printf("Try to decompose with bound set size %d\n", nBoundSet);
            std::vector<int> record(Combination(supportSet.size(), nBoundSet).count(), 0);
            std::vector<std::set<std::string> > recordCofoactor(Combination(supportSet.size(), nBoundSet).count());
            for (const auto& nodeIndex : waiting_nodes) {
                auto& node = getNode(nodeIndex);
                doDecomposition(node.getTruthTable(), nBoundSet, supportSet, record, recordCofoactor);
            }
            auto record_copy = record;
            for (const auto& i : irange(recordCofoactor.size())) {
                record[i] = recordCofoactor[i].size();
            }
            int minRecord = *std::min_element(record.begin(), record.end());
            if (minRecord < (1 << nBoundSet) * 3 / 4) {
                std::vector<int> minRecordIndex;
                std::vector<int> ref;
                for (const auto& i : irange(record.size())) {
                    if (record[i] == minRecord) {
                        minRecordIndex.push_back(i);
                        ref.push_back(record_copy[i]);
                    }
                }
                std::set<int> unionSet;
                for (const auto& index : minRecordIndex) {
                    auto comb = Combination(supportSet.size(), nBoundSet).get_reverse(index);
                    for (const auto& i : comb) {
                        unionSet.insert(supportSet[i]);
                    }
                }
                if (unionSet.size() == nBoundSet && min(ref) > nBoundSet) {
                    waiting_nodes = buildWithTheseSupportWithEntropyAndFourier(waiting_nodes, unionSet);
                    continue;
                }
                supportSet = std::vector<int>(unionSet.begin(), unionSet.end());
            }
        }

        int decisionVariable = 0;
        // compute gain
        std::vector<float> costs(nVars, 1024);
        for (const auto& nodeId : waiting_nodes) {
            auto& node = getNode(nodeId);
            auto cost = DecisionNode::computeEntropyCost(this, node.getTruthTable(), invalid_variables);
            for (const auto& i : irange(nVars)) {
                costs[i] += (cost[i] == 1024) ? 0 : cost[i];
            }
        }
        // printf("Costs: ");
        // for (const auto& cost : costs) {
        //     printf("%f ", cost);
        // }
        // printf("\n");

        // find decision variable
        std::vector<int> decisionSet;
        decisionVariable = std::distance(costs.begin(), std::min_element(costs.begin(), costs.end()));
        float decisionCost = costs[decisionVariable];
        for (const auto& i : irange(nVars)) {
            if (costs[i] == decisionCost && !invalid_variables.count(i)) {
                decisionSet.push_back(i);
            }
        }
        if (min(costs) == 1024) {
            decisionVariable = supportSet[0];
        }
        // printf("First decision variable: %d\n", decisionVariable);
        if (decisionSet.size() > 1 && enableFourier) {
            std::vector<float> fouerierCost(decisionSet.size(), 0);
            for (const auto& nodeId : waiting_nodes) {
                auto& node = getNode(nodeId);
                std::vector<float> cost(decisionSet.size(), 8192);
                for (const auto& i : irange(decisionSet.size())) {
                    if (invalid_variables.find(decisionSet[i]) != invalid_variables.end()) continue;
                    // consider two childs
                    auto cofactor0 = node.getTruthTable().cofactor(decisionSet[i], 1);
                    auto cofactor1 = node.getTruthTable().cofactor(decisionSet[i], 0);
                    if (cofactor0 == node.getTruthTable() || cofactor1 == node.getTruthTable()) {
                        continue;
                    }
                    cost[i] = getFourierCost(cofactor0) + getFourierCost(cofactor1);
                }
                for (const auto& i : irange(decisionSet.size())) {
                    fouerierCost[i] += cost[i];
                }
            }
            int decisionIndex = std::distance(fouerierCost.begin(), std::min_element(fouerierCost.begin(), fouerierCost.end()));
            decisionVariable = decisionSet[decisionIndex];
            // printf("Second decision variable: %d\n", decisionVariable);
        }

        std::set<int> next_waiting_nodes;
        for (const auto& nodeId : waiting_nodes) {
            buildWithDecisionVariable(nodeId, decisionVariable, next_waiting_nodes, 0);

            // printf("Check every nodes:\n");
            // for (int i = 0; i < _num_node_allocated; i++) {
            //     printf("Node id %d: left %d right %d\n", i, getNode(i).left, getNode(i).right);
            //     getNode(i).getTruthTable().print(TruthTable::Format::BIN);
            // }
            // printf("\n");

        }
        // for (auto next_node : next_waiting_nodes) {
        //     printf("Next waiting node: ");
        //     getNode(next_node).getTruthTable().print(TruthTable::Format::BIN);
        // }

        waiting_nodes = std::vector<int>(next_waiting_nodes.begin(), next_waiting_nodes.end());
        // printf("=========================\n\n");
    }
}

void DecisionDiagram::topoRec(int node, std::set<int>& visited, std::vector<int>& nodes) {
    if (visited.find(node) != visited.end() || node == const0) {
        return;
    }
    visited.insert(node);
    if (getNode(node).left != -1) {
        topoRec(LitToId(getNode(node).left), visited, nodes);
    }
    if (getNode(node).right != -1) {
        topoRec(LitToId(getNode(node).right), visited, nodes);
    }
    nodes.push_back(node);
}

void DecisionDiagram::topoSort(int root, std::vector<int>& nodes) {
    std::set<int> visited;
    topoRec(root, visited, nodes);
}

void DecisionDiagram::printRec(int root_, int space) {
    int root = LitToId(root_);
    bool is_complement = LitIsComplement(root_);
    // Base case
    if (root == const0)
        return;

    // Increase distance between levels
    space += 11;

    // Process right child first
    if (getNode(root).right == -1) return;
    printRec(getNode(root).right, space);

    // Print current node after space
    printf("\n");
    for (int i = 11; i < space; i++)
        printf(" ");
    if (root == const0Node()) {
        if (is_complement) {
            printf("CONST1\n");
        } else {
            printf("CONST0\n");
        }
    } else {
        printf("%sMUX[%2d](%2d)\n", (is_complement) ? "~" : "", getNode(root).decisionVariable, root);
    }

    // Process left child
    if (getNode(root).left == root) return;
    printRec(getNode(root).left, space);
}

void DecisionDiagram::print(void) {
    // Pass initial space count as 0
    for (const auto& root : roots)
        printRec(root, 0);
}

void DecisionDiagram::writeVerilog(const char* filename) {
    if (roots.size() == 0) {
        printf("[ERROR] Empty network\n");
        return;
    }
    FILE* f = fopen(filename, "w");
    if (f == NULL) {
        printf("[ERROR] Cannot open file %s\n", filename);
        return;
    }
    fprintf(f, "module decision_diagram(");
    for (const auto& i : irange(getNode(LitToId(roots[0])).tt.nVars())) {
        fprintf(f, "in_%u, ", i);
    }
    for (const auto& i : irange(roots.size() - 1)) {
        fprintf(f, "output_%lu, ", i);
    }
    fprintf(f, "output_%zu);\n", roots.size() - 1);
    for (const auto& i : irange(getNode(LitToId(roots[0])).tt.nVars())) {
        fprintf(f, "input in_%d;\n", i);
    }
    for (const auto& i : irange(roots.size())) {
        fprintf(f, "output output_%lu;\n", i);
    }
    fprintf(f, "wire node_%d = 0;\n", const0);
    for (const auto& node : sortedNodes) {
        fprintf(f, "wire node_%d;\n", node);
    }

    for (const auto& node : sortedNodes) {
        std::string decisionVariable = "in_" + std::to_string(getNode(node).decisionVariable);

        if (getNode(node).left == -1 || getNode(node).right == -1) continue;

        int lhs = LitToId(getNode(node).left);
        bool is_lhs_const = (lhs == const0);
        bool is_lhs_complement = LitIsComplement(getNode(node).left);
        int rhs = LitToId(getNode(node).right);
        bool is_rhs_const = (rhs == const0);
        bool is_rhs_complement = LitIsComplement(getNode(node).right);
        if (is_lhs_const && !is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            fprintf(f, "assign node_%d = 0;\n", node);
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && is_rhs_complement) {
            fprintf(f, "assign node_%d = 1;\n", node);
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            fprintf(f, "assign node_%d = %s;\n", node, decisionVariable.c_str());
        } else if (is_lhs_const && !is_lhs_complement && is_rhs_const && is_rhs_complement) {
            fprintf(f, "assign node_%d = ~%s;\n", node, decisionVariable.c_str());
        } else if (!is_lhs_const && is_rhs_const && !is_rhs_complement) {
            fprintf(f, "assign node_%d = %s & %snode_%d;\n", node, decisionVariable.c_str(), (is_lhs_complement) ? "~" : "", lhs);
        } else if (!is_rhs_const && is_lhs_const && !is_lhs_complement) {
            fprintf(f, "assign node_%d = ~%s & %snode_%d;\n", node, decisionVariable.c_str(), (is_rhs_complement) ? "~" : "", rhs);
        } else if (is_lhs_const && is_lhs_complement && !is_rhs_const) {
            fprintf(f, "assign node_%d = %s | %snode_%d;\n", node, decisionVariable.c_str(), (is_rhs_complement) ? "~" : "", rhs);
        } else if (is_rhs_const && is_rhs_complement && !is_lhs_const) {
            fprintf(f, "assign node_%d = ~%s | %snode_%d;\n", node, decisionVariable.c_str(), (is_lhs_complement) ? "~" : "", lhs);
        } else {
            fprintf(f, "assign node_%d = (%s) ? %snode_%d : %snode_%d;\n", node, decisionVariable.c_str(), (is_lhs_complement) ? "~" : "", lhs, (is_rhs_complement) ? "~" : "", rhs);
        }
    }

    for (const auto& i : irange(roots.size())) {
        int root = LitToId(roots[i]);
        bool is_complement = LitIsComplement(roots[i]);
        fprintf(f, "assign output_%lu = %snode_%d;\n", i, (is_complement) ? "~" : "", root);
    }

    fprintf(f, "endmodule\n");
    fclose(f);
}

void DecisionDiagram::buildAig(Gia_Man_t *pAig) {
    if (roots.size() == 0) {
        printf("[ERROR] Empty network\n");
        return;
    }

    std::vector<int> copy(sortedNodes.size() + 1, -1);
    copy[const0] = Gia_ManConst0Lit();
    for (const auto& node : sortedNodes) {
        // printf("node id %d: left %d right %d\n", node, getNode(node).left, getNode(node).right);
        if (getNode(node).left == -1 || getNode(node).right == -1) continue;

        int lhs = LitToId(getNode(node).left);
        bool is_lhs_const = (lhs == const0);
        bool is_lhs_complement = LitIsComplement(getNode(node).left);
        int rhs = LitToId(getNode(node).right);
        bool is_rhs_const = (rhs == const0);
        bool is_rhs_complement = LitIsComplement(getNode(node).right);
        // printf("lhs: %s%d rhs: %s%d\n", (is_lhs_complement) ? "~" : "", lhs, (is_rhs_complement) ? "~" : "", rhs);
        if (is_lhs_const && !is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManConst0Lit();
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && is_rhs_complement) {
            copy[node] = Gia_ManConst1Lit();
        } else if (is_lhs_const && is_lhs_complement && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManCiLit(pAig, getNode(node).decisionVariable);
        } else if (is_lhs_const && !is_lhs_complement && is_rhs_const && is_rhs_complement) {
            copy[node] = LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable));
        } else if (!is_lhs_const && is_rhs_const && !is_rhs_complement) {
            copy[node] = Gia_ManHashAnd(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[lhs], is_lhs_complement));
        } else if (!is_rhs_const && is_lhs_const && !is_lhs_complement) {
            copy[node] = Gia_ManHashAnd(pAig, LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable)), LitNotCond(copy[rhs], is_rhs_complement));
        } else if (is_lhs_const && is_lhs_complement && !is_rhs_const) {
            copy[node] = Gia_ManHashOr(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[rhs], is_rhs_complement));
        } else if (is_rhs_const && is_rhs_complement && !is_lhs_const) {
            copy[node] = Gia_ManHashOr(pAig, LitNot(Gia_ManCiLit(pAig, getNode(node).decisionVariable)), LitNotCond(copy[lhs], is_lhs_complement));
        } else {
            copy[node] = Gia_ManHashMux(pAig, Gia_ManCiLit(pAig, getNode(node).decisionVariable), LitNotCond(copy[lhs], is_lhs_complement), LitNotCond(copy[rhs], is_rhs_complement));
        }
    }

    for (const auto& i : irange(roots.size())) {
        int root_id = LitToId(roots[i]);
        bool is_complement = LitIsComplement(roots[i]);
        Gia_ManAppendCo(pAig, LitNotCond(copy[root_id], is_complement));
    }
}

} // namespace DecGraph

Gia_Man_t* Gia_ManDecGraph(Gia_Man_t* p) {
    int nIns = Gia_ManCiNum(p);
    int nOuts = Gia_ManCoNum(p);
    Gia_Man_t* pNew;
    Gia_Obj_t* pObj;
    word v;
    word* pTruth;
    int i, k;
    Gia_ManLevelNum(p);
    pNew = Gia_ManStart(Gia_ManObjNum(p));
    pNew->pName = Abc_UtilStrsav(p->pName);
    pNew->pSpec = Abc_UtilStrsav(p->pSpec);
    Gia_ManForEachCi(p, pObj, k)
        Gia_ManAppendCi(pNew);
    Gia_ObjComputeTruthTableStart(p, nIns);
    Gia_ManHashStart(pNew);
    DecGraph::DecisionDiagram dd;
    for (k = 0; k < nOuts; k++) {
        DecGraph::TruthTable tt;
        tt.create(1lu << nIns);
        int num_words = tt.nWords();
        pObj = Gia_ManCo(p, k);
        pTruth = Gia_ObjComputeTruthTable(p, Gia_ObjFanin0(pObj));
        if (nIns >= 6) {
            for (i = num_words - 1; i >= 0; --i) {
                tt.data()[i] = Gia_ObjFaninC0(pObj) ? ~DecGraph::reverseBits(pTruth[i]) : DecGraph::reverseBits(pTruth[i]);
            }
        } else {
            v = DecGraph::reverseBits((Gia_ObjFaninC0(pObj) ? ~pTruth[0] : pTruth[0]) & DecGraph::ones_mask[nIns]);
            tt.data()[0] = v;
        }
        dd.addOutput(tt);
    }
    dd.build();
    dd.buildAig(pNew);
    Gia_ObjComputeTruthTableStop(p);
    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew, Gia_ManRegNum(p));
    return pNew;
}

Gia_Man_t* Gia_ManDecGraphFromFile(char* pFileName) {
    char* pBuffer = Extra_FileReadContents(pFileName);

    char *table = strtok(pBuffer, " \r\n\t|");
    DecGraph::DecisionDiagram dd;
    while (table) {
        if (strlen(table) == 0) {
            break;
        }
        DecGraph::TruthTable tt;
        tt.readBinaryReverse(table);
        dd.addOutput(tt);
        table = strtok(NULL, " \r\n\t|");
    }

    free(pBuffer);

    dd.build();

    Gia_Man_t* pNew = Gia_ManStart(dd.nNodeAllocated());
    pNew->pName = Abc_UtilStrsav("top");
    for (int i = 0; i < dd.nVars(); ++i)
        Gia_ManAppendCi(pNew);
    Gia_ManHashStart(pNew);

    dd.buildAig(pNew);
    return pNew;
}

ABC_NAMESPACE_IMPL_END
