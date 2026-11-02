#include "misc/hash/hashPtr.h"
#include "misc/hash/hashInt.h"
#include "misc/hash/hashFlt.h"
#include "misc/hash/hashGen.h"
#define CHECK(Kind) do { \
    Hash_##Kind##_t table = {0}, *p = &table; \
    Hash_##Kind##_Entry_t entries[3] = {{0}}, *e; \
    int bin, count = 0; \
    table.nBins = 4; \
    table.pArray = calloc(4, sizeof(*table.pArray)); \
    Hash_##Kind##ForEachEntry(p, e, bin) count++; \
    if (count) return 1; \
    table.pArray[0] = entries; \
    entries[0].pNext = entries + 1; \
    table.pArray[3] = entries + 2; \
    Hash_##Kind##ForEachEntry(p, e, bin) { \
        if (e != entries + count++) return 2; \
        continue; \
    } \
    if (count != 3) return 3; \
    count = 0; \
    Hash_##Kind##ForEachEntry(p, e, bin) { count++; break; } \
    if (count != 1) return 4; \
    free(table.pArray); \
} while (0)
int main(void)
{
    CHECK(Ptr); CHECK(Int); CHECK(Flt); CHECK(Gen);
    puts("PASS: Issue #30");
    return 0;
}
