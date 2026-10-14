#include "misc/extra/extra.h"
int main(int argc, char **argv)
{
    Extra_FileReader_t *p = Extra_FileReaderAlloc(argv[1], "#", "\n", " \t");
    if (argc == 3) { if (p) { Extra_FileReaderFree(p); return 1; } }
    else { if (!p) return 2; if (Extra_FileReaderGetFileSize(p) != 64) return 3; Extra_FileReaderFree(p); }
    return 0;
}
