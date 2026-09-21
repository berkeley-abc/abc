#include <misc/util/abc_global.h>

#include <stdio.h>

ABC_NAMESPACE_IMPL_START

int Abc_RealMain(int argc, char *argv[]);

ABC_NAMESPACE_IMPL_END

int main(int argc, char *argv[])
{
   setvbuf(stdout, NULL, _IOLBF, BUFSIZ);
   return ABC_NAMESPACE_PREFIX Abc_RealMain(argc, argv);
}
