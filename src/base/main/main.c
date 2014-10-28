#include "base/main/mainInt.h"

int Abc_RealMain(int argc, char *argv[]);

//static Abc_FrameInitializer_t abc2_initializer = { Abc2_Init, Abc2_End };

int main(int argc, char *argv[])
{
//    Abc_FrameAddInitializer(&abc2_initializer);

    return Abc_RealMain(argc, argv);
}
