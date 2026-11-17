// Research harness for the original PR library. Uses one ABC process and one
// library load; all timed synthesis work is the unchanged compress2rs script.
#include "base/main/main.h"
#include "base/abc/abc.h"
#include "base/cmd/cmd.h"
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <ctime>

int main(int argc, char **argv)
{
    if (argc != 6) return 2;
    char *end = nullptr;
    const double budget = std::strtod(argv[3], &end);
    if (!end || *end || !std::isfinite(budget) || budget <= 0) return 2;
    const abctime start = std::clock();
    Abc_Start();
    auto *frame = Abc_FrameGetGlobalFrame();
    int result = Cmd_CommandExecute(frame, argv[1]);
    int cycles = 0;
    if (!result)
    {
        do
        {
            result = Cmd_CommandExecute(frame, argv[2]);
            if (result) break;
            ++cycles;
            if (cycles == 1) result = Cmd_CommandExecute(frame, argv[5]);
            std::printf("ABC_BUDGET_CYCLE cycles=%d nodes=%d cpu_seconds=%.9f\n", cycles,
                        Abc_NtkNodeNum(Abc_FrameReadNtk(frame)),
                        double(std::clock() - start) / CLOCKS_PER_SEC);
        } while (!result && double(std::clock() - start) / CLOCKS_PER_SEC < budget);
        std::printf("ABC_BUDGET target=%.9f cycles=%d cpu_seconds=%.9f\n", budget, cycles,
                    double(std::clock() - start) / CLOCKS_PER_SEC);
        if (!result) result = Cmd_CommandExecute(frame, argv[4]);
    }
    Abc_Stop();
    return result;
}
