#include "abc.h"
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

ABC_NAMESPACE_IMPL_START

void Abc_ExecPBO()
{
    pid_t pid = fork();

    if (pid == 0) {
        // Child process: executing pbo solver
        char arg_str[100] = {0};
        for (int i = 2; i < 10; ++i) {
            char temp[16];
            sprintf(temp, "%d", i);
            strcat(arg_str, temp);
            if (i < 10 - 1) strcat(arg_str, " ");
        }
        
        char *argv[] = {"./solver", "atpg.cnf", "output.opb", arg_str, NULL};
        execv("./solver", argv);
        _exit(1); // exec failed
    } else {
        // Parent process: wait for child to finish
        waitpid(pid, NULL, 0);
    }
}

ABC_NAMESPACE_IMPL_END