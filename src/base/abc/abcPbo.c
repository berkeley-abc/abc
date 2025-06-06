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
        char *argv[] = {"./solver", arg_str, NULL};
        execv("./solver", argv);
        _exit(1); // exec failed
    } else {
        // Parent process: wait for child to finish
        waitpid(pid, NULL, 0);
    }
}

ABC_NAMESPACE_IMPL_END