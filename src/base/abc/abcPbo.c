#include "abc.h"
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

ABC_NAMESPACE_IMPL_START

void Abc_ExecPBO( Abc_Ntk_t * pNtk )
{
    // extern void Abc_NtkAddTestPattern( Abc_Ntk_t * pNtk, Vec_Int_t * vPattern );

    const int pi_num =  Abc_NtkPiNum(pNtk);
    // int good_pi_num = Abc_NtkPiNum(pNtk);
    const int good_pi_num = pNtk->vGoodPis ? Vec_PtrSize(pNtk->vGoodPis) : -1;
    if (good_pi_num < 0) {
        Abc_Print(ABC_ERROR, "No good PIs found in the network.\n");
        return;
    }
    char pi_num_str[16], good_pi_str[16];
    sprintf(pi_num_str, "%d", pi_num);
    sprintf(good_pi_str, "%d", good_pi_num);

    int pipefd[2];
    if (pipe(pipefd) == -1) {
        perror("pipe");
        return;
    }

    pid_t pid = fork();

    if (pid == 0) {
        // Child process: executing pbo solver
        close(pipefd[0]); // Close unused read end

        dup2(pipefd[1], STDOUT_FILENO); // Redirect stdout to pipe
        
        // need to compile runPBO.cpp first
        char *argv[] = {"./runpbo", "atpg.cnf", "output.opb", pi_num_str, good_pi_str, NULL};
        execv("./runpbo", argv);

        // If execv returns, an error occurred
        perror("execv");
        close(pipefd[1]); // Close write end
        _exit(1); // exec failed

    } else {
        // Parent process: wait for child to finish
        close(pipefd[1]); // Close unused write end

        char buffer[1024];
        size_t total_size = 0;
        char *output = NULL;

        ssize_t count;
        while ((count = read(pipefd[0], buffer, sizeof(buffer))) > 0) {
            char *new_output = realloc(output, total_size + count + 1);
            if (!new_output) {
                Abc_Print(ABC_ERROR, "Memory allocation failed.\n");
                free(output);
                close(pipefd[0]);
                waitpid(pid, NULL, 0);
                return;
            }

            output = new_output;
            memcpy(output + total_size, buffer, count);
            total_size += count;
            output[total_size] = '\0'; // Null-terminate for safety
        }

        close(pipefd[0]); // Close read end
        waitpid(pid, NULL, 0);

        int* pattern = (int*)malloc(sizeof(int) * good_pi_num);
        if (!pattern) {
            Abc_Print(ABC_ERROR, "Memory allocation failed for pattern.\n");
            free(output);
            return;
        }

        if ( strncmp(output, "unsat", 5) == 0 ) {
            Abc_Print(ABC_WARNING, "PBO solver returned unsat.\n");
            free(output);
            free(pattern);
            return;
        }

        for (int i = 0; i < good_pi_num; ++i) {
            pattern[i] = output[i] == '1' ? 1 : 0 ; // Convert char to int
        }
        Vec_Int_t * vPattern = Vec_IntAllocArray(pattern, good_pi_num);

        Abc_NtkAddTestPattern(pNtk, vPattern);
        free(output);
        return;
    }
}

ABC_NAMESPACE_IMPL_END