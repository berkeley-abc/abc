#include "abc.h"
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

ABC_NAMESPACE_IMPL_START

Vec_Int_t * Abc_ExecPBO( Abc_Ntk_t * pNtk, int first_run )
{
    // extern void Abc_NtkAddTestPattern( Abc_Ntk_t * pNtk, Vec_Int_t * vPattern );

    const int pi_num =  Abc_NtkPiNum(pNtk);
    // int good_pi_num = Abc_NtkPiNum(pNtk);
    const int good_pi_num = pNtk->vGoodPis ? Vec_PtrSize(pNtk->vGoodPis) : -1;
    if (good_pi_num < 0) {
        Abc_Print(ABC_ERROR, "No good PIs found in the network.\n");
        return NULL;
    }
    char pi_num_str[16], good_pi_str[16];
    
    if(first_run){
        sprintf(pi_num_str, "%d", pi_num);
        sprintf(good_pi_str, "%d", good_pi_num);
    } else {
        // for next runPBO call
        // XY variable nums, and -1 specified incremental PBO
        sprintf(pi_num_str, "%d", (pi_num - good_pi_num)/2);
        sprintf(good_pi_str, "%d", -1);
    }

    int pipefd[2];
    if (pipe(pipefd) == -1) {
        perror("pipe");
        return NULL;
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
                return NULL;
            }

            output = new_output;
            memcpy(output + total_size, buffer, count);
            total_size += count;
            output[total_size] = '\0'; // Null-terminate for safety
        }

        close(pipefd[0]); // Close read end
        waitpid(pid, NULL, 0);

        if ( strncmp(output, "unsat", 5) == 0 ) {
            Abc_Print(ABC_STANDARD, "PBO solver returned unsat.\n");
            free(output);
            return NULL;
        }

        int* pattern = (int*)malloc(sizeof(int) * good_pi_num);
        if (!pattern) {
            Abc_Print(ABC_ERROR, "Memory allocation failed for pattern.\n");
            free(output);
            return NULL;
        }

        for (int i = 0; i < good_pi_num; ++i) {
            pattern[i] = output[i] == '1' ? 1 : 0 ; // Convert char to int
        }
        Vec_Int_t * vPattern = Vec_IntAllocArray(pattern, good_pi_num);

        free(output);

        return vPattern;

    }
}

ABC_NAMESPACE_IMPL_END