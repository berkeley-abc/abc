#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE 1024
#define MAX_LITS 1024

typedef struct {
    int num_vars;
    int num_clauses;
    int** clauses;
    int* clause_sizes;
} CNF;

CNF* parse_cnf(const char* filename) {
    FILE* file = fopen(filename, "r");
    if (!file) {
        perror("Error opening CNF file");
        return NULL;
    }

    CNF* cnf = malloc(sizeof(CNF));
    cnf->num_vars = 0;
    cnf->num_clauses = 0;
    cnf->clauses = NULL;
    cnf->clause_sizes = NULL;

    char line[MAX_LINE];
    int clause_index = 0;
    while (fgets(line, sizeof(line), file)) {
        if (line[0] == 'c') continue; // Skip comments
        if (line[0] == 'p') {
            sscanf(line, "p cnf %d %d", &cnf->num_vars, &cnf->num_clauses);
            cnf->clauses = malloc(cnf->num_clauses * sizeof(int*));
            cnf->clause_sizes = malloc(cnf->num_clauses * sizeof(int));
            continue;
        }

        // Parse clause
        int lit;
        int* clause = malloc(MAX_LITS * sizeof(int));
        int size = 0;
        char* token = strtok(line, " \t\n");
        while (token) {
            lit = atoi(token);
            if (lit == 0) break;
            clause[size++] = lit;
            token = strtok(NULL, " \t\n");
        }
        // printf("num of clauses: %d\n", clause_index);
        cnf->clauses[clause_index++] = clause;
        cnf->clause_sizes[clause_index - 1] = size;
    }

    fclose(file);
    return cnf;
}

void write_opb(const char* filename, CNF* cnf, int* obj, int size) {
    FILE* file = fopen(filename, "w");
    if (!file) {
        perror("Error opening OPB file");
        return;
    }

    fprintf(file, "* #variable= %d #constraint= %d\n", cnf->num_vars, cnf->num_clauses);

    if (size > 0) {
        fprintf(file, "min: ");
        for (int i = 0; i < size; i++) {
            int coef = obj[i];
            if (coef > cnf->num_vars){
                fprintf(stderr, "Invalid objective variable %d: must be less than or equal to the number of variables (%d)\n", coef, cnf->num_vars);
                exit(-1);
            }
            fprintf(file, "-1 x%d ", coef);
        }
        fprintf(file, ";\n");
    }

    for (int i = 0; i < cnf->num_clauses; i++) {
        for (int j = 0; j < cnf->clause_sizes[i]; j++) {
            int lit = cnf->clauses[i][j];
            if (lit < 0)
                fprintf(file, "1 ~x%d ", -lit);
            else
                fprintf(file, "1 x%d ", lit);
        }
        fprintf(file, ">= 1;\n");
    }

    fclose(file);
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        printf("Usage: %s input.cnf output.opb\n", argv[0]);
        return 1;
    }

    // hard code the input/output file name
    // so that abc can call and use directly
    // const char* input_filename = "atpg.cnf";
    // const char* opb_filename = "output.opb";
    const char* input_filename = argv[1];
    const char* opb_filename = argv[2];

    int* obj_variables = malloc((argc - 3) * sizeof(int));
    for (int i = 3; i < argc; ++i) {
        int num = atoi(argv[i]);
        if (num > 0){
            obj_variables[i - 3] = num;
        }
        else{
            fprintf(stderr, "objective variables should be possitive integers\n");
            exit(-1);
        }
        
    }
    int obj_size = argc - 3;

    CNF* cnf = parse_cnf(input_filename);
    if (!cnf) return 1;

    write_opb(opb_filename, cnf, obj_variables, obj_size);

    // Free allocated memory
    for (int i = 0; i < cnf->num_clauses; i++) {
        free(cnf->clauses[i]);
    }
    free(cnf->clauses);
    free(cnf->clause_sizes);
    free(cnf);

    char command[1024];
    snprintf(command, sizeof(command), "./pbcomp24-cg/build/mixed-bag %s", opb_filename);  // output_filename is like "myfile.opb"
    int result = system(command);
    if (result == -1) {
        perror("system");
    }

    return 0;
}

