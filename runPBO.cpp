#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <cstdlib>
#include <cstdio>

#define MAX_LINE 1024
#define MAX_LITS 1024

struct CNF {
    int num_vars;
    int num_clauses;
    std::vector<std::vector<int>> clauses;
};

CNF* parse_cnf(const std::string& filename, const std::vector<int>& obj) {
    std::ifstream file(filename);
    if (!file.is_open()) {
        perror("Error opening CNF file");
        return nullptr;
    }

    CNF* cnf = new CNF;
    cnf->num_vars = 0;
    cnf->num_clauses = 0;

    std::string line;
    int clause_index = 0;
    while (std::getline(file, line)) {
        if (line.empty() || line[0] == 'c') continue; // Skip comments
        if (line[0] == 'p') {
            sscanf(line.c_str(), "p cnf %d %d", &cnf->num_vars, &cnf->num_clauses);
            
            if (obj.empty()) { // If no objective variables are specified
                cnf->clauses.resize(cnf->num_clauses);
                continue;
            }
            
            cnf->clauses.resize(++cnf->num_clauses);
            // add one hot constraint for objective variables
            std::vector<int> clause;
            for (int i:obj) {
                if (i > cnf->num_vars) {
                    std::cerr << "Invalid objective variable " << i
                              << ": must be <= " << cnf->num_vars << std::endl;
                    exit(-1);
                }
                clause.push_back(i>0 ? i : -i); // ensure positive literals
            }
            cnf->clauses[clause_index] = clause; // one hot constraint
            clause_index++;
            continue;
        }

        std::istringstream iss(line);
        int lit;
        std::vector<int> clause;
        while (iss >> lit && lit != 0) {
            clause.push_back(lit);
        }
        cnf->clauses[clause_index++] = clause;
        if (clause_index >= cnf->num_clauses) break;
    }

    file.close();
    return cnf;
}

void write_opb(const std::string& filename, const CNF* cnf, const std::vector<int>& obj, const int pi_num, const int originPI_num) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        perror("Error opening OPB file");
        return;
    }

    file << "* #variable= " << cnf->num_vars << " #constraint= " << cnf->num_clauses << "\n";
    file << "* #PI= " << pi_num << " #originPI= " << originPI_num << "\n";

    if (!obj.empty()) {
        file << "min: ";
        for (int coef : obj) {
            if (coef > cnf->num_vars) {
                std::cerr << "Invalid objective variable " << coef
                          << ": must be <= " << cnf->num_vars << std::endl;
                exit(-1);
            }
            else if(coef < 0) continue; // Skip negative coefficients
            file << "-1 x" << coef << " ";
        }
        file << ";\n";
    }

    for (const auto& clause : cnf->clauses) {
        for (int lit : clause) {
            if (lit < 0)
                file << "1 ~x" << -lit << " ";
            else
                file << "1 x" << lit << " ";
        }
        file << ">= 1;\n";
    }

    file.close();
}

void execute_solver(const std::string& opb_filename, const int pi_num, const int originPI_num) {
    std::string command = "./pbcomp24-cg/build/mixed-bag " + opb_filename;
    FILE* fp = popen(command.c_str(), "r");
    if (!fp) {
        perror("popen");
        exit(1);
    }

    char buffer[256];
    bool sat = false;
    while (fgets(buffer, sizeof(buffer), fp)) {
        // std::cerr << buffer; // Print solver output to stderr
        if (buffer[0] != 'v') continue;

        std::istringstream iss(buffer);
        std::string token;
        std::vector<std::string> literals;

        // iss >> token; // skip 'v'
        while (iss >> token) {
            literals.push_back(token);
        }

        int total = literals.size() -1; // Exclude the first 'v' token
        int start = std::max(0, total - pi_num);
        int end = std::max(0, start + originPI_num);
        // std::cerr << "start: " << start << ", end: " << end << "\n";

        std::string bitstring;
        for (int i = start; i < end; ++i) {
            const std::string& lit = literals[i];
            bitstring += (lit[0] != '-') ? '1' : '0';
        }

        sat = true;
        std::cout << bitstring << "\n";

    }

    if (!sat) {
        std::cout << "unsat\n";
    }

    int status = pclose(fp);
    if (status == -1) {
        perror("pclose");
    }
}

int main(int argc, char* argv[]) {
    if (argc < 5) {
        std::cerr << "Usage: " << argv[0] << " input.cnf output.opb [pi_num] [origin pi num] [obj_vars...]\n";
        return 1;
    }
    else if(argc == 5){
        std::cerr << "[Warning] No objective variables specified, running PBO without objective function.\n";
    }

    std::string input_filename = argv[1];
    std::string opb_filename = argv[2];
    const int pi_num = (argc > 3) ? std::atoi(argv[3]) : 0;
    const int originPI_num = (argc > 4) ? std::atoi(argv[4]) : 0;
    std::vector<int> obj_variables;

    for (int i = 5; i < argc; ++i) {
        // possitive integers for objective variables
        // negative integers are not used for objective function, but for onehot encoding
        int num = std::atoi(argv[i]);
        // if (num > 0) {
        obj_variables.push_back(num);
        // } else {
        //     std::cerr << "Objective variables should be positive integers\n";
        //     return -1;
        // }
    }

    CNF* cnf = parse_cnf(input_filename, obj_variables);
    if (!cnf) return 1;
    std::cerr << "CNF parsed successfully\n";
    write_opb(opb_filename, cnf, obj_variables, pi_num, originPI_num);
    std::cerr << "OPB file written successfully\n";

    execute_solver(opb_filename, pi_num, originPI_num);

    delete cnf;

    return 0;
}
