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

CNF* parse_cnf(const std::string& filename) {
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
            cnf->clauses.resize(cnf->num_clauses);
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

void write_opb(const std::string& filename, const CNF* cnf, const std::vector<int>& obj) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        perror("Error opening OPB file");
        return;
    }

    file << "* #variable= " << cnf->num_vars << " #constraint= " << cnf->num_clauses << "\n";

    if (!obj.empty()) {
        file << "min: ";
        for (int coef : obj) {
            if (coef > cnf->num_vars) {
                std::cerr << "Invalid objective variable " << coef
                          << ": must be <= " << cnf->num_vars << std::endl;
                exit(-1);
            }
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

void execute_solver(const std::string& opb_filename) {
    std::string command = "./pbcomp24-cg/build/mixed-bag " + opb_filename;
    FILE* fp = popen(command.c_str(), "r");
    if (!fp) {
        perror("popen");
        exit(1);
    }

    char buffer[256];
    while (fgets(buffer, sizeof(buffer), fp)) {
        if (buffer[0] != 'v') continue;

        std::istringstream iss(buffer);
        std::string token;
        std::vector<std::string> literals;

        iss >> token; // skip 'v'
        while (iss >> token) {
            literals.push_back(token);
        }

        int total = literals.size();
        int start = std::max(0, total - 10);
        int end = std::max(0, total - 5);

        std::string bitstring;
        for (int i = start; i < end; ++i) {
            const std::string& lit = literals[i];
            bitstring += (lit[0] != '-') ? '1' : '0';
        }

        std::cout << bitstring << "\n";

    }

    int status = pclose(fp);
    if (status == -1) {
        perror("pclose");
    }
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cout << "Usage: " << argv[0] << " input.cnf output.opb [obj_vars...]\n";
        return 1;
    }

    std::string input_filename = argv[1];
    std::string opb_filename = argv[2];
    std::vector<int> obj_variables;

    for (int i = 3; i < argc; ++i) {
        int num = std::atoi(argv[i]);
        if (num > 0) {
            obj_variables.push_back(num);
        } else {
            std::cerr << "Objective variables should be positive integers\n";
            return -1;
        }
    }

    CNF* cnf = parse_cnf(input_filename);
    if (!cnf) return 1;
    std::cerr << "CNF parsed successfully\n";
    write_opb(opb_filename, cnf, obj_variables);
    std::cerr << "OPB file written successfully\n";

    execute_solver(opb_filename);

    delete cnf;

    return 0;
}
