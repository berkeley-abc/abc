#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <cstdlib>
#include <cstdio>
#include <regex>

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

void write_opb(const std::string& filename, CNF* cnf, const std::vector<int>& obj, const int pi_num, const int originPI_num) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        perror("Error opening OPB file");
        return;
    }

    if (!obj.empty()){
        std::vector<int> clause;
        for (int i:obj) {
            if (i > cnf->num_vars) {
                std::cerr << "Invalid objective variable " << i
                        << ": must be <= " << cnf->num_vars << std::endl;
                exit(-1);
            }
            int lit = i>0 ? i : -i;
            clause.push_back(lit); // ensure positive literals
        }
        cnf->num_clauses++ ;
        cnf->clauses.push_back(clause);
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

void add_pbo_constraint(const std::string& filename, CNF* cnf, const std::vector<int>& obj, int pi_num, int originPI_num) {
    std::ifstream infile(filename);
    if (!infile.is_open()) {
        perror("Error opening OPB file for reading");
        return;
    }

    std::stringstream buffer;
    std::string line;
    int current_constraints = cnf->num_clauses; // Start with the number of clauses in CNF
    bool first_header_found = false;
    bool second_header_found = false;

    int parsed_pi_num = -1, parsed_originPI_num = -1;

    // Step 1: Read file line by line and update headers
    int line_number = 0;
    while (std::getline(infile, line)) {
        line_number++;
        if (!first_header_found && line.rfind("* #variable=", 0) == 0) {
            first_header_found = true;

            // Parse "#variable= X #constraint= Y"
            std::regex pattern(R"(\* #variable= (\d+) #constraint= (\d+))");
            std::smatch match;
            if (std::regex_search(line, match, pattern)) {
                current_constraints += std::stoi(match[2]); // add 1 for new constraint
                std::ostringstream updated;
                updated << "* #variable= " << cnf->num_vars
                        << " #constraint= " << current_constraints << "\n";
                buffer << updated.str();
            } else {
                std::cerr << "Malformed header (line 1)\n";
                return;
            }
        } else if (!second_header_found && line.rfind("* #PI=", 0) == 0) {
            second_header_found = true;

            // Parse "#PI= X #originPI= Y"
            std::regex pattern(R"(\* #PI= (\d+) #originPI= (\d+))");
            std::smatch match;
            if (std::regex_search(line, match, pattern)) {
                parsed_pi_num = std::stoi(match[1]);
                parsed_originPI_num = std::stoi(match[2]);
                buffer << line << "\n";  // keep the original line
            } else {
                std::cerr << "Malformed PI line (line 2)\n";
                return;
            }
        } else {
            buffer << line << "\n";
        }
    }
    infile.close();

    // Step 2: Append the new constraint
    buffer << "* added constraint with provided cnf\n";
    // for (int i = 0; i < obj.size(); ++i) {
    //     if (obj[i] < 0)
    //         buffer << "1 ~x" << -obj[i] << " ";
    //     else
    //         buffer << "1 x" << obj[i] << " ";
    // }
    // buffer << ">= 1;\n";

    for (const auto& clause : cnf->clauses) {
        for (int lit : clause) {
            if (lit < 0)
                buffer << "1 ~x" << -lit << " ";
            else
                buffer << "1 x" << lit << " ";
        }
        buffer << ">= 1;\n";
    }

    // Step 3: Write back to file
    std::ofstream outfile(filename);
    if (!outfile.is_open()) {
        perror("Error opening OPB file for writing");
        return;
    }
    outfile << buffer.str();
    outfile.close();

    // Optional: print parsed PI info
    std::cout << "Parsed PI info: #PI= " << parsed_pi_num << ", #originPI= " << parsed_originPI_num << std::endl;
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
        obj_variables.push_back(num);
    }

    CNF* cnf = parse_cnf(input_filename);
    if (!cnf) return 1;
    std::cerr << "CNF parsed successfully\n";

    write_opb(opb_filename, cnf, obj_variables, pi_num, originPI_num);
    std::cerr << "OPB file written successfully\n";
    // add_pbo_constraint(opb_filename, cnf, obj_variables, pi_num, originPI_num);

    execute_solver(opb_filename, pi_num, originPI_num);

    delete cnf;

    return 0;
}
