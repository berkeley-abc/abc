#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <cstdlib>
#include <cstdio>
#include <regex>
#include <cassert>

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

int write_opb(const std::string& filename, CNF* cnf, const std::vector<int>& obj, const int pi_num, const int originPI_num) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        perror("Error opening OPB file");
        exit(-1);
    }

    int pi_start = cnf->num_vars - pi_num + 1; // [pi_start, pi_end] are the PI variables
    int xy_start = pi_start + originPI_num + obj.size();
    int xy_end = cnf->num_vars ; // [xy_start, xy_end] are the XY variables
    if(xy_end-xy_start + 1 != obj.size()){ // Ensure XY variables match the expected count
        std::cerr << "Error: xy_end-xy_start - 1 != obj.size().\n";
        std::cerr << "Expected: " << xy_end << "-" << xy_start << "-1, Found: " << obj.size() << "\n";
        file.close();
        exit(-1);
    }

    file << "* #variable= " << cnf->num_vars << " #constraint= " << cnf->num_clauses << "\n";
    file << "* #XY_start= " << xy_start << " #XY_end= " << xy_end << "\n";
    file << "* #PI_start= " << pi_start << " #PI_num= " << originPI_num << "\n";

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

    for (int i = xy_start; i <= xy_end; ++i) {
        file << "1 x" << i << " ";
    }
    file << "= 1;\n";

    file.close();
    return pi_start;
}

int add_pbo_constraint(const std::string& filename, CNF* cnf, int pi_num, int& originPI_num) {
    std::ifstream infile(filename);
    if (!infile.is_open()) {
        perror("Error opening OPB file for reading");
        exit(-1);
    }

    std::stringstream buffer;
    std::string line;
    int current_constraints = cnf->num_clauses; // Start with the number of clauses in CNF
    int current_vars = cnf->num_vars;           // Start with the number of variables in CNF
    bool first_header_found = false;
    bool second_header_found = false;
    bool third_header_found = false;

    int parsed_xy_start = -1, parsed_xy_end = -1;
    int parsed_pi_start = -1, parsed_pi_num = -1;
    int origin_vars = -1;


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
                current_constraints += std::stoi(match[2]);
                current_vars += std::stoi(match[1]) - pi_num; // add new variables, except for Xs, Ys.
                origin_vars = std::stoi(match[1]);                   // Store the original number of variables
                std::ostringstream updated;
                updated << "* #variable= " << current_vars
                        << " #constraint= " << current_constraints << "\n";
                buffer << updated.str();
                std::cerr << "variable = " << current_vars
                          << ", constraint = " << current_constraints << "\n";
            } else {
                std::cerr << "Malformed header (line 1)\n";
                exit(-1);
            }
        } 
        else if (!second_header_found && line.rfind("* #XY_", 0) == 0) {
            second_header_found = true;

            // Parse "#PI= X #originPI= Y"
            std::regex pattern(R"(\* #XY_start= (\d+) #XY_end= (\d+))");
            std::smatch match;
            if (std::regex_search(line, match, pattern)) {
                parsed_xy_start = std::stoi(match[1]);
                parsed_xy_end = std::stoi(match[2]);
                std::cerr << "parsed_xy_start = " << parsed_xy_start
                          << ", parsed_xy_end = " << parsed_xy_end << "\n";
                buffer << line << "\n";  // keep the original line
            } else {
                std::cerr << "Malformed PI line (line 2)\n";
                exit(-1);
            }
        } 
        else if (!third_header_found && line.rfind("* #PI_", 0) == 0) {
            second_header_found = true;

            // Parse "#PI= X #originPI= Y"
            std::regex pattern(R"(\* #PI_start= (\d+) #PI_num= (\d+))");
            std::smatch match;
            if (std::regex_search(line, match, pattern)) {
                parsed_pi_start = std::stoi(match[1]);
                parsed_pi_num = std::stoi(match[2]);
                std::cerr << "parsed_pi_start = " << parsed_pi_start
                          << ", parsed_pi_num = " << parsed_pi_num << "\n";
                buffer << line << "\n";  // keep the original line
            } else {
                std::cerr << "Malformed PI line (line 2)\n";
                exit(-1);
            }
        } 
        else {
            buffer << line << "\n";
        }
    }
    infile.close();

    // Step 2: Append the new constraint
    buffer << "* added constraint with provided cnf\n";

    for (const auto& clause : cnf->clauses) {
        for (int lit : clause) {
            if (lit < 0){
                lit = -lit + origin_vars; // adjust to fit origin variables
                if (lit > current_vars){
                    // adjust to fit origin XY variables
                    lit = (lit - current_vars) + parsed_xy_start -1; 
                    if (lit < parsed_xy_start || lit > parsed_xy_end) {
                        std::cerr << "Error: Literal " << -lit << " out of range for XY variables.\n";
                        exit(-1);
                    }
                }
                buffer << "1 ~x" << lit << " ";
            }     
            else{
                lit += origin_vars; // adjust to fit origin variables
                if (lit > current_vars){
                    lit = (lit - current_vars) + parsed_xy_start -1; // adjust to fit origin XY variables
                    if (lit < parsed_xy_start || lit > parsed_xy_end) {
                        std::cerr << "Error: Literal " << lit << " out of range for XY variables.\n";
                        exit(-1);
                    }
                }
                buffer << "1 x" << lit << " ";
            }
        }
        buffer << ">= 1;\n";
    }

    // Step 3: Write back to file
    std::ofstream outfile(filename);
    if (!outfile.is_open()) {
        perror("Error opening OPB file for writing");
        exit(-1);
    }
    outfile << buffer.str();
    outfile.close();

    // Optional: print parsed PI info
    std::cerr << "Parsed XY info: #XY_start= " << parsed_xy_start << ", #XY_end= " << parsed_xy_end << std::endl;
    
    originPI_num = parsed_pi_num; // Update originPI_num to the parsed value
    return parsed_pi_start;
}

// Function to perform the full task
void modify_opb_by_lits(const std::vector<std::string>& lits, const std::string& opb_filename) {
    std::ifstream infile(opb_filename);
    if (!infile.is_open()) {
        std::cerr << "Error opening file: " << opb_filename << std::endl;
        return;
    }

    std::vector<std::string> lines;
    std::string line;
    int min_line_index = -1;
    bool second_header_found = false;
    int obj_var_count = 0;

    // Step 1: read all lines and find the "min:" line
    std::vector<int> min_var_indices;  // stores indices like 19, 20, ...

    while (std::getline(infile, line)) {
        std::string trimmed = line;

        if (min_line_index == -1 && trimmed.rfind("min:", 0) == 0) {
            std::stringstream ss(trimmed);
            std::string token, coef, var;
            ss >> token; // skip "min:"

            while (ss >> coef >> var) {
                if (var == ";") break;
                if (var.size() > 1 && var[0] == 'x') {
                    int idx = std::stoi(var.substr(1));
                    min_var_indices.push_back(idx);
                }
            }

            min_line_index = lines.size(); // record which line to modify
        }
        else if (!second_header_found && line.rfind("* #XY_", 0) == 0) {
            second_header_found = true;

            // Parse "#PI= X #originPI= Y"
            std::regex pattern(R"(\* #XY_start= (\d+) #XY_end= (\d+))");
            std::smatch match;
            if (std::regex_search(line, match, pattern)) {
                obj_var_count = std::stoi(match[2]) - std::stoi(match[1]) + 1; // Calculate number of objective variables
            } else {
                std::cerr << "Malformed PI line (line 2)\n";
                return;
            }
        }

        lines.push_back(line);
    }
    infile.close();

    if (min_var_indices.size() == 0 || min_line_index < 0) {
        std::cerr << "No valid min line or variable found.\n";
        return;
    }

    // Step 2: find the first positive literal in lits[start_index...]
    std::string target_var;
    int t_var;
    for (int i: min_var_indices) {
        const std::string& lit = lits[i+obj_var_count];
        std::cerr << "Checking literal: " << lit << "\n";
        if (!lit.empty() && lit[0] != '-') {
            // strip "x" if present, store only the index
            size_t x_pos = lit.find('x');
            target_var = x_pos != std::string::npos ? lit.substr(x_pos + 1) : lit;
            t_var = std::stoi(target_var) -obj_var_count;
            target_var = std::to_string(t_var); // convert to string for consistency
            std::cerr << "Removing: x" << target_var << " from objective function\n";
            break;
        }
    }

    if (target_var.empty()) {
        std::cerr << "No positive literal found in lits.\n";
        std::cerr << "Available literals: " << lits.size() << "\n";
        return;
    }

    // Step 3: remove the variable from the "min:" line
    std::string& min_line = lines[min_line_index];
    std::stringstream ss(min_line);
    std::string updated_line, token;
    ss >> token; // skip "min:"
    updated_line = "min:";

    while (ss >> token) {
        if (token == ";") {
            updated_line += " ;";
            break;
        }

        std::string coef = token;
        if (!(ss >> token)) break; // read variable
        std::string var = token;

        // Keep if not the target
        if (var != ("x" + target_var)) {
            updated_line += " " + coef + " " + var;
        }
    }

    lines[min_line_index] = updated_line;

    // Step 4: overwrite the file
    std::ofstream outfile(opb_filename);
    if (!outfile.is_open()) {
        std::cerr << "Error writing to file: " << opb_filename << std::endl;
        return;
    }

    for (const auto& l : lines) {
        outfile << l << "\n";
    }

    outfile.close();
}

void execute_solver(const std::string& opb_filename, const int pi_start, const int originPI_num) {
    std::string command = "./pbcomp24-cg/build/mixed-bag " + opb_filename;
    FILE* fp = popen(command.c_str(), "r");
    if (!fp) {
        perror("popen");
        exit(1);
    }

    // char buffer[4096]; // TODO : Adjust buffer size as needed
    std::string line;
    char* c_line = nullptr;
    size_t len = 0;

    bool sat = false;
    while (getline(&c_line, &len, fp) != -1) {
        line = c_line;
        std::cerr << line; // Print solver output to stderr
        if (line.empty() || line[0] != 'v') continue;

        std::istringstream iss(line);
        std::string token;
        std::vector<std::string> literals;

        // iss >> token; // skip 'v'
        while (iss >> token) {
            literals.push_back(token);
        }

        int total = literals.size() -1; // Exclude the first 'v' token
        int start = pi_start;
        int end = pi_start + originPI_num ;
        std::cerr << "pi: [start: " << start << ", end: " << end << ")\n";

        std::string bitstring;
        for (int i = start; i < end && i < literals.size(); ++i) {
            const std::string& lit = literals[i];
            bitstring += (lit[0] != '-') ? '1' : '0';
        }

        sat = true;
        modify_opb_by_lits(literals, opb_filename); // Modify the OPB's objective function with the literals
        std::cout << bitstring << "\n";

    }
    free(c_line);

    if (!sat) {
        std::cout << "unsat\n";
    }

    int status = pclose(fp);
    if (status == -1) {
        perror("pclose");
    }
}

int main(int argc, char* argv[]) {
    if (argc != 5) {
        std::cerr << "Usage: " << argv[0] << " input.cnf output.opb [pi_num] [origin pi num]\n";
        return 1;
    }
    // else if(argc == 5){
    //     std::cerr << "[Warning] No objective variables specified, running PBO without objective function.\n";
    // }

    std::string input_filename = argv[1];
    std::string opb_filename = argv[2];
    const int pi_num = (argc > 3) ? std::atoi(argv[3]) : 0;
    int originPI_num = (argc > 4) ? std::atoi(argv[4]) : 0;
    assert(originPI_num <= pi_num); // let originPI_num = -1 be the signal of appending constraints
    std::vector<int> obj_variables;
    int pi_start = 0;

    CNF* cnf = parse_cnf(input_filename);
    if (!cnf) return 1;
    std::cerr << "CNF parsed successfully\n";

    if (originPI_num > 0){
        int start = cnf->num_vars - pi_num + originPI_num +1;
        int end = (start + cnf->num_vars)/2;
        std::cerr << "start: " << start << ", end: " << end << "\n";
        assert(end - start +1 == cnf->num_vars -end);
        for (int i = start; i <= end; ++i) {
            obj_variables.push_back(i);
        }

        pi_start = write_opb(opb_filename, cnf, obj_variables, pi_num, originPI_num);
        std::cerr << "OPB file written successfully\n";
    }
    else if (originPI_num == -1){
        pi_start = add_pbo_constraint(opb_filename, cnf, pi_num, originPI_num);
        std::cerr << "OPB file updated with new constraints successfully\n";
    }
    
    execute_solver(opb_filename, pi_start, originPI_num);

    delete cnf;

    return 0;
}
