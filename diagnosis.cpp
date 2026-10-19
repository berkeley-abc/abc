#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_map>
#include <algorithm>
#include <filesystem>  // C++17

namespace fs = std::filesystem;

struct Clause {
    std::vector<int> literals;
};

struct CNF {
    int num_vars;
    int num_clauses;
    std::vector<Clause> clauses;
};

CNF read_cnf(const std::string& filename) {
    CNF cnf;
    std::ifstream fin(filename);
    std::string line;
    while (std::getline(fin, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            std::istringstream iss(line);
            std::string tmp;
            iss >> tmp >> tmp >> cnf.num_vars >> cnf.num_clauses;
        } else {
            std::istringstream iss(line);
            Clause clause;
            int lit;
            while (iss >> lit && lit != 0) {
                clause.literals.push_back(lit);
            }
            cnf.clauses.push_back(clause);
        }
    }
    return cnf;
}

void write_cnf(const std::string& filename, int num_vars, const std::vector<Clause>& all_clauses) {
    std::ofstream fout(filename);
    fout << "p cnf " << num_vars << " " << all_clauses.size() << "\n";
    for (const auto& clause : all_clauses) {
        for (int lit : clause.literals) {
            fout << lit << " ";
        }
        fout << "0\n";
    }
}

// Generate all clauses enforcing: sum(x1 .. xn) ≤ k
std::vector<std::vector<int>> generate_at_most_k_cnf(int n, int k) {
    std::vector<std::vector<int>> clauses;

    // Variable IDs: 1 to n
    std::vector<int> vars(n);
    for (int i = 0; i < n; ++i) vars[i] = i + 1;

    // Create a selector mask for (k+1)-sized subsets
    std::vector<bool> select(n, false);
    std::fill(select.begin(), select.begin() + (k + 1), true);

    do {
        std::vector<int> clause;
        for (int i = 0; i < n; ++i) {
            if (select[i]) clause.push_back(-vars[i]); // ¬xᵢ
        }
        clauses.push_back(clause);
    } while (std::prev_permutation(select.begin(), select.end()));

    return clauses;
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <shared_vars_n>\n";
        return 1;
    }

    int n = std::stoi(argv[1]);
    int global_offset = 0;
    std::vector<Clause> combined_clauses;

    // // First pass to compute total offset for non-shared vars
    std::vector<CNF> cnf_list;
    for (int i = 2; i < argc; ++i) {
        CNF cnf = read_cnf(argv[i]);
        if (cnf.num_vars < n) {
            std::cerr << "Error: CNF file " << argv[i] << " has fewer variables than n=" << n << "\n";
            return 1;
        }
        cnf_list.push_back(cnf);
        global_offset += (cnf.num_vars - n);
    }
    // const std::string cnf_dir = "./diag_sample";
    // for (const auto& entry : fs::directory_iterator(cnf_dir)) {
    //     if (entry.path().extension() == ".cnf") {
    //         std::string filename = entry.path().string();
    //         std::cout << "Reading CNF file: " << filename << "\n";
    //         CNF cnf = read_cnf(filename);

    //         if (cnf.num_vars < n) {
    //             std::cerr << "Error: CNF file " << filename << " has fewer variables than n=" << n << "\n";
    //             return 1;
    //         }

    //         cnf_list.push_back(cnf);
    //         global_offset += (cnf.num_vars - n);
    //     }
    // }

    int global_shared_start = global_offset + 1;

    // Reset offset for mapping
    int offset_tracker = 0;

    for (size_t file_i = 0; file_i < cnf_list.size(); ++file_i) {
        const CNF& cnf = cnf_list[file_i];
        int V = cnf.num_vars;
        int non_shared = V - n;
        int local_shared_start = V - n + 1;

        std::unordered_map<int, int> var_map;

        // Map non-shared variables to new unique indices
        for (int i = 1; i <= non_shared; ++i) {
            var_map[i] = offset_tracker + i;
        }

        // Map shared variables to the global shared region
        for (int i = local_shared_start; i <= V; ++i) {
            int shared_idx = i - local_shared_start;
            var_map[i] = global_shared_start + shared_idx;
        }

        // Update offset tracker
        offset_tracker += non_shared;

        // Remap and add clauses
        for (const auto& clause : cnf.clauses) {
            Clause new_clause;
            for (int lit : clause.literals) {
                int var = std::abs(lit);
                int sign = (lit > 0) ? 1 : -1;
                new_clause.literals.push_back(sign * var_map[var]);
            }
            combined_clauses.push_back(new_clause);
        }
    }

    // auto clauses = generate_at_most_k_cnf(n, 5);
    // for (const auto& clause : clauses) {
    //     Clause new_clause;
    //     for (int lit : clause) {
    //         new_clause.literals.push_back(global_shared_start + lit);
    //     }
    //     combined_clauses.push_back(new_clause);
    // }
    

    int total_vars = global_shared_start + n - 1;
    write_cnf("combined.cnf", total_vars, combined_clauses);
    std::cout << "Combined CNF written to combined.cnf with " << total_vars
              << " variables and " << combined_clauses.size() << " clauses.\n";

    
    
    return 0;
}
