// Optional exact global input-correlation refinement for selected cuts.
// Simulation certifies reachable patterns; only SAT UNSAT excludes a pattern.
// Resource-limit/unknown answers remain cared. No observability assumptions.
struct SparseGlobalCare
{
    sat_solver *solver = nullptr;
    std::vector<unsigned char> encoded;
    std::vector<std::array<uint64_t, 4>> simulation;
    // SAT literals are allocated separately from ABC object IDs. Candidate
    // miters introduce auxiliary variables while later live nodes keep growing.
    std::vector<int> objectLiteral;
    std::unordered_map<uint64_t, int> ands;
    int one = -1;
    long proofQueries = 0, proofCalls = 0, proofUnsat = 0, proofSat = 0, proofUnknown = 0;
    struct Proof
    {
        int status;
        unsigned pattern;
    };
    std::unordered_map<std::string, Proof> proofs;
    long queries = 0, calls = 0, unsat = 0, unknown = 0, removed = 0, objects = 0;
    long endpointQueries = 0, endpointCalls = 0, endpointProved = 0, endpointUnknown = 0;
    std::unordered_map<std::string, int> endpointProofs;
    double seconds = 0;
    ~SparseGlobalCare()
    {
        const int variables = solver ? sat_solver_nvars(solver) : 0;
        if (solver)
            sat_solver_delete(solver);
        if (queries)
            TG_VERBOSE("TG_GLOBAL_CARE queries=%ld sat_calls=%ld unsat=%ld unknown=%ld "
                       "removed_patterns=%ld encoded_objects=%ld cpu_seconds=%.9f\n",
                       queries, calls, unsat, unknown, removed, objects, seconds);
        if (proofQueries)
            TG_VERBOSE("TG_GLOBAL_PROOF queries=%ld sat_calls=%ld proved=%ld refuted=%ld "
                       "unknown=%ld variables=%d cpu_seconds=%.9f\n",
                       proofQueries, proofCalls, proofUnsat, proofSat, proofUnknown, variables,
                       seconds);
        if (endpointQueries)
            TG_VERBOSE("TG_GLOBAL_ENDPOINT queries=%ld sat_calls=%ld proved=%ld unknown=%ld "
                       "variables=%d\n",
                       endpointQueries, endpointCalls, endpointProved, endpointUnknown, variables);
    }

    // The root and reused divisors need not share a small independent cut.
    // Only UNSAT certifies the replacement; simulation never authorizes edits.
    // This cache is valid only while every surviving object's global function
    // is preserved (the caller forbids ODC edits for this entire command).
};
