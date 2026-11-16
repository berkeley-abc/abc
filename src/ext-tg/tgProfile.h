#ifndef ABC__ext_tg__paProfile_h
#define ABC__ext_tg__paProfile_h
// Optional inclusive phase profiling. Production builds compile out every
// timer/counter; profile measurements are not used as runtime results.
#ifdef ABC_TG_ENABLE_PROFILE
#include <ctime>
#include <cstdio>
ABC_NAMESPACE_IMPL_START
namespace Tg_Profile
{
enum Phase
{
    Build,
    RootRefresh,
    RequiredRefresh,
    CandidateTiming,
    Commit,
    Replace,
    ReverseLevels,
    ArrivalPropagation,
    RequiredInvalidation,
    SeedPreparation,
    PhaseCount
};
enum Count
{
    ArrivalNodes,
    RequiredNodes,
    ReverseQueries,
    ReverseNaivePins,
    ReverseScannedPins,
    SeedBackwardNodes,
    SeedForwardNodes,
    CountSize
};
struct Data
{
    double seconds[PhaseCount] = {};
    unsigned long long calls[PhaseCount] = {}, counts[CountSize] = {};
};
inline Data &Get()
{
    static Data d;
    return d;
}
struct Scope
{
    Phase phase;
    std::clock_t start;
    explicit Scope(Phase p) : phase(p), start(std::clock()) {}
    ~Scope()
    {
        Get().seconds[phase] += double(std::clock() - start) / CLOCKS_PER_SEC;
        ++Get().calls[phase];
    }
};
inline void Flush()
{
    const char *names[] = {"build",
                           "root_refresh",
                           "required_refresh",
                           "candidate_timing",
                           "commit",
                           "replace",
                           "reverse_levels",
                           "arrival_propagation",
                           "required_invalidation",
                           "seed_preparation"};
    const char *counts[] = {"arrival_nodes",      "required_nodes",       "reverse_queries",
                            "reverse_naive_pins", "reverse_scanned_pins", "seed_backward_nodes",
                            "seed_forward_nodes"};
    for (int i = 0; i < PhaseCount; ++i)
        if (Get().calls[i])
            std::printf("tg_profile: %s cpu=%.6f calls=%llu\n", names[i], Get().seconds[i],
                        Get().calls[i]);
    for (int i = 0; i < CountSize; ++i)
        if (Get().counts[i])
            std::printf("tg_profile: %s count=%llu\n", counts[i], Get().counts[i]);
    Get() = Data{};
}
} // namespace Tg_Profile
ABC_NAMESPACE_IMPL_END
#define TG_PROFILE_SCOPE(name) Tg_Profile::Scope tg_profile_scope(Tg_Profile::name)
#define TG_PROFILE_COUNT(name, n) (Tg_Profile::Get().counts[Tg_Profile::name] += (n))
#define TG_PROFILE_FLUSH() Tg_Profile::Flush()
#else
#define TG_PROFILE_SCOPE(name) ((void)0)
#define TG_PROFILE_COUNT(name, n) ((void)0)
#define TG_PROFILE_FLUSH() ((void)0)
#endif
#endif
