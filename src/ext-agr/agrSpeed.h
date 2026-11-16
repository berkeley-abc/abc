#ifndef ABC_AGR_SPEED_H
#define ABC_AGR_SPEED_H
#include <array>
#include <vector>
#include <chrono>
#include <cstdio>
#include <cstdlib>
namespace AgrSpeed
{
inline constexpr bool CareAudit()
{
    return false;
}

inline constexpr bool Generation()
{
    return true;
}

inline constexpr bool Evaluation()
{
    return true;
}
// Recycle empty container storage, never candidate contents. A live vector
// exclusively owns its buffer; nested audit plans acquire different buffers.
// AGR is single-threaded. Bound both retained buffer count and capacity.
template <class T> class WorkspaceVector : public std::vector<T>
{
    using Base = std::vector<T>;
    static bool &Stopping()
    {
        static bool value = false;
        return value;
    }
    struct PoolStorage
    {
        std::vector<Base> buffers;
        ~PoolStorage()
        {
            Stopping() = true;
        }
    };
    static std::vector<Base> &Pool()
    {
        static PoolStorage storage;
        return storage.buffers;
    }
    bool recycle_ = Evaluation();

  public:
    using Base::operator=;
    WorkspaceVector()
    {
        if (recycle_ && !Pool().empty())
        {
            this->swap(Pool().back());
            Pool().pop_back();
        }
    }
    explicit WorkspaceVector(size_t count) : WorkspaceVector()
    {
        this->resize(count);
    }
    WorkspaceVector(size_t count, const T &value) : WorkspaceVector()
    {
        this->assign(count, value);
    }
    WorkspaceVector(const Base &other) : WorkspaceVector()
    {
        this->assign(other.begin(), other.end());
    }
    WorkspaceVector(const WorkspaceVector &other) : WorkspaceVector()
    {
        this->assign(other.begin(), other.end());
    }
    WorkspaceVector(WorkspaceVector &&other) noexcept
        : Base(std::move(other)), recycle_(other.recycle_)
    {
    }
    WorkspaceVector &operator=(const WorkspaceVector &other)
    {
        Base::operator=(other);
        return *this;
    }
    WorkspaceVector &operator=(WorkspaceVector &&other) noexcept
    {
        Base::operator=(std::move(other));
        return *this;
    }
    ~WorkspaceVector()
    {
        if (!Stopping() && recycle_ && this->capacity() <= 8192 && Pool().size() < 32)
        {
            this->clear();
            Pool().emplace_back();
            this->swap(Pool().back());
        }
    }
};
// Small integer neighborhoods keep four entries inline; larger fanouts grow normally.
struct IntList
{
    std::array<int, 4> local{};
    std::vector<int> large;
    size_t count = 0;
    bool small = Evaluation();
    size_t size() const
    {
        return count;
    }
    int *begin()
    {
        return small || !count ? local.data() : large.data();
    }
    const int *begin() const
    {
        return small || !count ? local.data() : large.data();
    }
    int *end()
    {
        return begin() + count;
    }
    const int *end() const
    {
        return begin() + count;
    }
    void push_back(int value)
    {
        if (small && count < 4)
            local[count++] = value;
        else
        {
            if (small)
            {
                large.assign(local.begin(), local.begin() + count);
                small = false;
            }
            large.push_back(value);
            ++count;
        }
    }
    void erase(int *first, int *last)
    {
        size_t a = first - begin(), b = last - begin();
        if (small)
        {
            for (size_t i = b; i < count; ++i)
                local[a + i - b] = local[i];
        }
        else
            large.erase(large.begin() + a, large.begin() + b);
        count -= b - a;
    }
};
// Bounded stack scratch with an unrestricted heap fallback for larger cuts.
template <class T, size_t N> struct Scratch
{
    std::array<T, N> local;
    std::vector<T> large;
    size_t count;
    explicit Scratch(size_t n) : count(n)
    {
        if (n > N)
            large.resize(n);
    }
    T *data()
    {
        return count > N ? large.data() : local.data();
    }
    T &operator[](size_t i)
    {
        return data()[i];
    }
};
#ifdef ABC_AGR_PIPE_PROFILE
struct Record
{
    double seconds = 0;
    unsigned long long calls = 0;
};
inline std::array<Record, 40> &Data()
{
    static std::array<Record, 40> d{};
    return d;
}
enum Phase
{
    Region,
    Generate,
    Truth,
    Graph,
    Screen,
    Entities,
    Materialization,
    Cascade,
    Nets,
    Density,
    Placement,
    Hpwl,
    Median,
    DensitySamples,
    Other,
    Factor,
    Spatial,
    Key
};
inline int &Domain()
{
    static int d = 0;
    return d;
}
struct CommitDomain
{
    int previous = Domain();
    CommitDomain()
    {
        Domain() = 1;
    }
    ~CommitDomain()
    {
        Domain() = previous;
    }
};
struct Scope
{
    int p;
    std::chrono::steady_clock::time_point start;
    explicit Scope(Phase x) : p(int(x) + 20 * Domain()), start(std::chrono::steady_clock::now()) {}
    ~Scope()
    {
        auto &d = Data()[p];
        d.seconds +=
            std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        ++d.calls;
    }
};
inline void Flush()
{
    const char *names[] = {
        "region",          "generation",      "truth", "graph",   "screen",    "entities",
        "materialization", "cascade",         "nets",  "density", "placement", "hpwl",
        "median",          "density_samples", "other", "factor",  "spatial",   "key"};
    for (int domain = 0; domain < 2; ++domain)
        for (int i = 0; i < 18; ++i)
            if (Data()[i + domain * 20].calls)
                std::printf("AGR_PIPE_PROFILE phase=%s domain=%s seconds=%.9f calls=%llu\n",
                            names[i], domain ? "commit" : "main", Data()[i + domain * 20].seconds,
                            Data()[i + domain * 20].calls);
    Data() = {};
}
#endif
} // namespace AgrSpeed
#ifdef ABC_AGR_PIPE_PROFILE
#define AGR_SPEED_SCOPE(phase) AgrSpeed::Scope agrSpeedScope(AgrSpeed::phase)
#define AGR_SPEED_FLUSH() AgrSpeed::Flush()
#define AGR_SPEED_COMMIT_DOMAIN() AgrSpeed::CommitDomain agrSpeedDomain
#else
#define AGR_SPEED_SCOPE(phase) ((void)0)
#define AGR_SPEED_FLUSH() ((void)0)
#define AGR_SPEED_COMMIT_DOMAIN() ((void)0)
#endif
#endif
