/**CFile****************************************************************

  FileName    [paWorkspace.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Placement-aware synthesis.]

  Synopsis    [Reusable scratch containers.]

  Author      [Anqi Lu]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

  Revision    [$Id: paWorkspace.h,v 1.00 2026/11/27 00:00:00 anqilu Exp $]

***********************************************************************/

#ifndef ABC__opt__pa__paWorkspace_h
#define ABC__opt__pa__paWorkspace_h
#include <array>
#include <vector>
#include <cstdlib>
namespace PaWorkspace
{
// Reuses the storage of destroyed vectors (never their contents); a live
// vector owns its buffer. Each thread has its own pool, bounded in count and
// capacity.
template <class T> class WorkspaceVector : public std::vector<T>
{
    using Base = std::vector<T>;
    static bool & Stopping()
    {
        static thread_local bool value = false;
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
    static std::vector<Base> & Pool()
    {
        static thread_local PoolStorage storage;
        return storage.buffers;
    }

public:
    using Base::operator=;
    WorkspaceVector()
    {
        if ( !Pool().empty() )
        {
            this->swap(Pool().back());
            Pool().pop_back();
        }
    }
    explicit WorkspaceVector(size_t count) : WorkspaceVector()
    {
        this->resize(count);
    }
    WorkspaceVector(size_t count, const T & value) : WorkspaceVector()
    {
        this->assign(count, value);
    }
    WorkspaceVector(const Base & other) : WorkspaceVector()
    {
        this->assign(other.begin(), other.end());
    }
    WorkspaceVector(const WorkspaceVector & other) : WorkspaceVector()
    {
        this->assign(other.begin(), other.end());
    }
    WorkspaceVector(WorkspaceVector && other) noexcept : Base(std::move(other))
    {
    }
    WorkspaceVector & operator=(const WorkspaceVector & other)
    {
        Base::operator=(other);
        return *this;
    }
    WorkspaceVector & operator=(WorkspaceVector && other) noexcept
    {
        Base::operator=(std::move(other));
        return *this;
    }
    ~WorkspaceVector()
    {
        if ( !Stopping() && this->capacity() <= 8192 && Pool().size() < 32 )
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
    bool small = true;
    size_t size() const
    {
        return count;
    }
    int * begin()
    {
        return small || !count ? local.data() : large.data();
    }
    const int * begin() const
    {
        return small || !count ? local.data() : large.data();
    }
    int * end()
    {
        return begin() + count;
    }
    const int * end() const
    {
        return begin() + count;
    }
    void push_back(int value)
    {
        if ( small && count < 4 )
            local[count++] = value;
        else
        {
            if ( small )
            {
                large.assign(local.begin(), local.begin() + count);
                small = false;
            }
            large.push_back(value);
            ++count;
        }
    }
    void erase(int * first, int * last)
    {
        size_t a = first - begin(), b = last - begin();
        if ( small )
        {
            for ( size_t i = b; i < count; ++i )
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
        if ( n > N )
            large.resize(n);
    }
    T * data()
    {
        return count > N ? large.data() : local.data();
    }
    T & operator[](size_t i)
    {
        return data()[i];
    }
};
} // namespace PaWorkspace
#endif
