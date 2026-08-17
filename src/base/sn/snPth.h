/**CFile****************************************************************

  FileName    [snPth.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New word-level design interface.]

  Synopsis    [Bounded worker support for parallel SN mapping jobs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: snPth.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#ifndef SN_PTH_H
#define SN_PTH_H

// Small self-contained pthread scheduler for SN passes. The requested process count includes the coordinating caller,
// so P > 1 creates exactly P-1 workers. Windows and builds without ABC_USE_PTHREADS compile this scheduler as a
// sequential loop, avoiding any SN dependency on pthreads while retaining full P=1 functionality.

#include <assert.h>
#include <stddef.h>
#include <stdlib.h>

#if defined(ABC_USE_PTHREADS) && !defined(_WIN32)
#define SN_PTH_USE_THREADS 1
#include <pthread.h>
#else
#define SN_PTH_USE_THREADS 0
#endif

ABC_NAMESPACE_HEADER_START

typedef void (*sn_pth_job_fn)(void* context, void* job);

typedef struct sn_pth_pool_t
{
    void** jobs;
    size_t count;
    size_t next;
    void* context;
    sn_pth_job_fn function;
#if SN_PTH_USE_THREADS
    pthread_mutex_t mutex;
#endif
} sn_pth_pool_t;

#if SN_PTH_USE_THREADS
static inline void* sn_pth_worker(void* argument)
{
    sn_pth_pool_t* pool = (sn_pth_pool_t*)argument;
    for (;;)
    {
        size_t index;
        int status = pthread_mutex_lock(&pool->mutex);
        if (status != 0)
            return NULL;
        index = pool->next++;
        status = pthread_mutex_unlock(&pool->mutex);
        assert(status == 0);
        (void)status;
        if (index >= pool->count)
            return NULL;
        pool->function(pool->context, pool->jobs[index]);
    }
}
#endif

static inline int sn_pth_parallel_available(void)
{
    return SN_PTH_USE_THREADS;
}

static inline void sn_pth_process(void** jobs, size_t count, unsigned processes,
                                  sn_pth_job_fn function, void* context)
{
    assert((jobs || count == 0) && processes >= 1 && function);
#if !SN_PTH_USE_THREADS
    (void)processes;
    for (size_t i = 0; i < count; i++)
        function(context, jobs[i]);
#else
    if (processes == 1 || count < 2)
    {
        for (size_t i = 0; i < count; i++)
            function(context, jobs[i]);
        return;
    }
    unsigned worker_count = processes - 1;
    if (worker_count > count)
        worker_count = (unsigned)count;
    sn_pth_pool_t pool;
    pool.jobs = jobs;
    pool.count = count;
    pool.next = 0;
    pool.context = context;
    pool.function = function;
    int status = pthread_mutex_init(&pool.mutex, NULL);
    if (status != 0)
    {
        for (size_t i = 0; i < count; i++)
            function(context, jobs[i]);
        return;
    }
    pthread_t* workers = (pthread_t*)malloc(sizeof(pthread_t) * worker_count);
    if (!workers)
    {
        status = pthread_mutex_destroy(&pool.mutex);
        assert(status == 0);
        (void)status;
        for (size_t i = 0; i < count; i++)
            function(context, jobs[i]);
        return;
    }
    unsigned created = 0;
    for (; created < worker_count; created++)
    {
        if (pthread_create(&workers[created], NULL, sn_pth_worker, &pool) != 0)
            break;
    }
    for (unsigned i = 0; i < created; i++)
    {
        int status = pthread_join(workers[i], NULL);
        assert(status == 0);
        (void)status;
    }
    // A worker that could not use the mutex leaves its unclaimed suffix for the coordinator.
    while (pool.next < count)
        function(context, jobs[pool.next++]);
    status = pthread_mutex_destroy(&pool.mutex);
    assert(status == 0);
    (void)status;
    free(workers);
#endif
}

#undef SN_PTH_USE_THREADS

ABC_NAMESPACE_HEADER_END

#endif
