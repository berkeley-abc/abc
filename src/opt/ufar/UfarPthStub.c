// No-op stubs for the subset of pthread functions referenced by UfarPth.cpp.
// Linked into libabc only when no real pthread implementation is available
// (currently: MSVC builds, where ABC_USE_PTHREADS is not set).
// RunConcurrentSolver simply won't do real parallel work in this build.

#include "../../../lib/pthread.h"

int pthread_create(pthread_t * thread, const pthread_attr_t * attr,
                   void * (*start_routine)(void *), void * arg)
{
    (void)thread; (void)attr; (void)start_routine; (void)arg;
    return -1;
}

void pthread_exit(void * retval) { (void)retval; }

int pthread_join(pthread_t thread, void ** retval)
{
    (void)thread; (void)retval;
    return 0;
}

int pthread_mutex_lock(pthread_mutex_t * mutex) { (void)mutex; return 0; }
int pthread_mutex_unlock(pthread_mutex_t * mutex) { (void)mutex; return 0; }

int pthread_cond_timedwait(pthread_cond_t * cond, pthread_mutex_t * mutex,
                           const struct timespec * abstime)
{
    (void)cond; (void)mutex; (void)abstime;
    return 0;
}

int pthread_cond_signal(pthread_cond_t * cond) { (void)cond; return 0; }
