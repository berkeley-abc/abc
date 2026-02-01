/*
 * util.cpp
 *
 *  Created on: Aug 31, 2015
 *      Author: Yen-Sheng Ho
 */

#include <iomanip>
#if !defined(__wasm)
#include <csignal>
#endif
#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

#ifdef __linux__
#include <sys/prctl.h>
#elif defined(__APPLE__)
#include <thread>
#include <cassert>
#include <cerrno>
#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>
#endif

#include "util.h"

ABC_NAMESPACE_IMPL_START

using namespace std;

unsigned LogT::loglevel = 0;
string LogT::prefix = "LOG";

bool OptMgr::Parse(int argc, char * argv[]) {
    if(argc <= 1) return true;

    for(int i = 1; i < argc; i++) {
        if(_map.count(argv[i]) == 0)
            return false;

        Option& opt = _map[argv[i]];
        opt._val = "yes";

        if(!opt.isBool()) {
            if (i + 1 == argc)
                return false;
            opt._val = argv[++i];
        }
    }

    return true;
}

void OptMgr::PrintUsage() {
    cout << "usage: " << _cmd << endl;
    cout << "       Uninterpreted Function Abstraction and Refinement (UFAR)\n";
    for (auto x : _map) {
        ostringstream ss;
        ss << x.first << " " << (x.second.isBool() ? "" : x.second._arg_type);
        cout << "       " << setw(10) << left << ss.str();
        cout << " : " << x.second._help << " [default = " << x.second._default << "]" << endl;
    }
}

#ifdef __linux__

void kill_on_parent_death(int sig)
{
    // kill process if parent dies
    prctl(PR_SET_PDEATHSIG, sig);

    // the parent might have died before calling prctl
    // in that case, it would be adopted by init, whose pid is 1
    if (getppid() == 1)
    {
        raise(sig);
    }
}

#elif defined(__APPLE__)

template <typename Func>
static auto retry_eintr(Func &&fn) -> decltype(fn())
{
    decltype(fn()) rc;
    do {
        rc = fn();
    } while (rc == -1 && errno == EINTR);
    return rc;
}

void kill_on_parent_death(int sig)
{
  const int ppid = getppid();

  std::thread monitor_thread([ppid, sig](){

    struct kevent change;
    EV_SET(&change, ppid, EVFILT_PROC, EV_ADD, NOTE_EXIT, 0, nullptr);

    int kq = kqueue();
    assert( kq >= 0 );

    struct kevent event;
    struct timespec ts = {0, 0};

    // start listening, we are guaranteed to receive a notification if ppid is dead
    kevent(kq, &change, 1, &event, 1, &ts);

    // however, if ppid died before the call to kevent, ppid might not be the pid of the parent
    // in that case, it would be adopted by init, whose pid is 1
    if( getppid() == 1 )
    {
      raise(sig);
    }

    // now block on kevent until the the parent process dies
    retry_eintr([&](){
       return kevent(kq, &change, 1, &event, 1, nullptr);
    });

    raise(sig);
  });

  monitor_thread.detach();
}

#else // neither linux or OS X

void kill_on_parent_death(int sig)
{
}

#endif

ABC_NAMESPACE_IMPL_END
