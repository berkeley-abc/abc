/*
 * util.h
 *
 *  Created on: Aug 31, 2015
 *      Author: Yen-Sheng Ho
 */

#ifndef SRC_EXT2_UTIL_UTIL_H_
#define SRC_EXT2_UTIL_UTIL_H_

/* http://stackoverflow.com/questions/6168107/how-to-implement-a-good-debug-logging-feature-in-a-project */

#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <vector>

#ifdef _WIN32
// Define timeval before windows.h to prevent winsock.h forward declaration conflicts
#ifndef _TIMEVAL_DEFINED
#define _TIMEVAL_DEFINED
struct timeval {
    long tv_sec;
    long tv_usec;
};
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>

static inline int gettimeofday(struct timeval *tv, struct timezone *tz) {
    if (tv) {
        FILETIME ft;
        GetSystemTimeAsFileTime(&ft);
        ULARGE_INTEGER uli;
        uli.LowPart = ft.dwLowDateTime;
        uli.HighPart = ft.dwHighDateTime;
        ULONGLONG time_in_us = (uli.QuadPart - 116444736000000000ULL) / 10ULL;
        tv->tv_sec = (long)(time_in_us / 1000000ULL);
        tv->tv_usec = (long)(time_in_us % 1000000ULL);
    }
    (void)tz;
    return 0;
}
#else
#include <sys/time.h>
#endif

#include "misc/util/abc_namespaces.h"

ABC_NAMESPACE_CXX_HEADER_START

class LogT {
    public:
        LogT(unsigned _loglevel = 0) {
            // _buffer << "LOG" << _loglevel << " :" << std::string(_loglevel > 0 ? _loglevel * 4 : 1, ' ');
            _buffer << prefix << " :" << std::string(_loglevel > 0 ? _loglevel * 4 : 1, ' ');
        }

        template<typename T>
        LogT & operator<<(T const & value) {
            _buffer << value;
            return *this;
        }

        ~LogT() {
            std::cout << _buffer.str() << std::endl;
        }

        static unsigned loglevel;
        static std::string prefix;
    private:
        std::ostringstream _buffer;
};

#define LOG(level) \
if (level > LogT::loglevel) ; \
else LogT(level)

class OptMgr {
    public:
        OptMgr(const std::string& cmd) : _cmd(cmd) {}
        bool Parse(int argc, char * argv[]);
        void AddOpt(const std::string& opt, const std::string& default_val, const std::string& arg_type, const std::string& help) {
            _map[opt] = Option(default_val, arg_type, help);
        }
        std::string GetOptVal(const std::string& opt) {return _map[opt]._val;}
        bool operator[](const std::string& opt) {return _has_opt(opt);}

        void PrintUsage();
    private:
        struct Option {
            Option(){}
            Option(const std::string& val, const std::string& arg_type, const std::string& help) :
                _default(val), _help(help), _arg_type(arg_type){}
            bool isBool() {return _arg_type == "";}
            std::string _default;
            std::string _help;
            std::string _arg_type;
            std::string _val;
        };

        bool _has_opt(const std::string& opt) {return !_map[opt]._val.empty();}

        std::map<std::string, Option> _map;
        std::string _cmd;
};

static inline unsigned elapsed_time_usec(const timeval& tBefore, const timeval& tAfter) {
    return (tAfter.tv_sec - tBefore.tv_sec)*1000000 + (tAfter.tv_usec - tBefore.tv_usec);
}

void kill_on_parent_death(int sig);

int call_python(const char* modulename, const char* funcname, const char* aig, std::vector<int>& cex);

ABC_NAMESPACE_CXX_HEADER_END

#endif /* SRC_EXT2_UTIL_UTIL_H_ */
