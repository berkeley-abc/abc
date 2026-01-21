/*
 * winsock_compat.h
 * 
 * Compatibility header for timeval on Windows
 * This must be included BEFORE windows.h to prevent winsock.h forward declaration conflicts
 */

#ifndef SRC_MISC_UTIL_WINSOCK_COMPAT_H_
#define SRC_MISC_UTIL_WINSOCK_COMPAT_H_

#ifdef _WIN32

// Define timeval before windows.h includes winsock.h
// This prevents winsock.h from forward declaring it as an incomplete type
struct timeval {
    long tv_sec;
    long tv_usec;
};

#endif /* _WIN32 */

#endif /* SRC_MISC_UTIL_WINSOCK_COMPAT_H_ */