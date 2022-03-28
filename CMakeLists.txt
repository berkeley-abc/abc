cmake_minimum_required(VERSION 3.10.0)

# Add cmake modules of this project to the module path
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

# with at least one base tag, this can have dynamic (git) versioning:
#  git describe last tag = 1.1.0
#  git describe last tag + rev count = 1.1.0.45
#
# for now, set -DSCM_VERSION_INFO in the build env to override
if(NOT SCM_VERSION_INFO)
    set(LIBRARY_VERSION 1.1.0)
    set(SCM_VERSION_INFO ${LIBRARY_VERSION})
endif()
set(LIBRARY_SOVERSION 1)

project(
    abc
    LANGUAGES C CXX
    VERSION ${SCM_VERSION_INFO}
)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_VERBOSE_MAKEFILE ON)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(CMAKE_CXX_COMPILER_ID STREQUAL Clang)
    set(CLANG_DEFAULT_CXX_STDLIB libc++)
    set(CLANG_DEFAULT_RTLIB compiler-rt)
endif()

if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE
        "RelWithDebInfo"
        CACHE STRING "Default build type: RelWithDebInfo" FORCE
    )
endif()

include(CMakeParseArguments)
include(CTest)
include(GNUInstallDirs)

# LTO requires cmake min version 3.9 and clang LTO requires lld
if(ABC_ENABLE_LTO AND CMAKE_BUILD_TYPE MATCHES "Release")
    if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        find_package(LLVM CONFIG)
    endif()

    include(CheckIPOSupported)
    check_ipo_supported(RESULT ipo_supported OUTPUT error)

    if(ipo_supported)
        message(STATUS "IPO / LTO supported")
        set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
    else()
        message(WARNING "IPO / LTO not supported: <${error}>")
    endif()
endif()


set(ABC_USE_NAMESPACE "" CACHE STRING "ABC namespace")
option(ABC_USE_STDINT_H "Use C99 stdint.h header for platform-dependent types")
option(ABC_USE_NO_CUDD "Compile CUDD with ABC")
option(ABC_USE_NO_READLINE "Whether to use libreadline")
option(ABC_USE_NO_PTHREADS "Whether to compile with pthread support")
option(ABC_USE_PIC "Whether to compile into position independent code")
option(ABC_USE_LIBSTDCXX "Link explicitly to stdc++")
option(ABC_USE_SONAME "Set library soname")
option(BUILD_TESTING "Build and run tests" ON)
option(COVERAGE_BUILD "Enable source-based LLVM code coverage" OFF)
option(ABC_SKIP_EXE "Skip building executable (build libs only)" OFF)

add_library(abc_interface INTERFACE)

set(ABC_HEADERS
    src/base/main/abcapis_old.h
    src/base/main/abcapis.h
)

string(REPLACE "src/" "${CMAKE_CURRENT_SOURCE_DIR}/src/" ABC_HEADERS
               "${ABC_HEADERS}"
)

# Cache variable so this can be used in parent projects
set(abc_INCLUDE_DIR
    "${CMAKE_CURRENT_LIST_DIR}/src"
    CACHE INTERNAL "Directory where common headers are located"
)

set(ABC_MODULES
    src/base/abc src/base/abci src/base/cmd src/base/io src/base/main src/base/exor
    src/base/ver src/base/wlc src/base/wln src/base/acb src/base/bac src/base/cba src/base/pla src/base/test
    src/map/mapper src/map/mio src/map/super src/map/if
    src/map/amap src/map/cov src/map/scl src/map/mpm
    src/misc/extra src/misc/mvc src/misc/st src/misc/util src/misc/nm
    src/misc/vec src/misc/hash src/misc/tim src/misc/bzlib src/misc/zlib
    src/misc/mem src/misc/bar src/misc/bbl src/misc/parse
    src/opt/cut src/opt/fxu src/opt/fxch src/opt/rwr src/opt/mfs src/opt/sim
    src/opt/ret src/opt/fret src/opt/res src/opt/lpk src/opt/nwk src/opt/rwt
    src/opt/cgt src/opt/csw src/opt/dar src/opt/dau src/opt/dsc src/opt/sfm src/opt/sbd
    src/sat/bsat src/sat/xsat src/sat/satoko src/sat/csat src/sat/msat src/sat/psat src/sat/cnf src/sat/bmc src/sat/glucose src/sat/glucose2
    src/bool/bdc src/bool/deco src/bool/dec src/bool/kit src/bool/lucky
    src/bool/rsb src/bool/rpo
    src/proof/pdr src/proof/abs src/proof/live src/proof/ssc src/proof/int
    src/proof/cec src/proof/acec src/proof/dch src/proof/fraig src/proof/fra src/proof/ssw
    src/aig/aig src/aig/saig src/aig/gia src/aig/ioa src/aig/ivy src/aig/hop
    src/aig/miniaig
)

if(NOT ABC_SKIP_EXE)
    message(STATUS "Building abc main executable")
    set(BUILD_MAIN_EXE
        TRUE
        CACHE BOOL "Building executable" FORCE
    )
endif()

file(GLOB "src/ext*" ABC_EXTERNAL_MODULES)

if(ABC_EXTERNAL_MODULES)
    message(STATUS "External abc modules: ${ABC_EXTERNAL_MODULES}")
    list(APPEND ABC_MODULES ${ABC_EXTERNAL_MODULES})
endif()

target_compile_definitions(abc_interface INTERFACE $<$<CONFIG:Debug>:_DEBUG> $<$<NOT:$<CONFIG:Debug>>:NDEBUG>)
target_include_directories(
    abc_interface
    INTERFACE $<BUILD_INTERFACE:${abc_INCLUDE_DIR}>
              $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
)

target_link_libraries(abc_interface INTERFACE ${CMAKE_DL_LIBS})

if(NOT ABC_USE_NO_CUDD)
    message(STATUS "Compiling with CUDD")
    list(APPEND ABC_MODULES src/bdd/cudd src/bdd/extrab src/bdd/dsd src/bdd/epd src/bdd/mtr src/bdd/reo src/bdd/cas src/bdd/bbr src/bdd/llb)
    target_compile_definitions(abc_interface
        INTERFACE ABC_USE_CUDD=1
    )
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND NOT (CMAKE_CXX_COMPILER_VERSION VERSION_LESS "4.6.0"))
    target_compile_options(abc_interface
        INTERFACE -fno-aggressive-loop-optimizations -Wno-unused-but-set-variable
    )
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR CMAKE_CXX_COMPILER_ID STREQUAL "Clang" OR CMAKE_CXX_COMPILER_ID STREQUAL "AppleClang")
    target_compile_options(abc_interface
        INTERFACE
            -Wall -Wno-unused-function -Wno-write-strings -Wno-sign-compare -Wno-deprecated
    )
    target_link_libraries(abc_interface INTERFACE m)
    if(WIN32 OR ABC_USE_NAMESPACE)
        target_compile_options(abc_interface
            INTERFACE
                $<$<COMPILE_LANGUAGE:CXX>:-fpermissive>
                $<$<COMPILE_LANGUAGE:CXX>:-fvisibility=hidden>
        )
    endif()
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    target_compile_definitions(abc_interface
        INTERFACE
            "_CONSOLE"
            "_MBCS"
            "_SCL_SECURE_NO_WARNINGS"
            "_CRT_SECURE_NO_WARNINGS"
            "HAVE_STRUCT_TIMESPEC"
            "_XKEYCHECK_H"
    )
endif()
if(WIN32)
    if(MINGW OR MSYS)
        add_definitions(-DWIN32 -D__MINGW32__)
    endif()
    target_compile_definitions(abc_interface
        INTERFACE
            $<$<BOOL:${BUILD_SHARED_LIBS}>:ABC_DLL=ABC_DLLEXPORT>
            $<$<NOT:$<BOOL:${BUILD_SHARED_LIBS}>>:WIN32_NO_DLL>
            $<$<NOT:$<BOOL:${BUILD_SHARED_LIBS}>>:ABC_NO_DYNAMIC_LINKING>
    )
endif()

if(ABC_USE_NAMESPACE)
    message(STATUS "Compiling in namespace ${ABC_USE_NAMESPACE}")
    target_compile_definitions(abc_interface INTERFACE "ABC_NAMESPACE=${ABC_USE_NAMESPACE}")
else()
    set(ABC_USE_STDINT_H 1)
endif()

include(CheckTypeSize)

if(ABC_USE_STDINT_H)
    check_type_size("void*" SIZEOF_VOID_P LANGUAGE C)
    message(STATUS "Setting ABC_USE_STDINT_H ${ABC_USE_STDINT_H}")
    target_compile_definitions(abc_interface INTERFACE "ABC_USE_STDINT_H=1")
else()
    check_type_size("void*" SIZEOF_VOID_P LANGUAGE CXX)
    check_type_size(long SIZEOF_LONG LANGUAGE CXX)
    check_type_size(int SIZEOF_INT LANGUAGE CXX)
    if(WIN32 OR MINGW OR MSYS)
        set(ARCH_PREFIX "NT")
    elseif(UNIX OR APPLE)
        set(ARCH_PREFIX "LIN")
    else()
        message(FATAL_ERROR "Unknown arch")
    endif()
    if(SIZEOF_VOID_P EQUAL 4)
        set(ARCH_SUFFIX "")
    elseif(SIZEOF_VOID_P EQUAL 8)
        set(ARCH_SUFFIX "64")
    else()
        message(FATAL_ERROR "Unknown pointer size")
    endif()
    target_compile_definitions(abc_interface INTERFACE
        "SIZEOF_VOID_P=${SIZEOF_VOID_P}"
        "SIZEOF_LONG=${SIZEOF_LONG}"
        "SIZEOF_INT=${SIZEOF_INT}"
        "${ARCH_PREFIX}${ARCH_SUFFIX}"
    )
endif()

if(CMAKE_SYSTEM_PROCESS STREQUAL "arm")
    target_compile_definitions(abc_interface INTERFACE
        ABC_MEMALIGN=4
    )
endif()

if(NOT ABC_USE_NO_READLINE)
    message(STATUS "Using libreadline")
    target_compile_definitions(abc_interface
        INTERFACE ABC_USE_READLINE
    )
    find_path(ABC_READLINE_INCLUDES
        NAMES readline.h
        HINTS
            $ENV{READLINE_ROOT}
        PATH_SUFFIXES include include/readline
    )
    find_library(ABC_READLINE_LIBRARIES
        NAMES readline libreadline
        HINTS
            $ENV{READLINE_ROOT}
    )
    if(NOT ABC_READLINE_INCLUDES OR NOT ABC_READLINE_LIBRARIES)
        message(FATAL_ERROR "Could not find readline")
    endif()
    target_include_directories(abc_interface
        INTERFACE ${ABC_READLINE_INCLUDES}
    )
    target_link_libraries(abc_interface
        INTERFACE ${ABC_READLINE_LIBRARIES}
    )
endif()

if(NOT ABC_USE_NO_PTHREADS)
    message(STATUS "Using pthreads")
    target_compile_definitions(abc_interface
        INTERFACE ABC_USE_PTHREADS
    )
    if(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
        option(ABC_USE_EXTERNAL_PTHREAD "Use external pthread library")
        if(ABC_USE_EXTERNAL_PTHREAD)
            find_path(ABC_EXTERNAL_PTHREAD_INCLUDES
                NAMES pthread.h
                HINTS
                    $ENV{PTHREAD_ROOT}
                PATH_SUFFIXES include include/readline
            )
            find_library(ABC_EXTERNAL_PTHREAD_LIBRARIES
                NAMES pthread pthread_lib pthread_dll
                HINTS
                    $ENV{PTHREAD_ROOT}
            )
            set(ABC_PTHREAD_INCLUDES "${ABC_EXTERNAL_PTHREAD_INCLUDES}")
            set(ABC_PTHREAD_LIBRARIES "${ABC_EXTERNAL_PTHREAD_LIBRARIES}")
        else()
            if(SIZEOF_VOID_P EQUAL 8)
                set(PTHREAD_ARCH "x64")
            else()
                set(PTHREAD_ARCH "x86")
            endif()
            set(ABC_PTHREAD_INCLUDES "${abc_SOURCE_DIR}/lib")
            set(ABC_PTHREAD_LIBRARIES "${abc_SOURCE_DIR}/lib/${PTHREAD_ARCH}/pthreadVC2.lib")
            install(FILES "${abc_SOURCE_DIR}/lib/${PTHREAD_ARCH}/pthreadVC2.dll"
                DESTINATION "${CMAKE_INSTALL_BINDIR}"
            )
        endif()
        if(NOT ABC_PTHREAD_INCLUDES OR NOT ABC_PTHREAD_LIBRARIES)
            message(FATAL_ERROR "Could not find pthread")
        endif()
        target_include_directories(
            abc_interface
            INTERFACE $<BUILD_INTERFACE:${ABC_PTHREAD_INCLUDES}>
        )
        target_link_libraries(abc_interface INTERFACE ${ABC_PTHREAD_LIBRARIES})
    else()
        set(CMAKE_THREAD_PREFER_PTHREAD ON)
        set(THREADS_PREFER_PTHREAD_FLAG ON)
        find_package(Threads REQUIRED)
        target_link_libraries(abc_interface
            INTERFACE ${CMAKE_THREAD_LIBS_INIT}
        )
    endif()
endif()

if(ABC_USE_PIC)
    message(STATUS "Compiling position independent code")
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
endif()

if(ABC_USE_LIBSTDCXX OR NOT ABC_USE_NAMESPACE)
    if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
        message(STATUS "Using explicit -lstdc++")
        target_link_libraries(abc_interface
            INTERFACE stdc++
        )
    endif()
endif()

define_property(GLOBAL
    PROPERTY LIBABC_SOURCES
    BRIEF_DOCS "Sources of libabc"
    FULL_DOCS "All source files of libabc"
)

define_property(GLOBAL
    PROPERTY ABC_SOURCES
    BRIEF_DOCS "Sources of executables of abc"
    FULL_DOCS "All source files of abc"
)

function(abc_libabc_add_sources)
    cmake_parse_arguments(AAM "" "NAME" "SOURCES" ${ARGN})
    file(RELATIVE_PATH RELDIR "${abc_SOURCE_DIR}" "${CMAKE_CURRENT_LIST_DIR}")
    set(RELSOURCES)
    foreach(SOURCE ${AAM_SOURCES})
        list(APPEND RELSOURCES "${RELDIR}/${SOURCE}")
    endforeach()
    source_group("${RELDIR}" FILES "${AAM_SOURCES}")
    set_property(GLOBAL APPEND PROPERTY LIBABC_SOURCES ${RELSOURCES})
endfunction()

function(abc_add_executable)
    cmake_parse_arguments(AAE "" "NAME" "SOURCES" ${ARGN})
    file(RELATIVE_PATH RELDIR "${abc_SOURCE_DIR}" "${CMAKE_CURRENT_LIST_DIR}")
    set(RELSOURCES)
    foreach(SOURCE ${AAE_SOURCES})
        list(APPEND RELSOURCES "${RELDIR}${SOURCE}")
    endforeach()
    if(ABC_USE_NAMESPACE)
        set_source_files_properties(${AAE_SOURCES} PROPERTIES LANGUAGE CXX)
    endif()
    add_executable("${AAE_NAME}" ${AAE_SOURCES})
    target_link_libraries("${AAE_NAME}" PUBLIC libabc)
    set_property(GLOBAL APPEND PROPERTY ABC_SOURCES ${RELSOURCES})
endfunction()

foreach(ABC_MODULE ${ABC_MODULES})
    add_subdirectory("${ABC_MODULE}")
endforeach()

get_property(LIBABC_SOURCES GLOBAL PROPERTY LIBABC_SOURCES)
get_property(ABC_SOURCES GLOBAL PROPERTY ABC_SOURCES)

if(ABC_USE_NAMESPACE)
    set_source_files_properties(${LIBABC_SOURCES} PROPERTIES LANGUAGE CXX)
endif()

add_library(libabc ${LIBABC_SOURCES})
target_link_libraries(libabc PUBLIC abc_interface)
set_target_properties(libabc
    PROPERTIES OUTPUT_NAME "abc"
)

if(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    set_target_properties(libabc
        PROPERTIES OUTPUT_NAME "abc$<$<CONFIG:Debug>:d>$<$<NOT:$<CONFIG:Debug>>:r>"
    )
endif()

if(BUILD_SHARED_LIBS)
    if(ABC_USE_SONAME)
        set_target_properties(
            libabc PROPERTIES VERSION ${LIBRARY_VERSION}
                              SOVERSION ${LIBRARY_SOVERSION}
                              WINDOWS_EXPORT_ALL_SYMBOLS TRUE
        )
    endif()
endif()

install(FILES ${ABC_HEADERS}
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/abc
)

install(
    TARGETS abc_interface libabc
    EXPORT abcConfig
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
    INCLUDES
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

install(EXPORT abcConfig
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/abc NAMESPACE abc::)

if(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    if(BUILD_SHARED_LIBS)
        install(FILES $<TARGET_PDB_FILE:libabc> DESTINATION bin OPTIONAL)
    endif()
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    if(ABC_ENABLE_LTO AND ipo_supported)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=lld")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -fuse-ld=lld")
    endif()
endif()

if(BUILD_TESTING)
    set(test_SRCS src/demo.c)
    if(ABC_USE_NAMESPACE)
        set_source_files_properties(${test_SRCS} PROPERTIES LANGUAGE CXX)
    endif()
    add_executable(base_test ${test_SRCS})
    target_link_libraries(base_test PUBLIC libabc)

    enable_testing()
    add_test(NAME base_test
        COMMAND base_test i10.aig
        WORKING_DIRECTORY "${abc_SOURCE_DIR}"
    )

    # Add source-based llvm code coverage targets.
    # Note this requires recent clang/llvm tooling.
    if(COVERAGE_BUILD)
        add_test(NAME main_test
            COMMAND abc -c "r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec"
            WORKING_DIRECTORY "${abc_SOURCE_DIR}"
        )

        include(coverage)
        add_coverage(abc)
        add_coverage(base_test)
    endif()
endif()

add_custom_target(etags
    etags ${LIBABC_SOURCES} ${ABC_SOURCES}
    COMMENT "Generating etags"
    WORKING_DIRECTORY "${abc_SOURCE_DIR}"
)

add_custom_target(docs
    doxygen doxygen.conf
    COMMENT "Building documentation."
    WORKING_DIRECTORY "${abc_SOURCE_DIR}"
)
