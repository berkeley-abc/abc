cmake_minimum_required(VERSION 3.25)

project(abc
    VERSION 1.0.0
    DESCRIPTION "ABC: System for Sequential Logic Synthesis and Formal Verification"
    HOMEPAGE_URL "https://people.eecs.berkeley.edu/~alanmi/abc/"
    LANGUAGES C CXX
)

include(GNUInstallDirs)

if (MSVC)

    set(CMAKE_C_STANDARD 11)
    set(CMAKE_C_STANDARD_REQUIRED ON)
    set(CMAKE_C_EXTENSIONS ON)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)

    # Embed debug info in each .obj instead of writing to a shared .pdb. With
    # ~1370 parallel TUs the shared PDB triggers C1041 even with /FS.
    # CMP0141 (CMake 3.25+) routes this through MSBuild's
    # <DebugInformationFormat> rather than injecting /Zi into CMAKE_*_FLAGS_*.
    set(CMAKE_MSVC_DEBUG_INFORMATION_FORMAT "$<$<CONFIG:Debug,RelWithDebInfo>:Embedded>")


    # Source discovery: parse the per-directory module.make files. The upstream 
    # Makefile (Makefile:35-53,91,171) treats those module.make files as the canonical
    # source list;
    file(READ "${CMAKE_CURRENT_SOURCE_DIR}/Makefile" abc_mk_text)
    string(REGEX REPLACE "\\\\[\r\n]+" " " abc_mk_text "${abc_mk_text}")
    string(REGEX MATCH "MODULES[ \t]*:=[^\n]*" abc_mk_init "${abc_mk_text}")
    string(REGEX MATCHALL "MODULES[ \t]*\\+=[^\n]+" abc_mk_appends "${abc_mk_text}")
    set(abc_mk_modules "${abc_mk_init}")
    foreach(abc_mk_line IN LISTS abc_mk_appends)
        string(APPEND abc_mk_modules " ${abc_mk_line}")
    endforeach()

    file(GLOB abc_ext_dirs RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}"
        "${CMAKE_CURRENT_SOURCE_DIR}/src/ext*")
    string(JOIN " " abc_ext_str ${abc_ext_dirs})
    string(REGEX REPLACE "\\$\\(wildcard[^)]+\\)" "${abc_ext_str}"
        abc_mk_modules "${abc_mk_modules}")

    string(REGEX MATCHALL "src/[A-Za-z0-9_/]+" ABC_MODULES "${abc_mk_modules}")
    list(REMOVE_DUPLICATES ABC_MODULES)
    list(LENGTH ABC_MODULES ABC_MODULES_COUNT)
    message(STATUS "abc: ${ABC_MODULES_COUNT} module dirs discovered from Makefile")

    set(ABC_SRC "")
    foreach(abc_mod IN LISTS ABC_MODULES)
        set(abc_mod_file "${CMAKE_CURRENT_SOURCE_DIR}/${abc_mod}/module.make")
        if(NOT EXISTS "${abc_mod_file}")
            message(WARNING "abc: missing ${abc_mod_file}")
            continue()
        endif()
        file(READ "${abc_mod_file}" abc_mod_text)
        # collapse "\<newline>" line continuations so each path is one token
        string(REGEX REPLACE "\\\\[\r\n]+" " " abc_mod_text "${abc_mod_text}")
        # alternation must list cpp before c — CMake regex picks the first match, not the longest
        string(REGEX MATCHALL "src/[A-Za-z0-9_/]+\\.(cpp|c)" abc_mod_srcs "${abc_mod_text}")
        foreach(abc_src_rel IN LISTS abc_mod_srcs)
            set(abc_src_abs "${CMAKE_CURRENT_SOURCE_DIR}/${abc_src_rel}")
            if(NOT EXISTS "${abc_src_abs}")
                message(FATAL_ERROR "abc: ${abc_mod_file} references missing ${abc_src_rel}")
            endif()
            list(APPEND ABC_SRC "${abc_src_abs}")
        endforeach()
    endforeach()

    list(LENGTH ABC_SRC ABC_SRC_COUNT)
    message(STATUS "abc: ${ABC_SRC_COUNT} sources from module.make files")

    # UfarPth.cpp unconditionally references pthread_*; supply no-op stubs for the linker
    list(APPEND ABC_SRC "${CMAKE_CURRENT_SOURCE_DIR}/src/opt/ufar/UfarPthStub.c")

    set(ABC_MAIN_SRC "${CMAKE_CURRENT_SOURCE_DIR}/src/base/main/main.c")
    list(REMOVE_ITEM ABC_SRC "${ABC_MAIN_SRC}")

    add_library(libabc STATIC ${ABC_SRC})
    add_executable(abc "${ABC_MAIN_SRC}")
    target_link_libraries(abc PRIVATE libabc)

    set(ABC_COMMON_DEFS
        WIN32=1
        NT=1
        NT64=1
        ABC_USE_CUDD=1
        ABC_USE_STDINT_H=1
        # Static build: make ABC_DLLEXPORT/IMPORT (and thus ABC_DLL) expand to nothing.
        # Defining ABC_DLL=1 would substitute the literal "1" into every
        # `extern ABC_DLL int Foo();` declaration in the headers.
        WIN32_NO_DLL=1
        # Keeps <windows.h> from pulling in <winsock.h>, which would re-define
        # struct timeval without setting _TIMEVAL_DEFINED and break the
        # in-tree timeval guards in util.h / UfarMgr.h.
        WIN32_LEAN_AND_MEAN=1
        # Tells the in-tree pthreads-win32 shim (lib/pthread.h) that struct
        # timespec is already available (UCRT defines it in <time.h>).
        HAVE_STRUCT_TIMESPEC=1
        # Tells lib/pthread.h to declare pthread_* as plain extern (not
        # dllimport), so our local stubs in UfarPthStub.c can satisfy them.
        PTW32_STATIC_LIB=1
        _CRT_SECURE_NO_WARNINGS=1
        _CRT_NONSTDC_NO_DEPRECATE=1
        # giaCTas2.c reuses fVal/fValOld as bitfield names; remap to avoid clash with local helpers
        fVal=Value
        fValOld=ValueOld
    )

    set(ABC_COMMON_OPTS /W1 /Zc:preprocessor /wd4005)

    set(ABC_COMMON_INCS
        "${CMAKE_CURRENT_SOURCE_DIR}/src"
        "${CMAKE_CURRENT_SOURCE_DIR}/src/misc/util"
        "${CMAKE_CURRENT_SOURCE_DIR}/src/aig"
        "${CMAKE_CURRENT_SOURCE_DIR}/src/opt"
    )

    foreach(abc_tgt libabc abc)
        target_compile_definitions(${abc_tgt} PRIVATE ${ABC_COMMON_DEFS})
        target_compile_options(${abc_tgt} PRIVATE ${ABC_COMMON_OPTS})
        # /TC + /std:c11 only apply to C TUs (a few module sources are .cpp)
        target_compile_options(${abc_tgt} PRIVATE
            $<$<COMPILE_LANGUAGE:C>:/TC>
            $<$<COMPILE_LANGUAGE:C>:/std:c11>
        )
        target_include_directories(${abc_tgt} PRIVATE ${ABC_COMMON_INCS})
    endforeach()

else()

    include(CMakeParseArguments)
    include(CheckCCompilerFlag)
    include(CheckCXXCompilerFlag)
    # Generate compilation database compile_commands.json
    set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

    # Default c++ standard used unless otherwise specified in target_compile_features.
    set(CMAKE_CXX_STANDARD 17 CACHE STRING "the C++ standard to use for this project")
    set(CMAKE_CXX_STANDARD_REQUIRED ON)

    function(addprefix var prefix)
        foreach( s ${ARGN} )
            list(APPEND tmp "-I${s}")
        endforeach()
        set(${var} ${tmp} PARENT_SCOPE)
    endfunction()

    # filter out flags that are not appropriate for the compiler being used
    function(target_compile_options_filtered target visibility)
        foreach( flag ${ARGN} )
            if( flag MATCHES "^-D.*" )
                target_compile_options( ${target} ${visibility} ${flag} )
            else()
                check_c_compiler_flag( ${flag} C_COMPILER_SUPPORTS__${flag} )
                if( C_COMPILER_SUPPORTS__${flag} )
                    target_compile_options( ${target} ${visibility} $<$<COMPILE_LANGUAGE:C>:${flag}> )
                endif()

                check_cxx_compiler_flag( ${flag} CXX_COMPILER_SUPPORTS__${flag} )
                if( CXX_COMPILER_SUPPORTS__${flag} )
                    target_compile_options( ${target} ${visibility} $<$<COMPILE_LANGUAGE:CXX>:${flag}>  )
                endif()
            endif()
        endforeach()
    endfunction()

    if(READLINE_FOUND MATCHES TRUE)
        addprefix(ABC_READLINE_INCLUDES_FLAGS "-I" ${READLINE_INCLUDE})
        string(REPLACE ";" " " ABC_READLINE_INCLUDES_FLAGS "${ABC_READLINE_INCLUDES_FLAGS}")
        list(APPEND ABC_READLINE_FLAGS "ABC_READLINE_INCLUDES=${ABC_READLINE_INCLUDES_FLAGS}")

        string(REPLACE ";" " " ABC_READLINE_LIBRARIES_FLAGS "${READLINE_LIBRARIES}")
        list(APPEND ABC_READLINE_FLAGS "ABC_READLINE_LIBRARIES=${ABC_READLINE_LIBRARIES_FLAGS}")
    elseif(READLINE_FOUND MATCHES FALSE)
        list(APPEND ABC_READLINE_FLAGS "ABC_USE_NO_READLINE=1")
    endif()

    if(ABC_USE_NAMESPACE)
        set(ABC_USE_NAMESPACE_FLAGS "ABC_USE_NAMESPACE=${ABC_USE_NAMESPACE}")
    endif()

    if( APPLE )
        set(make_env ${CMAKE_COMMAND} -E env SDKROOT=${CMAKE_OSX_SYSROOT})
    endif()

    # run make to extract compiler options, linker options and list of source files
    execute_process(
    COMMAND
        ${make_env}
        make
            ${ABC_READLINE_FLAGS}
            ${ABC_USE_NAMESPACE_FLAGS}
            ARCHFLAGS_EXE=${CMAKE_CURRENT_BINARY_DIR}/abc_arch_flags_program.exe
            ABC_MAKE_NO_DEPS=1
            CC=${CMAKE_C_COMPILER}
            CXX=${CMAKE_CXX_COMPILER}
            LD=${CMAKE_CXX_COMPILER}
            cmake_info
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    OUTPUT_VARIABLE MAKE_OUTPUT
    )

    # extract options from make output
    function(extract_var SEPARATOR DEST_VARIABLE MAKE_OUTPUT)
    string(REGEX MATCH "${SEPARATOR} .* ${SEPARATOR}" TMP "${MAKE_OUTPUT}")
    string(REGEX REPLACE "${SEPARATOR} (.*) ${SEPARATOR}" "\\1" TMP "${TMP}")

    separate_arguments(TMP)

    set(${DEST_VARIABLE} ${TMP} PARENT_SCOPE)
    endfunction()

    extract_var(SEPARATOR_SRC ABC_SRC ${MAKE_OUTPUT})
    extract_var(SEPARATOR_LIBS ABC_LIBS ${MAKE_OUTPUT})
    extract_var(SEPARATOR_CFLAGS ABC_CFLAGS ${MAKE_OUTPUT})
    extract_var(SEPARATOR_CXXFLAGS ABC_CXXFLAGS ${MAKE_OUTPUT})

    if(ABC_USE_NAMESPACE)
        set_source_files_properties(${ABC_SRC} PROPERTIES LANGUAGE CXX)
    endif()

    function(abc_properties target visibility)
        target_include_directories(${target} ${visibility} $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>)
        target_compile_options_filtered(${target} ${visibility} ${ABC_CFLAGS} ${ABC_CXXFLAGS} -Wno-unused-but-set-variable )
        target_link_libraries(${target} ${visibility} ${ABC_LIBS})
    endfunction()

    set(ABC_MAIN_SRC src/base/main/main.c)
    list(REMOVE_ITEM ABC_SRC ${ABC_MAIN_SRC})

    add_library(libabc EXCLUDE_FROM_ALL ${ABC_SRC})
    abc_properties(libabc PUBLIC)
    set_property(TARGET libabc PROPERTY OUTPUT_NAME abc)

    add_executable(abc ${ABC_MAIN_SRC})
    target_link_libraries(abc PRIVATE libabc)
    abc_properties(abc PRIVATE)

    add_library(libabc-pic EXCLUDE_FROM_ALL ${ABC_SRC})
    abc_properties(libabc-pic PUBLIC)
    set_property(TARGET libabc-pic PROPERTY POSITION_INDEPENDENT_CODE ON)
    set_property(TARGET libabc-pic PROPERTY OUTPUT_NAME abc-pic)

    if(NOT DEFINED ABC_SKIP_TESTS)
        enable_testing()
        include(FetchContent)
        FetchContent_Declare(
        googletest
        DOWNLOAD_EXTRACT_TIMESTAMP TRUE
        # Specify the commit you depend on and update it regularly.
        URL "https://github.com/google/googletest/archive/refs/tags/v1.14.0.zip"
        )
        FetchContent_MakeAvailable(googletest)
        include(GoogleTest)
        add_subdirectory(test)
    endif()
endif()

# ----------------------------------------------------------------------------
# Installation rules
# ----------------------------------------------------------------------------
# Layout (with the default CMAKE_INSTALL_PREFIX on each platform):
#   <prefix>/bin/abc[.exe]                               -- driver executable
#   <prefix>/lib/libabc.a   or  <prefix>/lib/libabc.lib  -- static library
#   <prefix>/include/abc/<...>                           -- full src/ header tree
#   <prefix>/lib/cmake/abc/abcConfig.cmake               -- find_package(abc) entry
#   <prefix>/lib/cmake/abc/abcConfigVersion.cmake
#   <prefix>/lib/cmake/abc/abcTargets*.cmake
#
# Downstream usage:
#   project(my_tool LANGUAGES C CXX)    # CXX required even for pure-C consumers:
#                                       # libabc carries C++ TUs (cadical, eslim, ...)
#                                       # so the link line needs the C++ runtime.
#   find_package(abc CONFIG REQUIRED)
#   target_link_libraries(my_tool PRIVATE abc::abc)
#
# ABC's headers cross-reference each other with paths like "misc/vec/vec.h",
# so the public include root is exposed as <prefix>/include/abc; consumers
# spell includes the same way the ABC sources do, e.g. <base/main/main.h>
# (no leading abc/ prefix).

include(CMakePackageConfigHelpers)

add_library(abc::abc ALIAS libabc)
set_target_properties(libabc PROPERTIES EXPORT_NAME abc)

target_include_directories(libabc INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}/abc>
)

target_compile_definitions(libabc INTERFACE WIN32_NO_DLL)

install(TARGETS abc RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

install(TARGETS libabc
    EXPORT abcTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/src/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/abc
    FILES_MATCHING
        PATTERN "*.h"
        PATTERN "*.hpp"
)

install(EXPORT abcTargets
    FILE abcTargets.cmake
    NAMESPACE abc::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/abc
)

configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/abcConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/abcConfig.cmake"
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/abc
)

write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/abcConfigVersion.cmake"
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/abcConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/abcConfigVersion.cmake"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/abc
)
