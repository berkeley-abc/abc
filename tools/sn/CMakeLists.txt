cmake_minimum_required(VERSION 3.28)
project(sn LANGUAGES CXX)
if(MSVC)
    message(FATAL_ERROR "The optional Slang-to-SN companion is not supported on Windows")
endif()
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

get_filename_component(ABC_DEFAULT_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
set(ABC_SOURCE_DIR "${ABC_DEFAULT_SOURCE_DIR}" CACHE PATH "ABC source directory")
if(NOT EXISTS "${ABC_SOURCE_DIR}/src/base/sn/sn.h")
    message(FATAL_ERROR "ABC_SOURCE_DIR must contain src/base/sn/sn.h")
endif()

if(NOT TARGET slang::slang)
    set(SLANG_SOURCE_DIR "" CACHE PATH "Existing Slang checkout; empty downloads the pinned revision")
    set(SLANG_REVISION "43028607069b954beaf3f5afd5a73016957c0162" CACHE STRING "Pinned Slang revision")

    set(BUILD_SHARED_LIBS OFF CACHE BOOL "" FORCE)
    set(SLANG_INCLUDE_TOOLS OFF CACHE BOOL "" FORCE)
    set(SLANG_INCLUDE_TESTS OFF CACHE BOOL "" FORCE)
    set(SLANG_INCLUDE_EXAMPLES OFF CACHE BOOL "" FORCE)
    set(SLANG_INCLUDE_INSTALL OFF CACHE BOOL "" FORCE)
    set(SLANG_USE_MIMALLOC OFF CACHE BOOL "" FORCE)
    # Use explicit URLs: this Slang revision otherwise derives a prefix from the
    # caller's Git remote, which is unavailable in source archives and some builds.
    include(FetchContent)
    FetchContent_Declare(fmt GIT_REPOSITORY https://github.com/fmtlib/fmt.git
        GIT_TAG 12.2.0 GIT_SHALLOW ON SYSTEM EXCLUDE_FROM_ALL)
    FetchContent_Declare(boost_regex GIT_REPOSITORY https://github.com/MikePopoloski/regex.git
        GIT_TAG boost-1.91.0 GIT_SHALLOW ON SOURCE_SUBDIR _no_build_)
    FetchContent_Declare(tomlplusplus GIT_REPOSITORY https://github.com/marzer/tomlplusplus.git
        GIT_TAG v3.4.0 GIT_SHALLOW ON FIND_PACKAGE_ARGS 3.4)
    if(SLANG_SOURCE_DIR)
        if(NOT EXISTS "${SLANG_SOURCE_DIR}/include/slang/ast/Compilation.h")
            message(FATAL_ERROR "SLANG_SOURCE_DIR is not a SystemVerilog Slang checkout")
        endif()
        add_subdirectory("${SLANG_SOURCE_DIR}" slang EXCLUDE_FROM_ALL)
    else()
        include(FetchContent)
        FetchContent_Declare(slang
            GIT_REPOSITORY https://github.com/MikePopoloski/slang.git
            GIT_TAG ${SLANG_REVISION}
            PATCH_COMMAND ${CMAKE_COMMAND}
                -DSLANG_SOURCE_DIR=<SOURCE_DIR>
                -P "${CMAKE_CURRENT_SOURCE_DIR}/cmake/patchSlangGitProbe.cmake")
        FetchContent_MakeAvailable(slang)
    endif()
endif()

add_library(sn_slang_lib STATIC src/snSlang.cpp)
target_include_directories(sn_slang_lib PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/src" "${ABC_SOURCE_DIR}/src/base/sn" "${ABC_SOURCE_DIR}/src")
target_compile_features(sn_slang_lib PUBLIC cxx_std_20)
target_link_libraries(sn_slang_lib PRIVATE slang::slang)
add_executable(sn src/snMain.cpp)
target_link_libraries(sn PRIVATE sn_slang_lib)
install(TARGETS sn RUNTIME DESTINATION bin)
