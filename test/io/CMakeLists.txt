get_filename_component(ABC_IO_ROOT "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)

# Native Windows CI links the same tests against its MSBuild-produced library.
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    cmake_minimum_required(VERSION 3.10)
    project(abc_io_tests LANGUAGES C CXX)
    if(NOT MSVC)
        message(FATAL_ERROR "Standalone configuration expects an MSVC-built ABC library")
    endif()
    set(ABC_IO_LIBRARY "" CACHE FILEPATH "ABC static library built with matching capture settings")
    if(NOT EXISTS "${ABC_IO_LIBRARY}")
        message(FATAL_ERROR "Set ABC_IO_LIBRARY to the existing ABC static library")
    endif()
    option(ABC_USE_STDIO_REDIRECT "Test an ABC library built with output capture" OFF)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
    add_library(libabc STATIC IMPORTED)
    set_target_properties(libabc PROPERTIES
        IMPORTED_LOCATION "${ABC_IO_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${ABC_IO_ROOT}/src"
        INTERFACE_COMPILE_DEFINITIONS "WIN32;ABC_DLL=;ABC_USE_PTHREADS;ABC_USE_CUDD;HAVE_STRUCT_TIMESPEC;_WINSOCKAPI_;_CRT_SECURE_NO_DEPRECATE;_CRT_NONSTDC_NO_WARNINGS")
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        set_property(TARGET libabc APPEND PROPERTY INTERFACE_COMPILE_DEFINITIONS NT64)
    endif()
    set(ABC_CFLAGS -DABC_USE_PTHREADS)
    enable_testing()
endif()
if(NOT "-DABC_USE_PTHREADS" IN_LIST ABC_CFLAGS)
    message(STATUS "Skipping output-routing tests: ABC_USE_PTHREADS is required")
    return()
endif()

# Compile emitters like ABC, and the driver like an external library consumer.
add_library(abc_io_test_emit STATIC io_emit.c io_emit.cpp)
target_link_libraries(abc_io_test_emit PRIVATE libabc)
if(ABC_USE_STDIO_REDIRECT)
    if(MSVC)
        target_compile_options(abc_io_test_emit PRIVATE "/FI${ABC_IO_ROOT}/src/misc/util/abc_stdio.h")
    else()
        target_compile_options(abc_io_test_emit PRIVATE -include ${ABC_IO_ROOT}/src/misc/util/abc_stdio.h)
    endif()
endif()
if(ABC_USE_NAMESPACE)
    set_source_files_properties(io_emit.c PROPERTIES LANGUAGE CXX)
endif()
add_executable(abc_io_test io_test.cpp)
target_link_libraries(abc_io_test PRIVATE abc_io_test_emit libabc)
if(MSVC)
    set(io_arch x86)
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        set(io_arch x64)
    endif()
    target_link_libraries(abc_io_test PRIVATE "${ABC_IO_ROOT}/lib/${io_arch}/pthreadVC2.lib")
    add_custom_command(TARGET abc_io_test POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
            "${ABC_IO_ROOT}/lib/${io_arch}/pthreadVC2.dll" "$<TARGET_FILE_DIR:abc_io_test>")
endif()

set(io_capture OFF)
if(ABC_USE_STDIO_REDIRECT AND NOT ABC_USE_NO_THREAD_LOCAL)
    set(io_capture ON)
endif()
add_test(NAME io_routing
    COMMAND ${CMAKE_COMMAND}
        "-DIO_PROGRAM=$<TARGET_FILE:abc_io_test>"
        "-DIO_FIXTURE=${CMAKE_CURRENT_SOURCE_DIR}/mixed.blif"
        "-DIO_CAPTURE=${io_capture}"
        -P "${CMAKE_CURRENT_SOURCE_DIR}/check.cmake")
set_tests_properties(io_routing PROPERTIES TIMEOUT 120)
