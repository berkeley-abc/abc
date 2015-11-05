cmake_minimum_required(VERSION 3.3.0)

include(CMakeParseArguments)
include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

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

project(abc)

# run make to extract compiler options, linker options and list of source files
execute_process(
  COMMAND make ABC_MAKE_NO_DEPS=1 CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} LD=${CMAKE_CXX_COMPILER} cmake_info
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  OUTPUT_VARIABLE MAKE_OUTPUT
)

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


add_executable(abc ${ABC_SRC})

target_include_directories(abc PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src )
target_compile_options_filtered(abc PRIVATE ${ABC_CFLAGS} -Wno-unused-but-set-variable )
target_link_libraries(abc PRIVATE ${ABC_LIBS})
