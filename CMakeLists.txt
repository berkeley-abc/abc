cmake_minimum_required(VERSION 3.1.0)

project(abc)

execute_process(
  COMMAND make ABC_MAKE_NO_DEPS=1 cmake_info
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

add_executable(abc ${ABC_SRC})

target_include_directories(abc PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src )
target_compile_options(abc PRIVATE ${ABC_CFLAGS} )
target_link_libraries(abc PRIVATE ${ABC_LIBS})
