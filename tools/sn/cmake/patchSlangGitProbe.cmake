set(path "${SLANG_SOURCE_DIR}/external/CMakeLists.txt")
file(READ "${path}" contents)

set(old [=[  OUTPUT_STRIP_TRAILING_WHITESPACE)
message(STATUS "Git remote URL: ${GITHUB_PREFIX}")]=])
set(new [=[  OUTPUT_STRIP_TRAILING_WHITESPACE
  ERROR_QUIET
  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}")
message(STATUS "Git remote URL: ${GITHUB_PREFIX}")]=])

string(FIND "${contents}" "${new}" patched)
if(patched EQUAL -1)
    string(FIND "${contents}" "${old}" found)
    if(found EQUAL -1)
        message(FATAL_ERROR "Cannot locate Slang's Git remote probe in ${path}")
    endif()
    string(REPLACE "${old}" "${new}" contents "${contents}")
    file(WRITE "${path}" "${contents}")
endif()
