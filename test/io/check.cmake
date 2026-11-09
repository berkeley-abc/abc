execute_process(
    COMMAND "${IO_PROGRAM}" "${IO_FIXTURE}" "${IO_CAPTURE}"
    RESULT_VARIABLE result OUTPUT_VARIABLE out ERROR_VARIABLE err
    TIMEOUT 90)
if(NOT "${result}" STREQUAL "0")
    message(FATAL_ERROR "Output-routing test failed (${result})\n${out}\n${err}")
endif()

# Windows console streams use CRLF; private logs are checked byte-for-byte.
if(WIN32)
    string(REPLACE "\r\n" "\n" out "${out}")
    string(REPLACE "\r\n" "\n" err "${err}")
endif()

# These are the only messages allowed to reach the host console. Private log
# contents are checked by the executable, including concurrent worker output.
set(expected_out "C:console\nC-WORKER:console\nCPP:console:002a\nCPP-WORKER:console\n")
set(expected_err "C-ERR:console\nC-WORKER-ERR:console\nCPP-ERR:console\n")
if(IO_CAPTURE)
    string(APPEND expected_out "HOST stdout\nPASS capture\n")
    string(APPEND expected_err "HOST stderr\n")
else()
    string(APPEND expected_out "PASS disabled\n")
endif()
if(NOT "${out}" STREQUAL "${expected_out}" OR NOT "${err}" STREQUAL "${expected_err}")
    message(FATAL_ERROR "Unexpected console output (possible capture leak)\nstdout:\n${out}\nstderr:\n${err}")
endif()
message(STATUS "Output routing: console and private logs passed (capture=${IO_CAPTURE})")
