add_subdirectory(gia)

if(UNIX)
    add_test(NAME acec_output_coverage
        COMMAND bash ${CMAKE_CURRENT_SOURCE_DIR}/acec_output_coverage.sh $<TARGET_FILE:abc>)
endif()
