add_subdirectory(gia)

find_program(ABC_BASH_EXECUTABLE bash)
if(ABC_BASH_EXECUTABLE)
    add_test(NAME sresub_drw_cleanup
        COMMAND ${CMAKE_COMMAND} -E env "ABC=$<TARGET_FILE:abc>"
            ${ABC_BASH_EXECUTABLE} "${CMAKE_CURRENT_SOURCE_DIR}/sresub_drw_cleanup.sh")
    set_tests_properties(sresub_drw_cleanup PROPERTIES
        SKIP_REGULAR_EXPRESSION "SKIP: python3 is needed")
endif()
