#enable_testing()

add_test(NAME aligntest
    COMMAND ./aligntest.sh
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
