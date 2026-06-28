add_executable(gia_test gia_test.cc)

target_link_libraries(gia_test
    gtest_main
    libabc
)

gtest_discover_tests(gia_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

add_executable(origins_test origins_test.cc)

target_link_libraries(origins_test
    gtest_main
    libabc
)

gtest_discover_tests(origins_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)