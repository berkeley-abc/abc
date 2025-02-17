add_executable(gia_test gia_test.cc)

target_include_directories(gia_test PUBLIC ${GTEST_INCLUDE_DIRS})
target_compile_options(gia_test PUBLIC ${GTEST_CFLAGS})
target_link_libraries(gia_test PUBLIC
    libabc
    ${GTEST_LIBS}
)

gtest_discover_tests(gia_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
