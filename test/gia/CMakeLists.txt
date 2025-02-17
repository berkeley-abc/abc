add_executable(gia_test gia_test.cc)

target_link_libraries(gia_test PUBLIC
    gtest
    gtest_main
    libabc
    ${CMAKE_THREAD_LIBS_INIT}
)
target_compile_options(gia_test PUBLIC ${GTEST_CFLAGS})

gtest_discover_tests(gia_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)
