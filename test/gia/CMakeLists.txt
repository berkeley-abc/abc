if(ABC_USE_NAMESPACE)
    set_source_files_properties(gia_test.cc PROPERTIES LANGUAGE CXX)
endif()

add_executable(gia_test gia_test.cc)

target_compile_options(gia_test PUBLIC ${GTEST_CFLAGS})
target_link_libraries(gia_test PUBLIC
    libabc
    ${GTEST_LINK_LIBRARIES}
)

gtest_discover_tests(gia_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)
