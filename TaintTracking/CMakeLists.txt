add_library(LLVMPassTaintTracking MODULE TaintTracking.cpp)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
target_compile_features(LLVMPassTaintTracking PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that.
set_target_properties(LLVMPassTaintTracking PROPERTIES
        COMPILE_FLAGS "-D__GLIBCXX_USE_CXX11_ABI=0 -fno-rtti"
        )

# Get proper shared-library behavior (where symbols are not necessarily
# resolved when the shared library is linked) on OS X.
if(APPLE)
    set_target_properties(LLVMPassTaintTracking PROPERTIES
            LINK_FLAGS "-undefined dynamic_lookup"
            )
endif(APPLE)

#cmake_minimum_required(VERSION 3.12)
#project(TaintTracking)
#
#add_executable(main temp.cpp)
#
#find_library(TOOL NAMES tool HINTS ${CMAKE_SOURCE_DIR}/tool/target/debug)
#target_link_libraries(main ${TOOL})

