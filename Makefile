# define some Makefile variables for the compiler and compiler flags
# to use Makefile variables later in the Makefile: $()
#
#  -g    adds debugging information to the executable file
#  -Wall turns on most, but not all, compiler warnings
#
# for C++ define  CC = g++
CXX = g++
CXXFLAGS  = -O3 -std=c++11 -march=native -flto -g -pthread 

# typing 'make' will invoke the first target entry in the file 
# (in this case the default target entry)	
# you can name this target entry anything, but "default" or "all"
# are the most commonly used names by convention
#
TESTS = cuckoo_commits2 cuckoo_commits
# variable assignement only goes into affect if variable does not already exist. Could, for example, do make TESTS=test to only make test

default: $(TESTS)
.PHONY: default clean
# phony because default and clean are not files

%: %.cpp
	$(CXX) $(CXXFLAGS) -o $@ $^

# To start over from scratch, type 'make clean'.  This
# removes the executable file, as well as old .o object
# files and *~ backup files:
#
clean: 
	$(RM) $(TESTS) *.o *~

# want g++ -O2 -std=c++11  test.cpp  fastavoidance.cpp hashdb.cpp -g -o test
