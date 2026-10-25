CXX ?= c++
CXXFLAGS ?= -g -Wall -ansi --pedantic -O3
CPPFLAGS ?=
LDFLAGS ?=
LDLIBS ?=

ifeq ($(REJECT_MODE),yes)
CPPFLAGS += -DREJECTFLAG
endif
ifeq ($(VERBOSE_MODE),yes)
CPPFLAGS += -DVERBOSE_MODE
endif

SOURCES = include/CatalanSuit.cpp include/CompletionSuit.cpp src/MainExhaustivDFA.cpp
OBJECTS = $(SOURCES:.cpp=.o)
DEPFILES = $(OBJECTS:.o=.d)

.PHONY: all test clean
all: dfa

dfa: $(OBJECTS)
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJECTS) $(LDLIBS)

# Also bootstrap dependency files when upgrading from an older build.
$(OBJECTS): Makefile

%.o: %.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -c $< -o $@

-include $(DEPFILES)

test: dfa
	python3 tests/check_enumeration.py

clean:
	rm -f $(OBJECTS) $(DEPFILES) dfa dfa.dot dfa.eps
