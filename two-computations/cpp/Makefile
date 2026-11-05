# The mockup of the multiradial algorithm.  make; make check
CXX ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -pedantic
SRC = main.cpp multiradial.cpp iv.cpp oracle.cpp theater.cpp link.cpp
HDR = common.hpp decimal.hpp datum.hpp theater.hpp multiradial.hpp iv.hpp oracle.hpp link.hpp classical.hpp

mockup: $(SRC) $(HDR)
	$(CXX) $(CXXFLAGS) -o $@ $(SRC)

# The information flow: the implemented algorithm and the IV estimate must not see a theater, not even through
# another header. g++ -H lists every header a file pulls in.
check: mockup
	@for f in multiradial.cpp iv.cpp; do \
	   if $(CXX) $(CXXFLAGS) -H -fsyntax-only $$f 2>&1 | grep -q -e 'theater.hpp' -e 'oracle.hpp' -e 'link.hpp'; \
	   then echo "information flow: FAILED ($$f sees a theater)"; exit 1; fi; \
	   if grep -q 'HodgeTheater' $$f; then echo "information flow: FAILED ($$f names HodgeTheater)"; exit 1; fi; done
	@echo "information flow: multiradial.cpp and iv.cpp do not include theater.hpp, oracle.hpp or link.hpp, even indirectly"
	@for d in ../data/D*.txt; do ./mockup --selftest $$d | tail -1; done

clean:
	rm -f mockup
