all: DNFScheduling TreeGenerator MultiStreamDNFScheduling MultistreamTreeGenerator

BOOSTLOCATION = -I/opt/local/include/
CCFLAGS= -O3 -g -Wall

DNFScheduling.o: DNFScheduling.cpp DNFScheduling.hpp Makefile
	g++ $(CCFLAGS) $(BOOSTLOCATION) -c DNFScheduling.cpp

Optimal4SingleStream.o: Optimal4SingleStream.cpp DNFScheduling.hpp Makefile
	g++ $(CCFLAGS) $(BOOSTLOCATION) -c Optimal4SingleStream.cpp

DNFScheduling: Optimal4SingleStream.o DNFScheduling.o
	g++ $(CCFLAGS) $(BOOSTLOCATION) Optimal4SingleStream.o DNFScheduling.o -o $@

TreeGenerator: TreeGenerator.cpp
	g++ $(CCFLAGS) $(BOOSTLOCATION) $< -o $@

MultistreamTreeGenerator: MultistreamTreeGenerator.cpp
	g++ $(CCFLAGS) $< -o $@

MultiStreamDNFScheduling.o: MultiStreamDNFScheduling.cpp MultiStream.hpp Makefile
	g++ $(CCFLAGS) -c MultiStreamDNFScheduling.cpp

Optimal4MultiStream.o: Optimal4MultiStream.cpp MultiStream.hpp Makefile
	g++ $(CCFLAGS) -c Optimal4MultiStream.cpp

MultiStreamDNFScheduling: Optimal4MultiStream.o MultiStreamDNFScheduling.o
	g++ $(CCFLAGS) Optimal4MultiStream.o MultiStreamDNFScheduling.o -o $@

