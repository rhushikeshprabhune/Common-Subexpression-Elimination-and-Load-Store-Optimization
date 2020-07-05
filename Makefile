.SUFFIXES: %.c %.cpp

OBJS =  main.o \
	dominance.o \
	worklist.o \
	valmap.o \
	transform.o \
	cfg.o \
	loop.o 

OBJS += CSE.o summary.o

# Comment out next line for C++

.PHONY: all

all: p3

p3: $(OBJS)
	clang++ -g -Wno-implicit-function-declaration -o $@ $(OBJS) `llvm-config --cxxflags --ldflags --libs --system-libs`

clean:
	rm -Rf p3 $(OBJS)

%.o:%.c
	clang -g -c -o $@ $^ `llvm-config --cflags` 

%.o:%.cpp
	clang++ -g -c -o $@ $^ `llvm-config --cxxflags` 


