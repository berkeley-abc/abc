
CC   := gcc
CXX  := g++ 
LD   := g++
CP   := cp

PROG := abc

MODULES := src/base/abc src/base/cmd src/base/io src/base/main \
           src/bdd/cudd src/bdd/epd src/bdd/mtr src/bdd/parse \
           src/map/fpga src/map/mapper src/map/mio src/map/super \
           src/misc/extra src/misc/st src/misc/util src/misc/vec \
           src/sat/asat src/sat/fraig src/sat/msat \
           src/seq \
           src/sop/ft src/sop/mvc

default: $(PROG)

CFLAGS   += -Wall -Wno-unused-function -g -O $(patsubst %, -I%, $(MODULES)) 
CXXFLAGS += $(CFLAGS) 

LIBS := 
SRC  := 
GARBAGE := core core.* *.stackdump ./tags $(PROG)

.PHONY: tags clean docs

include $(patsubst %, %/module.make, $(MODULES))

OBJ := \
	$(patsubst %.cc, %.o, $(filter %.cc, $(SRC))) \
	$(patsubst %.c, %.o,  $(filter %.c, $(SRC)))  \
	$(patsubst %.y, %.o,  $(filter %.y, $(SRC))) 

DEP := $(OBJ:.o=.d)

# implicit rules

%.d: %.c
	./depends.sh $(CC) `dirname $*.c` $(CFLAGS) $*.c > $@

%.d: %.cc
	./depends.sh $(CXX) `dirname $*.cc` $(CXXFLAGS) $(CFLAGS) $*.cc > $@

-include $(DEP)

# Actual targets

depend: $(DEP)

clean: 
	rm -rf $(PROG) $(OBJ) $(GARBAGE) $(OBJ:.o=.d) 

tags:
	ctags -R .

$(PROG): $(OBJ)
	$(LD) -o $@ $^ $(LIBS)

docs:
	doxygen doxygen.conf

