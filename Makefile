
CC   := gcc
CXX  := g++
LD   := g++
CP   := cp

PROG := abc

MODULES := \
        $(wildcard src/ext) src/misc/ext \
	src/base/abc src/base/abci src/base/cmd src/base/io \
	src/base/main src/base/ver src/base/test \
	src/bdd/cudd src/bdd/dsd src/bdd/epd src/bdd/mtr src/bdd/parse \
	src/bdd/reo src/bdd/cas \
	src/map/fpga src/map/mapper src/map/mio src/map/super src/map/if \
	src/map/amap src/map/cov \
	src/misc/extra src/misc/mvc src/misc/st src/misc/util src/misc/nm \
	src/misc/vec src/misc/hash src/misc/tim src/misc/bzlib src/misc/zlib \
	src/misc/mem src/misc/bar src/misc/bbl \
	src/opt/cut src/opt/fxu src/opt/rwr src/opt/mfs src/opt/sim \
	src/opt/ret src/opt/res src/opt/lpk src/opt/nwk src/opt/rwt \
	src/opt/cgt src/opt/csw src/opt/dar \
	src/sat/bsat src/sat/csat src/sat/msat src/sat/psat src/sat/cnf \
	src/bool/bdc src/bool/deco src/bool/dec src/bool/kit \
	src/proof/pdr src/proof/int src/proof/bbr src/proof/llb src/proof/live \
	src/proof/cec src/proof/dch src/proof/fraig src/proof/fra src/proof/ssw \
	src/aig/aig src/aig/saig src/aig/gia src/aig/ioa src/aig/ivy src/aig/hop \
	src/python 

all: $(PROG)
default: $(PROG)

arch_flags : arch_flags.c
	$(CC) arch_flags.c -o arch_flags

ARCHFLAGS := $(shell $(CC) arch_flags.c -o arch_flags && ./arch_flags)
OPTFLAGS  := -g -O #-DABC_NAMESPACE=xxx

CFLAGS   += -Wall -Wno-unused-function $(OPTFLAGS) $(ARCHFLAGS) -I$(PWD)
CXXFLAGS += $(CFLAGS) 

#LIBS := -m32 -ldl -rdynamic -lreadline -ltermcap
LIBS := -lreadline

SRC  := 
GARBAGE := core core.* *.stackdump ./tags $(PROG) arch_flags

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
	rm -rf $(PROG) lib$(PROG).a $(OBJ) $(GARBAGE) $(OBJ:.o=.d) 

tags:
	ctags -R .

$(PROG): $(OBJ)
	$(LD) -o $@ $^ $(LIBS)

lib$(PROG).a: $(OBJ)
	ar rv $@ $?
	ranlib $@

docs:
	doxygen doxygen.conf

