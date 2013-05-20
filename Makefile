CC   := gcc
CXX  := g++
LD   := $(CXX)

$(info Using CC=$(CC))
$(info Using CXX=$(CXX))
$(info Using LD=$(LD))

PROG := abc

MODULES := \
	$(wildcard src/ext) src/misc/ext \
	src/base/abc src/base/abci src/base/cmd src/base/io \
	src/base/main src/base/ver src/base/test \
	src/bdd/cudd src/bdd/dsd src/bdd/epd src/bdd/mtr src/bdd/parse \
	src/bdd/reo src/bdd/cas \
	src/map/mapper src/map/mio src/map/super src/map/if \
	src/map/amap src/map/cov src/map/scl \
	src/misc/extra src/misc/mvc src/misc/st src/misc/util src/misc/nm \
	src/misc/vec src/misc/hash src/misc/tim src/misc/bzlib src/misc/zlib \
	src/misc/mem src/misc/bar src/misc/bbl \
	src/opt/cut src/opt/fxu src/opt/rwr src/opt/mfs src/opt/sim \
	src/opt/ret src/opt/res src/opt/lpk src/opt/nwk src/opt/rwt \
	src/opt/cgt src/opt/csw src/opt/dar src/opt/dau src/opt/sfm \
	src/sat/bsat src/sat/csat src/sat/msat src/sat/psat src/sat/cnf src/sat/bmc \
	src/bool/bdc src/bool/deco src/bool/dec src/bool/kit src/bool/lucky src/bool/rsb \
	src/proof/pdr src/proof/int src/proof/bbr src/proof/llb src/proof/live \
	src/proof/cec src/proof/dch src/proof/fraig src/proof/fra src/proof/ssw \
	src/proof/abs src/proof/ssc \
	src/aig/aig src/aig/saig src/aig/gia src/aig/ioa src/aig/ivy src/aig/hop \
	src/aig/miniaig \
	src/python 

all: $(PROG)
default: $(PROG)

arch_flags : arch_flags.c
	$(CC) arch_flags.c -o arch_flags

ARCHFLAGS := $(shell $(CC) arch_flags.c -o arch_flags && ./arch_flags)
OPTFLAGS  := -g -O #-DABC_NAMESPACE=xxx

CFLAGS   += -Wall -Wno-unused-function -Wno-write-strings -Wno-sign-compare $(OPTFLAGS) $(ARCHFLAGS) -I$(PWD)/src

# Set -Wno-unused-bug-set-variable for GCC 4.6.0 and greater only
ifneq ($(or $(findstring gcc,$(CC)),$(findstring g++,$(CC))),)
empty:=
space:=$(empty) $(empty)

GCC_VERSION=$(shell $(CC) -dumpversion)
GCC_MAJOR=$(word 1,$(subst .,$(space),$(GCC_VERSION)))
GCC_MINOR=$(word 2,$(subst .,$(space),$(GCC_VERSION)))

$(info Found GCC_VERSION $(GCC_VERSION))
ifeq ($(findstring $(GCC_MAJOR),0 1 2 3),)
$(info Found GCC_MAJOR>=4)
ifeq ($(findstring $(GCC_MINOR),0 1 2 3 4 5),)
$(info Found GCC_MINOR>=6)
CFLAGS += -Wno-unused-but-set-variable
endif
endif

endif

LIBS := -ldl

ifneq ($(READLINE),0)
CFLAGS += -DABC_USE_READLINE
LIBS += -lreadline
endif

ifneq ($(PTHREADS),0)
CFLAGS += -DABC_USE_PTHREADS
LIBS += -lpthread
endif

$(info Using CFLAGS=$(CFLAGS))
CXXFLAGS += $(CFLAGS) 

SRC  := 
GARBAGE := core core.* *.stackdump ./tags $(PROG) arch_flags

.PHONY: all default tags clean docs

include $(patsubst %, %/module.make, $(MODULES))

OBJ := \
	$(patsubst %.cc, %.o, $(filter %.cc, $(SRC))) \
	$(patsubst %.c, %.o,  $(filter %.c, $(SRC)))  \
	$(patsubst %.y, %.o,  $(filter %.y, $(SRC))) 

DEP := $(OBJ:.o=.d)

# implicit rules

%.o: %.c
	@echo "\`\` Compiling:" $(LOCAL_PATH)/$<
	@$(CC) -c $(CFLAGS) $< -o $@

%.o: %.cc
	@echo "\`\` Compiling:" $(LOCAL_PATH)/$<
	@$(CXX) -c $(CXXFLAGS) $< -o $@

%.d: %.c
	@echo "\`\` Dependency:" $(LOCAL_PATH)/$<
	@./depends.sh $(CC) `dirname $*.c` $(CFLAGS) $*.c > $@

%.d: %.cc
	@echo "\`\` Generating dependency:" $(LOCAL_PATH)/$<
	@./depends.sh $(CXX) `dirname $*.cc` $(CXXFLAGS) $*.cc > $@

-include $(DEP)

# Actual targets

depend: $(DEP)

clean: 
	@echo "\`\` Cleaning up..."
	@rm -rvf $(PROG) lib$(PROG).a $(OBJ) $(GARBAGE) $(OBJ:.o=.d) 

tags:
	etags `find . -type f -regex '.*\.\(c\|h\)'`

$(PROG): $(OBJ)
	@echo "\`\` Building binary:" $(notdir $@)
	@$(LD) -o $@ $^ $(LIBS)

lib$(PROG).a: $(OBJ)
	@echo "\`\` Linking:" $(notdir $@)
	@ar rv $@ $?
	@ranlib $@

docs:
	@echo "\`\` Building documentation." $(notdir $@)
	@doxygen doxygen.conf
