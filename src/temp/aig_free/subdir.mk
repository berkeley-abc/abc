################################################################################
# Automatically-generated file. Do not edit!
################################################################################

INCPATHS = -I$(ROOT)/aig-alan

# Add inputs and outputs from these tool invocations to the build variables 
PURE_C_SRCS += \
${addprefix $(ROOT)/aig-alan/, \
aigBalance.c \
aigCheck.c \
aigDfs.c \
aigMan.c \
aigMem.c \
aigObj.c \
aigOper.c \
aigTable.c \
aigUtil.c \
cudd2.c \
st.c \
}

C_SRCS += $(PURE_C_SRCS)


PURE_C_OBJS += \
${addprefix $(ROOT)/obj/aig-alan/, \
aigBalance.o \
aigCheck.o \
aigDfs.o \
aigMan.o \
aigMem.o \
aigObj.o \
aigOper.o \
aigTable.o \
aigUtil.o \
cudd2.o \
st.o \
}

OBJS += $(PURE_C_OBJS) 

PURE_C_DEPS += \
${addprefix $(ROOT)/obj/aig-alan, \
aigBalance.d \
aigCheck.d \
aigDfs.d \
aigMan.d \
aigMem.d \
aigObj.d \
aigOper.d \
aigTable.d \
aigUtil.d \
cudd2.d \
st.d \
}

DEPS += $(PURE_C_DEPS)


OCAML_OBJS += 


DEPEND_SRCS += 

# Each subdirectory must supply rules for building sources it contributes
$(ROOT)/obj/aig-alan/%.o: $(ROOT)/aig-alan/%.c
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C Compiler: $(CC)'
	@echo $(CC) $(GPCC_OPTS) $(INCPATHS)  -O3 -g3 -Wall -c -fmessage-length=0 -o$@ $<
	@$(CC)  $(GPCC_OPTS)  $(INCPATHS) -O3 -g3 -Wall -c -fmessage-length=0 -o$@ $< && \
	echo -n $(@:%.o=%.d) $(dir $@) > $(@:%.o=%.d) && \
	$(CC) -MM -MG -P -w  $(GPCC_OPTS) $(INCPATHS) -O3 -g3 -Wall -c -fmessage-length=0  $< >> $(@:%.o=%.d)
	@echo 'Finished building: $<'
	@echo ' '

$(ROOT)/obj/aig-alan/%.o: $(ROOT)/aig-alan/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: G++ C Compiler: $(GPCC)'
	@echo $(GPPCC) $(GPCC_OPTS) $(INCPATHS)  -O3 -g3 -Wall -c -fmessage-length=0 -o$@ $<
	@$(GPPCC)  $(GPCC_OPTS)  $(INCPATHS) -O3 -g3 -Wall -c -fmessage-length=0 -o$@ $< && \
	echo -n $(@:%.o=%.d) $(dir $@) > $(@:%.o=%.d) && \
	$(GPPCC) -MM -MG -P -w  $(GPCC_OPTS) $(INCPATHS) -O3 -g3 -Wall -c -fmessage-length=0  $< >> $(@:%.o=%.d)
	@echo 'Finished building: $<'
	@echo ' '


