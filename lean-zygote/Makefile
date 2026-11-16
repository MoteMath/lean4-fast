LEAN_BUILD_DIR ?= /home/devin/build-lean4-s2
LEAN_BIN       := $(LEAN_BUILD_DIR)/bin/lean
LEAN_INC       := $(LEAN_BUILD_DIR)/include
LEAN_LIB_DIR   := $(LEAN_BUILD_DIR)/lib/lean
LEAN_TOP_LIB   := $(LEAN_BUILD_DIR)/lib
CXX            ?= g++
CC             ?= gcc

COMMA          := ,
LOCAL_DEPS_LIB ?= /home/devin/local-deps/usr/lib/x86_64-linux-gnu
EXTRA_LINK_FLAGS := $(if $(wildcard $(LOCAL_DEPS_LIB)),-L$(LOCAL_DEPS_LIB) -Wl$(COMMA)-rpath$(COMMA)$(LOCAL_DEPS_LIB),)

all: lean-zygote lean-zygote-client

LeanZygoteShim.c: LeanZygoteShim.lean $(LEAN_BIN)
	LEAN_PATH=$(LEAN_LIB_DIR) $(LEAN_BIN) --root=. -c $@ $<

LeanZygoteShim.o: LeanZygoteShim.c
	$(CC) -O3 -fPIC -std=c11 -I$(LEAN_INC) -c $< -o $@

lean-zygote: lean_zygote.cpp LeanZygoteShim.o
	$(CXX) -O3 -std=c++17 -pthread -Wall -Wextra -I$(LEAN_INC) $< LeanZygoteShim.o \
		-L$(LEAN_LIB_DIR) -L$(LEAN_TOP_LIB) $(EXTRA_LINK_FLAGS) \
		-Wl,-rpath,'$$ORIGIN/../lib' -Wl,-rpath,'$$ORIGIN/../lib/lean' \
		-Wl,-rpath,$(LEAN_LIB_DIR) -Wl,-rpath,$(LEAN_TOP_LIB) \
		-rdynamic -lInit_shared -lleanshared -lstdc++ -lm -ldl -o $@

lean-zygote-client: lean_zygote_client.cpp
	$(CXX) -O3 -std=c++17 $< -o $@

install: all
	cp -f lean-zygote $(LEAN_BUILD_DIR)/bin/lean-zygote
	cp -f lean-zygote-client $(LEAN_BUILD_DIR)/bin/lean-zygote-client

clean:
	rm -f LeanZygoteShim.c LeanZygoteShim.o lean-zygote lean-zygote-client

.PHONY: all install clean
