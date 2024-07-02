# Makefile for building qemu CHERI virt board

# If not provided, assume cheri sdk installed in default location
CHERI_SDK ?= $(abspath ${HOME}/cheri/output/sdk)

# Default 64-bit
BITS ?= 64

# Default cheri on (pure/hybrid controls only userspace)
CHERI ?= pure

# Other config
export NUM_PROCS ?= 4
export PLIC_BASE_ADDR ?= 0xc000000
export BAUD_RATE ?=115200
export N_REGIONS ?= 4
export STACK_SIZE ?= 0x2000
export UART0_BASE_ADDR ?= 0x10000000
export UART0_IRQ ?=10

TARGET=riscv${BITS}imac-unknown-none-cheri-hybrid-elf

# When using "no_std" (which Tock does), rust builds its own compiler_builtins.
# memcpy is broken using upstream rust based compiler builtins because it
# uses usize, not a pointer type (as well as going out of bounds)
# I have a rewritten version, but can't work out how to add that as
# dependency while not also building the upstream compiler builtins.
# In the mean time, I am linking in the cheribuild baremetal libc which
# will override the weak symbols provided by the rust compiler builtins

CHERI_LIBC ?= $(CHERI_SDK)/baremetal/baremetal-newlib-riscv$(BITS)-hybrid/riscv$(BITS)-unknown-elf

EXTRA_FLAGS = -lstatic=c -L$(CHERI_LIBC)/lib

PLATFORM=qemu_cheri_virt

RUSTC_FLAGS += \
  -C link-arg=-Tlayout.ld \
  -C linker=${CHERI_SDK}/bin/ld.lld \
  -C linker-flavor=ld.lld \
  -C relocation-model=static \
  -C link-arg=-nmagic \
  -C link-arg=-icf=all \
  $(EXTRA_FLAGS) \
  -Z macro-backtrace \

# We do have rustup, we just don't want the Makefile.common to try any of the
# toolchain commands with it because it is a custom one and that always causes
# an error.
NO_RUSTUP=1
TOOLCHAIN ?= ${CHERI_SDK}/bin/llvm

include ../Makefile.common

# Pad to flash size
$(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM)_pad.bin: $(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM).bin
	cp $^ $@
	dd if=/dev/null of=$@ bs=1 seek=33554431 count=1

$(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM)_app.bin : $(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM).bin $(APP_BIN)
	cp $< $@
	dd if=/dev/null of=$@ bs=1 seek=4194304 count=1
	cat $(APP_BIN) >> $@
	dd if=/dev/null of=$@ bs=1 seek=33554431 count=1


invoke_qemu = ${CHERI_SDK}/bin/qemu-system-riscv${BITS}cheri		\
	  -M virt 														\
	  -cpu any,Xcheri_v9=true 										\
	  -m 10M 														\
	  -bios none 													\
	  -drive if=pflash,file=$(1),format=raw,readonly=on -nographic	\
	  -D /tmp/qemu.log											    \
      -d instr,mmu

# Run just the kernel on QEMU
.PHONY: run
run: $(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM)_pad.bin
	$(call invoke_qemu,$^)

# Run the kernel with a bundled app on QEMU
.PHONY: run_app
run_app: $(TOCK_ROOT_DIRECTORY)target/$(TARGET)/release/$(PLATFORM)_app.bin
	$(call invoke_qemu,$^)