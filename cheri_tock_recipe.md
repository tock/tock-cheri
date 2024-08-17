# Get a toolchain

## Cheribuild

First, check out cheribuild:

```
mkdir ~/cheri && cd ~/cheri
git clone https://github.com/CTSRD-CHERI/cheribuild.git
```

Cheribuild will tell you, but probably need a few packages. If you system has
apt:
```
sudo apt install cmake ninja-build libpixman-1-dev libglib2.0-dev samba
```

It will help you build everything but rustc.

You will need (at minimum) a clang/llvm/libc/qemu

libc is needed even for tock because we need CHERI compatible compiler builtins.

To build these:

```
cd ~/cheri/cheribuild
./cheribuild.py llvm qemu compiler-rt-builtins-baremetal-riscv64-hybrid
CCC_OVERRIDE_OPTIONS=+-Wno-error=implicit-function-declaration ./cheribuild.py newlib-baremetal-riscv64-hybrid --reconfigure --clean
```

Note: other useful targets to build with cheribuild are the buuiltins/newlib with
riscv32 for 32bit, -purecap for purecap, or without -hybrid for non-CHERI.


LLVM, especially, will take a while. As it is progressing, start with getting a CHERI rustc.

## Rustc

Sadly, nobody has taught cheribuild this recipe yet. Check out:

```
cd ~
git clone -b cheri-hybrid-1.67.1+rv32 https://github.com/arichardson/rust.git
```

You will then need to add your own config.toml to inside the root of this project.
Here is mine (I presume you are also on an x86 host):

```

[target.x86_64-unknown-linux-gnu]
llvm-config = "[HOME]/cheri/output/sdk/bin/llvm-config"
# crt-static = true

[build]
extended = true
docs = false
tools = [
    "cargo",
    "clippy",
    "rustdoc",
    "rustfmt",
    "rust-analyzer",
    "rust-analyzer-proc-macro-srv",
    "analysis",
]i
sanitizers = true
profiler = true

[install]
prefix= "[HOME]/cheri/output/sdk/rust-sdk"
sysconfdir= "etc"

[rust]
codegen-tests = false
channel = "nightly"
llvm-tools = true
```

You might not care to build all the tools / sanitizers / profiler.
Obviously, replace [MY_HOME] with something appropriate. I think this file does
NOT expand environment variables.

Note that building this requires llvm to have already built, so wait for that.

For some reason rustc expects this directory to exist even though we are not
using the llvm-project from rustc (because we use the CHERI one), so:

```
mkdir ~/rust/src/llvm-project/libunwind
```

Then, build and install.

```
./x.py build
./x.py install
```

Finally, make a custom rustup toolchain. If you don't actually have rustup:

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

To make a toolchain called cheri (this matches the name in the toolchain file in tock)
linked to where rustc is installed:

```
rustup toolchain link cheri ${HOME}/cheri/output/sdk/rust-sdk
```

# Build and run CHERI tock

You can check out the CHERI tock here:

```
cd ~
git clone -b all_squashed https://github.com/tock/tock-cheri.git
```

And, finally, build/run the QEMU CHERI virt board:

```
make -C ~/tock/boards/qemu_cheri_virt run
```

If you used the paths in this file then this should just work, although running
it will be completely un-interesting without any processes.

# Build and run CHERI C applications

Now is a good time to also build a purecap libc:

```
cd ~/cheri/cheribuild
./cheribuild.py compiler-rt-builtins-baremetal-riscv64-purecap
CCC_OVERRIDE_OPTIONS=+-Wno-error=implicit-function-declaration ./cheribuild.py newlib-baremetal-riscv64-purecap
```

And for whatever reason builtins and libc end up not being in the same directory,
so copy over all the libraries from the builtins into the respective libc

```
cp ~/cheri/output/sdk/baremetal/baremetal-riscv64-purecap/lib/* ~/cheri/output/sdk/baremetal/baremetal-newlib-riscv64-purecap/riscv64-unknown-elf/lib/
cp ~/cheri/output/sdk/baremetal/baremetal-riscv64-hybrid/lib/* ~/cheri/output/sdk/baremetal/baremetal-newlib-riscv64-hybrid/riscv64-unknown-elf/lib/
```


Check out libtock-c:

```
cd ~
git clone -b all_squashed https://github.com/tock/libtock-c-cheri.git
```

Note: The makefile rules in the libtock-c expect both the cheri sdk and tock to
be in the same directory as libtock-c. If they are not, you will likely have
to invoke make with CHERI_SDK and TOCK_DIR set to something sensible.

You can now run some examples

```
cd ~/libtock-c/examples/c_hello
make CLANG=1 RISCV=1 CHERI=1 run_pure
```

Each target will be built, but `run_pure` runs the purecap binary and `run_hybrid`
runs the hybrid binary.

You might also try running the revocation test which interracts more heavily
with CHERI features in the kernel:

```
cd ~/libtock-c/examples/revoke_test
make CLANG=1 RISCV=1 CHERI=1 run_pure
```

There is also `examples/vun` with the simple buffer overflow example presented
in the tockworld7 cheri talk.

# Build and run CHERI Rust applications

check out libtock-rs:

```
cd ~
git clone -b all_squashed https://github.com/tock/libtock-rs-cheri.git
```

Note: this branch expects to have tock rooted under it, so
will either have to fiddle with git submodules or just remove
the submodule and symlink tock

Now you can run an example:

```
EXAMPLE=consle make -C ~/libtock-rs run_qemu_rv64xcheri 
```
