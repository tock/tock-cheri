/* The QEMU virt board
 */


MEMORY
{
  rom (rx)  : ORIGIN = 0x20000000, LENGTH = 0x400000
  prog (rx) : ORIGIN = 0x20400000, LENGTH = 0x4000000-0x400000
  ram (rwx) : ORIGIN = 0x80000000, LENGTH = 0x800000
}

MPU_MIN_ALIGN = 1;
WORD_SIZE = 16;

INCLUDE ../kernel_layout.ld
