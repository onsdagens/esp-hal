//! Minimal startup / runtime for RISC-V CPUs from Espressif
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.60 and up. It *might*
//! compile with older versions but that may change in any new patch release.
//!
//! # Features
//!
//! This crate provides:
//!
//! - Before main initialization of the `.bss` and `.data` sections controlled
//!   by features
//! - `#[entry]` to declare the entry point of the program

// NOTE: Adapted from riscv-rt/src/lib.rs
#![no_std]
#![feature(abi_riscv_interrupt)]

use core::arch::global_asm;
use rtt_target::rprintln;

pub use riscv;
use riscv::register::{
    mcause,
    mtvec::{self, TrapMode}, mepc,
};
pub use riscv_rt_macros::{entry, pre_init};

pub use self::Interrupt as interrupt;

#[export_name = "error: esp-riscv-rt appears more than once in the dependency graph"]
#[doc(hidden)]
pub static __ONCE__: () = ();

extern "C" {
    // Boundaries of the .bss section
    static mut _bss_end: u32;
    static mut _bss_start: u32;

    // Boundaries of the .data section
    static mut _data_end: u32;
    static mut _data_start: u32;

    // Initial values of the .data section (stored in Flash)
    static _sidata: u32;
}

/// Rust entry point (_start_rust)
///
/// Zeros bss section, initializes data section and calls main. This function
/// never returns.
#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
pub unsafe extern "C" fn start_rust(a0: usize, a1: usize, a2: usize) -> ! {
    extern "Rust" {
        // This symbol will be provided by the user via `#[entry]`
        fn main(a0: usize, a1: usize, a2: usize) -> !;

        fn __post_init();

        fn _setup_interrupts();

    }

    __post_init();

    _setup_interrupts();

    main(a0, a1, a2);
}

/// Registers saved in trap handler
#[allow(missing_docs)]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
pub struct TrapFrame {
    pub ra: usize,
    pub t0: usize,
    pub t1: usize,
    pub t2: usize,
    pub t3: usize,
    pub t4: usize,
    pub t5: usize,
    pub t6: usize,
    pub a0: usize,
    pub a1: usize,
    pub a2: usize,
    pub a3: usize,
    pub a4: usize,
    pub a5: usize,
    pub a6: usize,
    pub a7: usize,
    pub s0: usize,
    pub s1: usize,
    pub s2: usize,
    pub s3: usize,
    pub s4: usize,
    pub s5: usize,
    pub s6: usize,
    pub s7: usize,
    pub s8: usize,
    pub s9: usize,
    pub s10: usize,
    pub s11: usize,
    pub gp: usize,
    pub tp: usize,
    pub sp: usize,
    pub pc: usize,
    pub mstatus: usize,
    pub mcause: usize,
    pub mtval: usize,
}

/// Trap entry point rust (_start_trap_rust)
///
/// `scause`/`mcause` is read to determine the cause of the trap. XLEN-1 bit
/// indicates if it's an interrupt or an exception. The result is examined and
/// ExceptionHandler or one of the core interrupt handlers is called.
#[link_section = ".trap.rust"]
#[export_name = "_start_trap_rust"]
pub unsafe extern "C" fn start_trap_rust(trap_frame: *const TrapFrame) {
    extern "C" {
        fn ExceptionHandler(trap_frame: &TrapFrame);
        fn DefaultHandler();
    }

    unsafe {
        let cause = mcause::read();

        if cause.is_exception() {
            ExceptionHandler(&*trap_frame)
        } else if cause.code() < __INTERRUPTS.len() {
            let h = &__INTERRUPTS[cause.code()];
            if h.reserved == 0 {
                DefaultHandler();
            } else {
                (h.handler)();
            }
        } else {
            DefaultHandler();
        }
    }
}

#[doc(hidden)]
#[no_mangle]
#[allow(unused_variables, non_snake_case)]
pub fn DefaultExceptionHandler(trap_frame: &TrapFrame) -> ! {
    use rtt_target::rprintln;
    let mcause: u32 = mcause::read().bits().try_into().unwrap();
    rprintln!("mcause:{:032b}", mcause);
    let mepc: u32 = mepc::read() as u32;
    rprintln!("mepc:{:08x}", mepc);
    loop {
        // Prevent this from turning into a UDF instruction
        // see rust-lang/rust#28728 for details
        continue;
    }
}

#[doc(hidden)]
#[no_mangle]
#[allow(unused_variables, non_snake_case)]
pub fn DefaultInterruptHandler() {
    loop {
        // Prevent this from turning into a UDF instruction
        // see rust-lang/rust#28728 for details
        continue;
    }
}

// Interrupts
#[doc(hidden)]
pub enum Interrupt {
    UserSoft,
    SupervisorSoft,
    MachineSoft,
    UserTimer,
    SupervisorTimer,
    MachineTimer,
    UserExternal,
    SupervisorExternal,
    MachineExternal,
}

extern "C" {
    fn UserSoft();
    fn SupervisorSoft();
    fn MachineSoft();
    fn UserTimer();
    fn SupervisorTimer();
    fn MachineTimer();
    fn UserExternal();
    fn SupervisorExternal();
    fn MachineExternal();
}

#[doc(hidden)]
pub union Vector {
    pub handler: unsafe extern "C" fn(),
    pub reserved: usize,
}

#[doc(hidden)]
#[no_mangle]
pub static __INTERRUPTS: [Vector; 12] = [
    Vector { handler: UserSoft },
    Vector {
        handler: SupervisorSoft,
    },
    Vector { reserved: 0 },
    Vector {
        handler: MachineSoft,
    },
    Vector { handler: UserTimer },
    Vector {
        handler: SupervisorTimer,
    },
    Vector { reserved: 0 },
    Vector {
        handler: MachineTimer,
    },
    Vector {
        handler: UserExternal,
    },
    Vector {
        handler: SupervisorExternal,
    },
    Vector { reserved: 0 },
    Vector {
        handler: MachineExternal,
    },
];

#[doc(hidden)]
#[no_mangle]
#[rustfmt::skip]
pub unsafe extern "Rust" fn default_post_init() {}

/// Default implementation of `_setup_interrupts` that sets `mtvec`/`stvec` to a
/// trap handler address.
#[doc(hidden)]
#[no_mangle]
#[rustfmt::skip]
pub unsafe extern "Rust" fn default_setup_interrupts() {
    extern "C" {
        fn _vector_table();
    }

    mtvec::write(_vector_table as usize, TrapMode::Direct);
}

/// Parse cfg attributes inside a global_asm call.
macro_rules! cfg_global_asm {
    {@inner, [$($x:tt)*], } => {
        global_asm!{$($x)*}
    };
    (@inner, [$($x:tt)*], #[cfg($meta:meta)] $asm:literal, $($rest:tt)*) => {
        #[cfg($meta)]
        cfg_global_asm!{@inner, [$($x)* $asm,], $($rest)*}
        #[cfg(not($meta))]
        cfg_global_asm!{@inner, [$($x)*], $($rest)*}
    };
    {@inner, [$($x:tt)*], $asm:literal, $($rest:tt)*} => {
        cfg_global_asm!{@inner, [$($x)* $asm,], $($rest)*}
    };
    {$($asms:tt)*} => {
        cfg_global_asm!{@inner, [], $($asms)*}
    };
}

cfg_global_asm! {
    r#"
/*
    Entry point of all programs (_start).

    It initializes DWARF call frame information, the stack pointer, the
    frame pointer (needed for closures to work in start_rust) and the global
    pointer. Then it calls _start_rust.
*/

.section .init, "ax"
.global _start

_start:
    /* Jump to the absolute address defined by the linker script. */
    lui ra, %hi(_abs_start)
    jr %lo(_abs_start)(ra)

_abs_start:
    .option norelax
    .cfi_startproc
    .cfi_undefined ra
"#,
#[cfg(feature = "has-mie-mip")]
    r#"
    csrw mie, 0
    csrw mip, 0
"#,
#[cfg(feature = "zero-bss")]
    r#"
    la a0, _bss_start
    la a1, _bss_end
    mv a3, x0
    1:
    sw a3, 0(a0)
    addi a0, a0, 4
    blt a0, a1, 1b
"#,
#[cfg(feature = "zero-rtc-fast-bss")]
    r#"
    la a0, _rtc_fast_bss_start
    la a1, _rtc_fast_bss_end
    mv a3, x0
    1:
    sw a3, 0(a0)
    addi a0, a0, 4
    blt a0, a1, 1b
"#,
#[cfg(feature = "init-data")]
    r#"
    la a0, _data_start
    la a1, _data_end
    la a2, _sidata
    1:
    lw a3, 0(a2)
    sw a3, 0(a0)
    addi a0, a0, 4
    addi a2, a2, 4
    blt a0, a1, 1b
"#,
#[cfg(feature = "init-rw-text")]
    r#"
    la a0, _srwtext
    la a1, _erwtext
    la a2, _irwtext
    1:
    lw a3, 0(a2)
    sw a3, 0(a0)
    addi a0, a0, 4
    addi a2, a2, 4
    blt a0, a1, 1b
"#,
#[cfg(feature = "init-rtc-fast-data")]
    r#"
    la a0, _rtc_fast_data_start
    la a1, _rtc_fast_data_end
    la a2, _irtc_fast_data
    1:
    lw a3, 0(a2)
    sw a3, 0(a0)
    addi a0, a0, 4
    addi a2, a2, 4
    blt a0, a1, 1b
"#,
#[cfg(feature = "init-rtc-fast-text")]
    r#"
    la a0, _srtc_fast_text
    la a1, _ertc_fast_text
    la a2, _irtc_fast_text
    1:
    lw a3, 0(a2)
    sw a3, 0(a0)
    addi a0, a0, 4
    addi a2, a2, 4
    blt a0, a1, 1b
"#,
    r#"
    li  x1, 0
    li  x2, 0
    li  x3, 0
    li  x4, 0
    li  x5, 0
    li  x6, 0
    li  x7, 0
    li  x8, 0
    li  x9, 0
    li  x10,0
    li  x11,0
    li  x12,0
    li  x13,0
    li  x14,0
    li  x15,0
    li  x16,0
    li  x17,0
    li  x18,0
    li  x19,0
    li  x20,0
    li  x21,0
    li  x22,0
    li  x23,0
    li  x24,0
    li  x25,0
    li  x26,0
    li  x27,0
    li  x28,0
    li  x29,0
    li  x30,0
    li  x31,0

    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    // Check hart ID
    csrr t2, mhartid
    lui t0, %hi(_max_hart_id)
    add t0, t0, %lo(_max_hart_id)
    bgtu t2, t0, abort

    // Allocate stack
    la sp, _stack_start
    lui t0, 16
    sub sp, sp, t0

    // Set frame pointer
    add s0, sp, zero

    jal zero, _start_rust

    .cfi_endproc

/*
    Trap entry points (_start_trap, _start_trapN for N in 1..=31)

    The default implementation saves all registers to the stack and calls
    _start_trap_rust, then restores all saved registers before `mret`
*/
.section .trap, "ax"

_start_trap:
    la t0, abort
    jr t0

/* Make sure there is an abort when linking */
.section .text.abort
.globl abort
abort:
    j abort

/*
    Interrupt vector table (_vector_table)
*/

.section .trap, "ax"
.weak _vector_table
.type _vector_table, @function

.option push
.balign 0x100
.option norelax
.option norvc

_vector_table:
    j _start_trap_rust
    j _start_trap1
    j _start_trap2
    j cpu_int_3_handler
    j cpu_int_4_handler
    j cpu_int_5_handler
    j cpu_int_6_handler
    j cpu_int_7_handler
    j cpu_int_8_handler
    j cpu_int_9_handler
    j cpu_int_10_handler
    j cpu_int_11_handler
    j cpu_int_12_handler
    j cpu_int_13_handler
    j cpu_int_14_handler
    j cpu_int_15_handler
    j cpu_int_16_handler
    j cpu_int_17_handler
    j cpu_int_18_handler
    j cpu_int_19_handler
    j cpu_int_20_handler
    j cpu_int_21_handler
    j cpu_int_22_handler
    j cpu_int_23_handler
    j cpu_int_24_handler
    j cpu_int_25_handler
    j cpu_int_26_handler
    j cpu_int_27_handler
    j cpu_int_28_handler
    j cpu_int_29_handler
    j cpu_int_30_handler
    j cpu_int_31_handler

.option pop
"#,
#[cfg(feature="weak-handlers")]
r#"
#this is required for the linking step, these symbols for in-use interrupts should always be overwritten by the user.
.section .trap, "ax"
.weak cpu_int_1_handler
.weak cpu_int_2_handler
.weak cpu_int_3_handler
.weak cpu_int_4_handler
.weak cpu_int_5_handler
.weak cpu_int_6_handler
.weak cpu_int_7_handler
.weak cpu_int_8_handler
.weak cpu_int_9_handler
.weak cpu_int_10_handler
.weak cpu_int_11_handler
.weak cpu_int_12_handler
.weak cpu_int_13_handler
.weak cpu_int_14_handler
.weak cpu_int_15_handler
.weak cpu_int_16_handler
.weak cpu_int_17_handler
.weak cpu_int_18_handler
.weak cpu_int_19_handler
.weak cpu_int_20_handler
.weak cpu_int_21_handler
.weak cpu_int_22_handler
.weak cpu_int_23_handler
.weak cpu_int_24_handler
.weak cpu_int_25_handler
.weak cpu_int_26_handler
.weak cpu_int_27_handler
.weak cpu_int_28_handler
.weak cpu_int_29_handler
.weak cpu_int_30_handler
.weak cpu_int_31_handler
_start_trap1:
    addi sp, sp, -24
    sw a0, 0(sp)    #stack a0
    sw a1, 4(sp)
    sw ra, 8(sp)   #stack return address
    csrrs a0, mstatus, x0
    sw a0, 12(sp)    #stack mstatus
    csrrs a0, mepc, x0
    sw a0, 16(sp)    #stack mepc
    #_STORE_PRIO SUBROUTINE
        lui a1, 0x600C2     #intr base upper bytes we need a separate register for this
        lw a0, 0x194(a1)    #load current threshold
        sw a0, 20(sp)       #stack current threshold
        csrrs a0, mcause, x0
        andi a0, a0, 31     #mcause & 0b11111 gives interrupt id
        slli a0, a0, 2      #interrupt id * 4 gives byte offset from base
        add a0, a0, a1      #intr base + offset
        lw a0, 0x114(a0)    #load current interrupt prio
        addi a0, a0, 1      #threshold must be 1 higher
        sw a0, 0x194(a1)    #set threshold
    #END
    csrrsi x0, mstatus, 8 #enable global interrupts
    jal ra, cpu_int_1_handler
    lw a0, 20(sp)  #load old prio
    #RETURN PRIO SUBROUTINE
    lui a1, 0x600C2 #intr base
    sw a0, 0x194(a1) #restore threshold
    #END
    lw a0, 12(sp) #load mstatus
    csrrw x0, mstatus, a0
    lw a0, 16(sp) #load mepc
    csrrw x0, mepc, a0
    lw a0, 0(sp)
    lw a1, 4(sp)
    lw ra, 8(sp)
    addi sp, sp, 24 #pop
    mret
_start_trap2:
    addi sp, sp, -24
    sw a0, 0(sp)    #stack a0
    sw a1, 4(sp)
    sw ra, 8(sp)   #stack return address
    csrrs a0, mstatus, x0
    sw a0, 12(sp)    #stack mstatus
    csrrs a0, mepc, x0
    sw a0, 16(sp)    #stack mepc
    #_STORE_PRIO SUBROUTINE
        lui a1, 0x600C2     #intr base upper bytes we need a separate register for this
        lw a0, 0x194(a1)    #load current threshold
        sw a0, 20(sp)       #stack current threshold
        csrrs a0, mcause, x0
        andi a0, a0, 31     #mcause & 0b11111 gives interrupt id
        slli a0, a0, 2      #interrupt id * 4 gives byte offset from base
        add a0, a0, a1      #intr base + offset
        lw a0, 0x114(a0)    #load current interrupt prio
        addi a0, a0, 1      #threshold must be 1 higher
        sw a0, 0x194(a1)    #set threshold
    #END
    csrrsi x0, mstatus, 8 #enable global interrupts
    jal ra, cpu_int_2_handler
    lw a0, 20(sp)  #load old prio
    #RETURN PRIO SUBROUTINE
    lui a1, 0x600C2 #intr base
    sw a0, 0x194(a1) #restore threshold
    #END
    lw a0, 12(sp) #load mstatus
    csrrw x0, mstatus, a0
    lw a0, 16(sp) #load mepc
    csrrw x0, mepc, a0
    lw a0, 0(sp)
    lw a1, 4(sp)
    lw ra, 8(sp)
    addi sp, sp, 24 #pop
    mret

cpu_int_1_handler:
cpu_int_2_handler:
cpu_int_3_handler:
cpu_int_4_handler:
cpu_int_5_handler:
cpu_int_6_handler:
cpu_int_7_handler:
cpu_int_8_handler:
cpu_int_9_handler:
cpu_int_10_handler:
cpu_int_11_handler:
cpu_int_12_handler:
cpu_int_13_handler:
cpu_int_14_handler:
cpu_int_15_handler:
cpu_int_16_handler:
cpu_int_17_handler:
cpu_int_18_handler:
cpu_int_19_handler:
cpu_int_20_handler:
cpu_int_21_handler:
cpu_int_22_handler:
cpu_int_23_handler:
cpu_int_24_handler:
cpu_int_25_handler:
cpu_int_26_handler:
cpu_int_27_handler:
cpu_int_28_handler:
cpu_int_29_handler:
cpu_int_30_handler:
cpu_int_31_handler:
    la ra, abort #abort since proper handler is not defined, this could also just load the default _start_trap_rust_hal address and let the hal handle it.
    jr ra
    "#,
}