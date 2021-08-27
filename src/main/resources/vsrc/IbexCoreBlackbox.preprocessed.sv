`define WT_DCACHE
`define DISABLE_TRACER
`define SRAM_NO_INIT
`define VERILATOR
// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Package with constants used by Ibex
 */
package ibex_pkg;

////////////////
// IO Structs //
////////////////

typedef struct packed {
  logic [31:0] current_pc;
  logic [31:0] next_pc;
  logic [31:0] last_data_addr;
  logic [31:0] exception_addr;
} crash_dump_t;

typedef struct packed {
  logic        dummy_instr_id;
  logic [4:0]  raddr_a;
  logic [4:0]  waddr_a;
  logic        we_a;
  logic [4:0]  raddr_b;
} core2rf_t;

/////////////////////
// Parameter Enums //
/////////////////////

typedef enum integer {
  RegFileFF    = 0,
  RegFileFPGA  = 1,
  RegFileLatch = 2
} regfile_e;

typedef enum integer {
  RV32MNone        = 0,
  RV32MSlow        = 1,
  RV32MFast        = 2,
  RV32MSingleCycle = 3
} rv32m_e;

typedef enum integer {
  RV32BNone     = 0,
  RV32BBalanced = 1,
  RV32BFull     = 2
} rv32b_e;

/////////////
// Opcodes //
/////////////

typedef enum logic [6:0] {
  OPCODE_LOAD     = 7'h03,
  OPCODE_MISC_MEM = 7'h0f,
  OPCODE_OP_IMM   = 7'h13,
  OPCODE_AUIPC    = 7'h17,
  OPCODE_STORE    = 7'h23,
  OPCODE_OP       = 7'h33,
  OPCODE_LUI      = 7'h37,
  OPCODE_BRANCH   = 7'h63,
  OPCODE_JALR     = 7'h67,
  OPCODE_JAL      = 7'h6f,
  OPCODE_SYSTEM   = 7'h73
} opcode_e;


////////////////////
// ALU operations //
////////////////////

typedef enum logic [5:0] {
  // Arithmetics
  ALU_ADD,
  ALU_SUB,

  // Logics
  ALU_XOR,
  ALU_OR,
  ALU_AND,
  // RV32B
  ALU_XNOR,
  ALU_ORN,
  ALU_ANDN,

  // Shifts
  ALU_SRA,
  ALU_SRL,
  ALU_SLL,
  // RV32B
  ALU_SRO,
  ALU_SLO,
  ALU_ROR,
  ALU_ROL,
  ALU_GREV,
  ALU_GORC,
  ALU_SHFL,
  ALU_UNSHFL,

  // Comparisons
  ALU_LT,
  ALU_LTU,
  ALU_GE,
  ALU_GEU,
  ALU_EQ,
  ALU_NE,
  // RV32B
  ALU_MIN,
  ALU_MINU,
  ALU_MAX,
  ALU_MAXU,

  // Pack
  // RV32B
  ALU_PACK,
  ALU_PACKU,
  ALU_PACKH,

  // Sign-Extend
  // RV32B
  ALU_SEXTB,
  ALU_SEXTH,

  // Bitcounting
  // RV32B
  ALU_CLZ,
  ALU_CTZ,
  ALU_PCNT,

  // Set lower than
  ALU_SLT,
  ALU_SLTU,

  // Ternary Bitmanip Operations
  // RV32B
  ALU_CMOV,
  ALU_CMIX,
  ALU_FSL,
  ALU_FSR,

  // Single-Bit Operations
  // RV32B
  ALU_SBSET,
  ALU_SBCLR,
  ALU_SBINV,
  ALU_SBEXT,

  // Bit Extract / Deposit
  // RV32B
  ALU_BEXT,
  ALU_BDEP,

  // Bit Field Place
  // RV32B
  ALU_BFP,

  // Carry-less Multiply
  // RV32B
  ALU_CLMUL,
  ALU_CLMULR,
  ALU_CLMULH,

  // Cyclic Redundancy Check
  ALU_CRC32_B,
  ALU_CRC32C_B,
  ALU_CRC32_H,
  ALU_CRC32C_H,
  ALU_CRC32_W,
  ALU_CRC32C_W
} alu_op_e;

typedef enum logic [1:0] {
  // Multiplier/divider
  MD_OP_MULL,
  MD_OP_MULH,
  MD_OP_DIV,
  MD_OP_REM
} md_op_e;


//////////////////////////////////
// Control and status registers //
//////////////////////////////////

// CSR operations
typedef enum logic [1:0] {
  CSR_OP_READ,
  CSR_OP_WRITE,
  CSR_OP_SET,
  CSR_OP_CLEAR
} csr_op_e;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} priv_lvl_e;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;

//////////////
// WB stage //
//////////////

// Type of instruction present in writeback stage
typedef enum logic[1:0] {
  WB_INSTR_LOAD,  // Instruction is awaiting load data
  WB_INSTR_STORE, // Instruction is awaiting store response
  WB_INSTR_OTHER  // Instruction doesn't fit into above categories
} wb_instr_type_e;

//////////////
// ID stage //
//////////////

// Operand a selection
typedef enum logic[1:0] {
  OP_A_REG_A,
  OP_A_FWD,
  OP_A_CURRPC,
  OP_A_IMM
} op_a_sel_e;

// Immediate a selection
typedef enum logic {
  IMM_A_Z,
  IMM_A_ZERO
} imm_a_sel_e;

// Operand b selection
typedef enum logic {
  OP_B_REG_B,
  OP_B_IMM
} op_b_sel_e;

// Immediate b selection
typedef enum logic [2:0] {
  IMM_B_I,
  IMM_B_S,
  IMM_B_B,
  IMM_B_U,
  IMM_B_J,
  IMM_B_INCR_PC,
  IMM_B_INCR_ADDR
} imm_b_sel_e;

// Regfile write data selection
typedef enum logic {
  RF_WD_EX,
  RF_WD_CSR
} rf_wd_sel_e;

//////////////
// IF stage //
//////////////

// PC mux selection
typedef enum logic [2:0] {
  PC_BOOT,
  PC_JUMP,
  PC_EXC,
  PC_ERET,
  PC_DRET,
  PC_BP
} pc_sel_e;

// Exception PC mux selection
typedef enum logic [1:0] {
  EXC_PC_EXC,
  EXC_PC_IRQ,
  EXC_PC_DBD,
  EXC_PC_DBG_EXC // Exception while in debug mode
} exc_pc_sel_e;

// Interrupt requests
typedef struct packed {
  logic        irq_software;
  logic        irq_timer;
  logic        irq_external;
  logic [14:0] irq_fast; // 15 fast interrupts,
                         // one interrupt is reserved for NMI (not visible through mip/mie)
} irqs_t;

// Exception cause
typedef enum logic [5:0] {
  EXC_CAUSE_IRQ_SOFTWARE_M     = {1'b1, 5'd03},
  EXC_CAUSE_IRQ_TIMER_M        = {1'b1, 5'd07},
  EXC_CAUSE_IRQ_EXTERNAL_M     = {1'b1, 5'd11},
  // EXC_CAUSE_IRQ_FAST_0      = {1'b1, 5'd16},
  // EXC_CAUSE_IRQ_FAST_14     = {1'b1, 5'd30},
  EXC_CAUSE_IRQ_NM             = {1'b1, 5'd31}, // == EXC_CAUSE_IRQ_FAST_15
  EXC_CAUSE_INSN_ADDR_MISA     = {1'b0, 5'd00},
  EXC_CAUSE_INSTR_ACCESS_FAULT = {1'b0, 5'd01},
  EXC_CAUSE_ILLEGAL_INSN       = {1'b0, 5'd02},
  EXC_CAUSE_BREAKPOINT         = {1'b0, 5'd03},
  EXC_CAUSE_LOAD_ACCESS_FAULT  = {1'b0, 5'd05},
  EXC_CAUSE_STORE_ACCESS_FAULT = {1'b0, 5'd07},
  EXC_CAUSE_ECALL_UMODE        = {1'b0, 5'd08},
  EXC_CAUSE_ECALL_MMODE        = {1'b0, 5'd11}
} exc_cause_e;

// Debug cause
typedef enum logic [2:0] {
  DBG_CAUSE_NONE    = 3'h0,
  DBG_CAUSE_EBREAK  = 3'h1,
  DBG_CAUSE_TRIGGER = 3'h2,
  DBG_CAUSE_HALTREQ = 3'h3,
  DBG_CAUSE_STEP    = 3'h4
} dbg_cause_e;

// ICache constants
parameter int unsigned ADDR_W          = 32;
parameter int unsigned BUS_SIZE        = 32;
parameter int unsigned BUS_BYTES       = BUS_SIZE/8;
parameter int unsigned BUS_W           = $clog2(BUS_BYTES);
parameter int unsigned IC_SIZE_BYTES   = 4096;
parameter int unsigned IC_NUM_WAYS     = 2;
parameter int unsigned IC_LINE_SIZE    = 64;
parameter int unsigned IC_LINE_BYTES   = IC_LINE_SIZE/8;
parameter int unsigned IC_LINE_W       = $clog2(IC_LINE_BYTES);
parameter int unsigned IC_NUM_LINES    = IC_SIZE_BYTES / IC_NUM_WAYS / IC_LINE_BYTES;
parameter int unsigned IC_LINE_BEATS   = IC_LINE_BYTES / BUS_BYTES;
parameter int unsigned IC_LINE_BEATS_W = $clog2(IC_LINE_BEATS);
parameter int unsigned IC_INDEX_W      = $clog2(IC_NUM_LINES);
parameter int unsigned IC_INDEX_HI     = IC_INDEX_W + IC_LINE_W - 1;
parameter int unsigned IC_TAG_SIZE     = ADDR_W - IC_INDEX_W - IC_LINE_W + 1; // 1 valid bit
parameter int unsigned IC_OUTPUT_BEATS = (BUS_BYTES / 2); // number of halfwords

// PMP constants
parameter int unsigned PMP_MAX_REGIONS      = 16;
parameter int unsigned PMP_CFG_W            = 8;

// PMP acces type
parameter int unsigned PMP_I = 0;
parameter int unsigned PMP_D = 1;

typedef enum logic [1:0] {
  PMP_ACC_EXEC    = 2'b00,
  PMP_ACC_WRITE   = 2'b01,
  PMP_ACC_READ    = 2'b10
} pmp_req_e;

// PMP cfg structures
typedef enum logic [1:0] {
  PMP_MODE_OFF   = 2'b00,
  PMP_MODE_TOR   = 2'b01,
  PMP_MODE_NA4   = 2'b10,
  PMP_MODE_NAPOT = 2'b11
} pmp_cfg_mode_e;

typedef struct packed {
  logic          lock;
  pmp_cfg_mode_e mode;
  logic          exec;
  logic          write;
  logic          read;
} pmp_cfg_t;

// Machine Security Configuration (ePMP)
typedef struct packed {
  logic rlb;  // Rule Locking Bypass
  logic mmwp; // Machine Mode Whitelist Policy
  logic mml;  // Machine Mode Lockdown
} pmp_mseccfg_t;

// CSRs
typedef enum logic[11:0] {
  // Machine information
  CSR_MHARTID   = 12'hF14,

  // Machine trap setup
  CSR_MSTATUS   = 12'h300,
  CSR_MISA      = 12'h301,
  CSR_MIE       = 12'h304,
  CSR_MTVEC     = 12'h305,
  CSR_MCOUNTEREN= 12'h306,

  // Machine trap handling
  CSR_MSCRATCH  = 12'h340,
  CSR_MEPC      = 12'h341,
  CSR_MCAUSE    = 12'h342,
  CSR_MTVAL     = 12'h343,
  CSR_MIP       = 12'h344,

  // Physical memory protection
  CSR_PMPCFG0   = 12'h3A0,
  CSR_PMPCFG1   = 12'h3A1,
  CSR_PMPCFG2   = 12'h3A2,
  CSR_PMPCFG3   = 12'h3A3,
  CSR_PMPADDR0  = 12'h3B0,
  CSR_PMPADDR1  = 12'h3B1,
  CSR_PMPADDR2  = 12'h3B2,
  CSR_PMPADDR3  = 12'h3B3,
  CSR_PMPADDR4  = 12'h3B4,
  CSR_PMPADDR5  = 12'h3B5,
  CSR_PMPADDR6  = 12'h3B6,
  CSR_PMPADDR7  = 12'h3B7,
  CSR_PMPADDR8  = 12'h3B8,
  CSR_PMPADDR9  = 12'h3B9,
  CSR_PMPADDR10 = 12'h3BA,
  CSR_PMPADDR11 = 12'h3BB,
  CSR_PMPADDR12 = 12'h3BC,
  CSR_PMPADDR13 = 12'h3BD,
  CSR_PMPADDR14 = 12'h3BE,
  CSR_PMPADDR15 = 12'h3BF,

  // ePMP control
  CSR_MSECCFG   = 12'h747,
  CSR_MSECCFGH  = 12'h757,

  // Debug trigger
  CSR_TSELECT   = 12'h7A0,
  CSR_TDATA1    = 12'h7A1,
  CSR_TDATA2    = 12'h7A2,
  CSR_TDATA3    = 12'h7A3,
  CSR_MCONTEXT  = 12'h7A8,
  CSR_SCONTEXT  = 12'h7AA,

  // Debug/trace
  CSR_DCSR      = 12'h7b0,
  CSR_DPC       = 12'h7b1,

  // Debug
  CSR_DSCRATCH0 = 12'h7b2, // optional
  CSR_DSCRATCH1 = 12'h7b3, // optional

  // Machine Counter/Timers
  CSR_MCOUNTINHIBIT  = 12'h320,
  CSR_MHPMEVENT3     = 12'h323,
  CSR_MHPMEVENT4     = 12'h324,
  CSR_MHPMEVENT5     = 12'h325,
  CSR_MHPMEVENT6     = 12'h326,
  CSR_MHPMEVENT7     = 12'h327,
  CSR_MHPMEVENT8     = 12'h328,
  CSR_MHPMEVENT9     = 12'h329,
  CSR_MHPMEVENT10    = 12'h32A,
  CSR_MHPMEVENT11    = 12'h32B,
  CSR_MHPMEVENT12    = 12'h32C,
  CSR_MHPMEVENT13    = 12'h32D,
  CSR_MHPMEVENT14    = 12'h32E,
  CSR_MHPMEVENT15    = 12'h32F,
  CSR_MHPMEVENT16    = 12'h330,
  CSR_MHPMEVENT17    = 12'h331,
  CSR_MHPMEVENT18    = 12'h332,
  CSR_MHPMEVENT19    = 12'h333,
  CSR_MHPMEVENT20    = 12'h334,
  CSR_MHPMEVENT21    = 12'h335,
  CSR_MHPMEVENT22    = 12'h336,
  CSR_MHPMEVENT23    = 12'h337,
  CSR_MHPMEVENT24    = 12'h338,
  CSR_MHPMEVENT25    = 12'h339,
  CSR_MHPMEVENT26    = 12'h33A,
  CSR_MHPMEVENT27    = 12'h33B,
  CSR_MHPMEVENT28    = 12'h33C,
  CSR_MHPMEVENT29    = 12'h33D,
  CSR_MHPMEVENT30    = 12'h33E,
  CSR_MHPMEVENT31    = 12'h33F,
  CSR_MCYCLE         = 12'hB00,
  CSR_MINSTRET       = 12'hB02,
  CSR_MHPMCOUNTER3   = 12'hB03,
  CSR_MHPMCOUNTER4   = 12'hB04,
  CSR_MHPMCOUNTER5   = 12'hB05,
  CSR_MHPMCOUNTER6   = 12'hB06,
  CSR_MHPMCOUNTER7   = 12'hB07,
  CSR_MHPMCOUNTER8   = 12'hB08,
  CSR_MHPMCOUNTER9   = 12'hB09,
  CSR_MHPMCOUNTER10  = 12'hB0A,
  CSR_MHPMCOUNTER11  = 12'hB0B,
  CSR_MHPMCOUNTER12  = 12'hB0C,
  CSR_MHPMCOUNTER13  = 12'hB0D,
  CSR_MHPMCOUNTER14  = 12'hB0E,
  CSR_MHPMCOUNTER15  = 12'hB0F,
  CSR_MHPMCOUNTER16  = 12'hB10,
  CSR_MHPMCOUNTER17  = 12'hB11,
  CSR_MHPMCOUNTER18  = 12'hB12,
  CSR_MHPMCOUNTER19  = 12'hB13,
  CSR_MHPMCOUNTER20  = 12'hB14,
  CSR_MHPMCOUNTER21  = 12'hB15,
  CSR_MHPMCOUNTER22  = 12'hB16,
  CSR_MHPMCOUNTER23  = 12'hB17,
  CSR_MHPMCOUNTER24  = 12'hB18,
  CSR_MHPMCOUNTER25  = 12'hB19,
  CSR_MHPMCOUNTER26  = 12'hB1A,
  CSR_MHPMCOUNTER27  = 12'hB1B,
  CSR_MHPMCOUNTER28  = 12'hB1C,
  CSR_MHPMCOUNTER29  = 12'hB1D,
  CSR_MHPMCOUNTER30  = 12'hB1E,
  CSR_MHPMCOUNTER31  = 12'hB1F,
  CSR_MCYCLEH        = 12'hB80,
  CSR_MINSTRETH      = 12'hB82,
  CSR_MHPMCOUNTER3H  = 12'hB83,
  CSR_MHPMCOUNTER4H  = 12'hB84,
  CSR_MHPMCOUNTER5H  = 12'hB85,
  CSR_MHPMCOUNTER6H  = 12'hB86,
  CSR_MHPMCOUNTER7H  = 12'hB87,
  CSR_MHPMCOUNTER8H  = 12'hB88,
  CSR_MHPMCOUNTER9H  = 12'hB89,
  CSR_MHPMCOUNTER10H = 12'hB8A,
  CSR_MHPMCOUNTER11H = 12'hB8B,
  CSR_MHPMCOUNTER12H = 12'hB8C,
  CSR_MHPMCOUNTER13H = 12'hB8D,
  CSR_MHPMCOUNTER14H = 12'hB8E,
  CSR_MHPMCOUNTER15H = 12'hB8F,
  CSR_MHPMCOUNTER16H = 12'hB90,
  CSR_MHPMCOUNTER17H = 12'hB91,
  CSR_MHPMCOUNTER18H = 12'hB92,
  CSR_MHPMCOUNTER19H = 12'hB93,
  CSR_MHPMCOUNTER20H = 12'hB94,
  CSR_MHPMCOUNTER21H = 12'hB95,
  CSR_MHPMCOUNTER22H = 12'hB96,
  CSR_MHPMCOUNTER23H = 12'hB97,
  CSR_MHPMCOUNTER24H = 12'hB98,
  CSR_MHPMCOUNTER25H = 12'hB99,
  CSR_MHPMCOUNTER26H = 12'hB9A,
  CSR_MHPMCOUNTER27H = 12'hB9B,
  CSR_MHPMCOUNTER28H = 12'hB9C,
  CSR_MHPMCOUNTER29H = 12'hB9D,
  CSR_MHPMCOUNTER30H = 12'hB9E,
  CSR_MHPMCOUNTER31H = 12'hB9F,
  CSR_CPUCTRL        = 12'h7C0,
  CSR_SECURESEED     = 12'h7C1
} csr_num_e;

// CSR pmp-related offsets
parameter logic [11:0] CSR_OFF_PMP_CFG  = 12'h3A0; // pmp_cfg  @ 12'h3a0 - 12'h3a3
parameter logic [11:0] CSR_OFF_PMP_ADDR = 12'h3B0; // pmp_addr @ 12'h3b0 - 12'h3bf

// CSR status bits
parameter int unsigned CSR_MSTATUS_MIE_BIT      = 3;
parameter int unsigned CSR_MSTATUS_MPIE_BIT     = 7;
parameter int unsigned CSR_MSTATUS_MPP_BIT_LOW  = 11;
parameter int unsigned CSR_MSTATUS_MPP_BIT_HIGH = 12;
parameter int unsigned CSR_MSTATUS_MPRV_BIT     = 17;
parameter int unsigned CSR_MSTATUS_TW_BIT       = 21;

// CSR machine ISA
parameter logic [1:0] CSR_MISA_MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32

// CSR interrupt pending/enable bits
parameter int unsigned CSR_MSIX_BIT      = 3;
parameter int unsigned CSR_MTIX_BIT      = 7;
parameter int unsigned CSR_MEIX_BIT      = 11;
parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
parameter int unsigned CSR_MFIX_BIT_HIGH = 30;

// CSR Machine Security Configuration bits
parameter int unsigned CSR_MSECCFG_MML_BIT  = 0;
parameter int unsigned CSR_MSECCFG_MMWP_BIT = 1;
parameter int unsigned CSR_MSECCFG_RLB_BIT  = 2;

// These LFSR parameters have been generated with
// $ opentitan/util/design/gen-lfsr-seed.py --width 32 --seed 2480124384 --prefix ""
parameter int LfsrWidth = 32;
typedef logic [LfsrWidth-1:0] lfsr_seed_t;
typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
parameter lfsr_seed_t RndCnstLfsrSeedDefault = 32'hac533bf4;
parameter lfsr_perm_t RndCnstLfsrPermDefault = {
  160'h1e35ecba467fd1b12e958152c04fa43878a8daed
};

endpackage
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that don't support assertions. See
// prim_assert.sv for documentation for each of the macros.

`define ASSERT_I(__name, __prop)
`define ASSERT_INIT(__name, __prop)
`define ASSERT_FINAL(__name, __prop)
`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSUME_I(__name, __prop)
`elsif SYNTHESIS
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that don't support assertions. See
// prim_assert.sv for documentation for each of the macros.

`define ASSERT_I(__name, __prop)
`define ASSERT_INIT(__name, __prop)
`define ASSERT_FINAL(__name, __prop)
`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
`define ASSUME_I(__name, __prop)
`elsif YOSYS
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for formal verification with Yosys. See prim_assert.sv
// for documentation for each of the macros.

`define ASSERT_I(__name, __prop)    \
  always_comb begin : __name        \
    assert (__prop);                \
  end

`define ASSERT_INIT(__name, __prop)    \
  initial begin : __name               \
    assert (__prop);                   \
  end

// This doesn't make much sense for a formal tool (we never get to the final block!)
`define ASSERT_FINAL(__name, __prop)

`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assert (__prop);                                       \
  end

`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                             \
    if (! (__rst !== '0)) __name: assert (! (__prop));                                         \
  end

// Yosys uses 2-state logic, so this doesn't make sense here
`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)

`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin : __name                                             \
    cover ((! (__rst !== '0)) && (__prop));                                             \
  end

`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assume (__prop);                                       \
  end

`define ASSUME_I(__name, __prop)              \
  always_comb begin : __name                  \
    assume (__prop);                          \
  end
 `define INC_ASSERT
`else
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that support full SystemVerilog and SVA syntax.
// See prim_assert.sv for documentation for each of the macros.

`define ASSERT_I(__name, __prop) \
  __name: assert (__prop)        \
    else begin                   \
      `ASSERT_ERROR(__name)      \
    end

// Formal tools will ignore the initial construct, so use static assertion as a workaround.
// This workaround terminates design elaboration if the __prop predict is false.
// It calls $fatal() with the first argument equal to 2, it outputs the statistics about the memory
// and CPU time.
`define ASSERT_INIT(__name, __prop)                                          \
`ifdef FPV_ON                                                                \
  if (!(__prop)) $fatal(2, "Fatal static assertion [%s]: (%s) is not true.", \
                        (__name), (__prop));                                 \
`else                                                                        \
  initial begin                                                              \
    __name: assert (__prop)                                                  \
      else begin                                                             \
        `ASSERT_ERROR(__name)                                                \
      end                                                                    \
  end                                                                        \
`endif

`define ASSERT_FINAL(__name, __prop)                                         \
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `ASSERT_ERROR(__name)                                                \
      end                                                                    \
  end

`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `ASSERT_ERROR(__name)                                                              \
    end

`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) not (__prop))         \
    else begin                                                                                 \
      `ASSERT_ERROR(__name)                                                                    \
    end

`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, !$isunknown(__sig), __clk, __rst)

`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: cover property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop));

`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assume property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `ASSERT_ERROR(__name)                                                              \
    end

`define ASSUME_I(__name, __prop) \
  __name: assume (__prop)        \
    else begin                   \
      `ASSERT_ERROR(__name)      \
    end
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_ram_1p_pkg;

  typedef struct packed {
    logic       cfg_en;
    logic [3:0] cfg;
  } cfg_t;

  typedef struct packed {
    cfg_t ram_cfg;  // configuration for ram
    cfg_t rf_cfg;   // configuration for regfile
  } ram_1p_cfg_t;

  parameter ram_1p_cfg_t RAM_1P_CFG_DEFAULT = '0;

endpackage // prim_ram_1p_pkg
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Constants for use in primitives
//
// This file is a stop-gap until the DV file list is generated by FuseSoC.
// Its contents are taken from the file which would be generated by FuseSoC.
// https://github.com/lowRISC/ibex/issues/893

package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric,
    ImplXilinx
  } impl_e;
endpackage : prim_pkg
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Arithmetic logic unit
 */
module ibex_alu #(
  parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone
) (
    input  ibex_pkg::alu_op_e operator_i,
    input  logic [31:0]       operand_a_i,
    input  logic [31:0]       operand_b_i,

    input  logic              instr_first_cycle_i,

    input  logic [32:0]       multdiv_operand_a_i,
    input  logic [32:0]       multdiv_operand_b_i,

    input  logic              multdiv_sel_i,

    input  logic [31:0]       imd_val_q_i[2],
    output logic [31:0]       imd_val_d_o[2],
    output logic [1:0]        imd_val_we_o,

    output logic [31:0]       adder_result_o,
    output logic [33:0]       adder_result_ext_o,

    output logic [31:0]       result_o,
    output logic              comparison_result_o,
    output logic              is_equal_result_o
);
  import ibex_pkg::*;

  logic [31:0] operand_a_rev;
  logic [32:0] operand_b_neg;

  // bit reverse operand_a for left shifts and bit counting
  for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
    assign operand_a_rev[k] = operand_a_i[31-k];
  end

  ///////////
  // Adder //
  ///////////

  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;

  always_comb begin
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      ALU_SUB,

      // Comparator OPs
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU,

      // MinMax OPs (RV32B Ops)
      ALU_MIN,  ALU_MINU,
      ALU_MAX,  ALU_MAXU: adder_op_b_negate = 1'b1;

      default:;
    endcase
  end

  // prepare operand a
  assign adder_in_a    = multdiv_sel_i ? multdiv_operand_a_i : {operand_a_i,1'b1};

  // prepare operand b
  assign operand_b_neg = {operand_b_i,1'b0} ^ {33{1'b1}};
  always_comb begin
    unique case(1'b1)
      multdiv_sel_i:     adder_in_b = multdiv_operand_b_i;
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default :          adder_in_b = {operand_b_i, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result       = adder_result_ext_o[32:1];

  assign adder_result_o     = adder_result;

  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      ALU_GE,
      ALU_LT,
      ALU_SLT,
      // RV32B only
      ALU_MIN,
      ALU_MAX: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);
  assign is_equal_result_o = is_equal;

  // Is greater equal
  always_comb begin
    if ((operand_a_i[31] ^ operand_b_i[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a_i[31] ^ (cmp_signed);
    end
  end

  // GTE unsigned:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1

  // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      ALU_EQ:             cmp_result =  is_equal;
      ALU_NE:             cmp_result = ~is_equal;
      ALU_GE,   ALU_GEU,
      ALU_MAX,  ALU_MAXU: cmp_result = is_greater_equal; // RV32B only
      ALU_LT,   ALU_LTU,
      ALU_MIN,  ALU_MINU, //RV32B only
      ALU_SLT,  ALU_SLTU: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  assign comparison_result_o = cmp_result;

  ///////////
  // Shift //
  ///////////

  // The shifter structure consists of a 33-bit shifter: 32-bit operand + 1 bit extension for
  // arithmetic shifts and one-shift support.
  // Rotations and funnel shifts are implemented as multi-cycle instructions.
  // The shifter is also used for single-bit instructions and bit-field place as detailed below.
  //
  // Standard Shifts
  // ===============
  // For standard shift instructions, the direction of the shift is to the right by default. For
  // left shifts, the signal shift_left signal is set. If so, the operand is initially reversed,
  // shifted to the right by the specified amount and shifted back again. For arithmetic- and
  // one-shifts the 33rd bit of the shifter operand can is set accordingly.
  //
  // Multicycle Shifts
  // =================
  //
  // Rotation
  // --------
  // For rotations, the operand signals operand_a_i and operand_b_i are kept constant to rs1 and
  // rs2 respectively.
  //
  // Rotation pseudocode:
  //   shift_amt = rs2 & 31;
  //   multicycle_result = (rs1 >> shift_amt) | (rs1 << (32 - shift_amt));
  //                       ^-- cycle 0 -----^ ^-- cycle 1 --------------^
  //
  // Funnel Shifts
  // -------------
  // For funnel shifs, operand_a_i is tied to rs1 in the first cycle and rs3 in the
  // second cycle. operand_b_i is always tied to rs2. The order of applying the shift amount or
  // its complement is determined by bit [5] of shift_amt.
  //
  // Funnel shift Pseudocode: (fsl)
  //  shift_amt = rs2 & 63;
  //  shift_amt_compl = 32 - shift_amt[4:0]
  //  if (shift_amt >=33):
  //     multicycle_result = (rs1 >> shift_amt_compl[4:0]) | (rs3 << shift_amt[4:0]);
  //                         ^-- cycle 0 ----------------^ ^-- cycle 1 ------------^
  //  else if (shift_amt <= 31 && shift_amt > 0):
  //     multicycle_result = (rs1 << shift_amt[4:0]) | (rs3 >> shift_amt_compl[4:0]);
  //                         ^-- cycle 0 ----------^ ^-- cycle 1 -------------------^
  //  For shift_amt == 0, 32, both shift_amt[4:0] and shift_amt_compl[4:0] == '0.
  //  these cases need to be handled separately outside the shifting structure:
  //  else if (shift_amt == 32):
  //     multicycle_result = rs3
  //  else if (shift_amt == 0):
  //     multicycle_result = rs1.
  //
  // Single-Bit Instructions
  // =======================
  // Single bit instructions operate on bit operand_b_i[4:0] of operand_a_i.

  // The operations sbset, sbclr and sbinv are implemented by generation of a bit-mask using the
  // shifter structure. This is done by left-shifting the operand 32'h1 by the required amount.
  // The signal shift_sbmode multiplexes the shifter input and sets the signal shift_left.
  // Further processing is taken care of by a separate structure.
  //
  // For sbext, the bit defined by operand_b_i[4:0] is to be returned. This is done by simply
  // shifting operand_a_i to the right by the required amount and returning bit [0] of the result.
  //
  // Bit-Field Place
  // ===============
  // The shifter structure is shared to compute bfp_mask << bfp_off.

  logic       shift_left;
  logic       shift_ones;
  logic       shift_arith;
  logic       shift_funnel;
  logic       shift_sbmode;
  logic [5:0] shift_amt;
  logic [5:0] shift_amt_compl; // complementary shift amount (32 - shift_amt)

  logic        [31:0] shift_operand;
  logic signed [32:0] shift_result_ext_signed;
  logic        [32:0] shift_result_ext;
  logic               unused_shift_result_ext;
  logic        [31:0] shift_result;
  logic        [31:0] shift_result_rev;

  // zbf
  logic bfp_op;
  logic [4:0]  bfp_len;
  logic [4:0]  bfp_off;
  logic [31:0] bfp_mask;
  logic [31:0] bfp_mask_rev;
  logic [31:0] bfp_result;

  // bfp: shares the shifter structure to compute bfp_mask << bfp_off
  assign bfp_op = (RV32B != RV32BNone) ? (operator_i == ALU_BFP) : 1'b0;
  assign bfp_len = {~(|operand_b_i[27:24]), operand_b_i[27:24]}; // len = 0 encodes for len = 16
  assign bfp_off = operand_b_i[20:16];
  assign bfp_mask = (RV32B != RV32BNone) ? ~(32'hffff_ffff << bfp_len) : '0;
  for (genvar i=0; i<32; i++) begin : gen_rev_bfp_mask
    assign bfp_mask_rev[i] = bfp_mask[31-i];
  end

  assign bfp_result =(RV32B != RV32BNone) ?
      (~shift_result & operand_a_i) | ((operand_b_i & bfp_mask) << bfp_off) : '0;

  // bit shift_amt[5]: word swap bit: only considered for FSL/FSR.
  // if set, reverse operations in first and second cycle.
  assign shift_amt[5] = operand_b_i[5] & shift_funnel;
  assign shift_amt_compl = 32 - operand_b_i[4:0];

  always_comb begin
    if (bfp_op) begin
      shift_amt[4:0] = bfp_off ; // length field of bfp control word
    end else begin
      shift_amt[4:0] = instr_first_cycle_i ?
          (operand_b_i[5] && shift_funnel ? shift_amt_compl[4:0] : operand_b_i[4:0]) :
          (operand_b_i[5] && shift_funnel ? operand_b_i[4:0] : shift_amt_compl[4:0]);
    end
  end

  // single-bit mode: shift
  assign shift_sbmode = (RV32B != RV32BNone) ?
      (operator_i == ALU_SBSET) | (operator_i == ALU_SBCLR) | (operator_i == ALU_SBINV) : 1'b0;

  // left shift if this is:
  // * a standard left shift (slo, sll)
  // * a rol in the first cycle
  // * a ror in the second cycle
  // * fsl: without word-swap bit: first cycle, else: second cycle
  // * fsr: without word-swap bit: second cycle, else: first cycle
  // * a single-bit instruction: sbclr, sbset, sbinv (excluding sbext)
  // * bfp: bfp_mask << bfp_off
  always_comb begin
    unique case (operator_i)
      ALU_SLL: shift_left = 1'b1;
      ALU_SLO,
      ALU_BFP: shift_left = (RV32B != RV32BNone) ? 1'b1 : 1'b0;
      ALU_ROL: shift_left = (RV32B != RV32BNone) ? instr_first_cycle_i : 0;
      ALU_ROR: shift_left = (RV32B != RV32BNone) ? ~instr_first_cycle_i : 0;
      ALU_FSL: shift_left = (RV32B != RV32BNone) ?
        (shift_amt[5] ? ~instr_first_cycle_i : instr_first_cycle_i) : 1'b0;
      ALU_FSR: shift_left = (RV32B != RV32BNone) ?
          (shift_amt[5] ? instr_first_cycle_i : ~instr_first_cycle_i) : 1'b0;
      default: shift_left = 1'b0;
    endcase
    if (shift_sbmode) begin
      shift_left = 1'b1;
    end
  end

  assign shift_arith  = (operator_i == ALU_SRA);
  assign shift_ones   =
      (RV32B != RV32BNone) ? (operator_i == ALU_SLO) | (operator_i == ALU_SRO) : 1'b0;
  assign shift_funnel =
      (RV32B != RV32BNone) ? (operator_i == ALU_FSL) | (operator_i == ALU_FSR) : 1'b0;

  // shifter structure.
  always_comb begin
    // select shifter input
    // for bfp, sbmode and shift_left the corresponding bit-reversed input is chosen.
    if (RV32B == RV32BNone) begin
      shift_operand = shift_left ? operand_a_rev : operand_a_i;
    end else begin
      unique case (1'b1)
        bfp_op:       shift_operand = bfp_mask_rev;
        shift_sbmode: shift_operand = 32'h8000_0000;
        default:      shift_operand = shift_left ? operand_a_rev : operand_a_i;
      endcase
    end

    shift_result_ext_signed =
        $signed({shift_ones | (shift_arith & shift_operand[31]), shift_operand}) >>> shift_amt[4:0];
    shift_result_ext = $unsigned(shift_result_ext_signed);

    shift_result            = shift_result_ext[31:0];
    unused_shift_result_ext = shift_result_ext[32];

    for (int unsigned i=0; i<32; i++) begin
      shift_result_rev[i] = shift_result[31-i];
    end

    shift_result = shift_left ? shift_result_rev : shift_result;

  end

  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;
  logic [31:0] bwlogic_result;

  logic bwlogic_op_b_negate;

  always_comb begin
    unique case (operator_i)
      // Logic-with-negate OPs (RV32B Ops)
      ALU_XNOR,
      ALU_ORN,
      ALU_ANDN: bwlogic_op_b_negate = (RV32B != RV32BNone) ? 1'b1 : 1'b0;
      ALU_CMIX: bwlogic_op_b_negate = (RV32B != RV32BNone) ? ~instr_first_cycle_i : 1'b0;
      default:  bwlogic_op_b_negate = 1'b0;
    endcase
  end

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b_i;

  assign bwlogic_or_result  = operand_a_i | bwlogic_operand_b;
  assign bwlogic_and_result = operand_a_i & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a_i ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR)  | (operator_i == ALU_ORN);
  assign bwlogic_and = (operator_i == ALU_AND) | (operator_i == ALU_ANDN);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end

  logic [5:0]  bitcnt_result;
  logic [31:0] minmax_result;
  logic [31:0] pack_result;
  logic [31:0] sext_result;
  logic [31:0] singlebit_result;
  logic [31:0] rev_result;
  logic [31:0] shuffle_result;
  logic [31:0] butterfly_result;
  logic [31:0] invbutterfly_result;
  logic [31:0] clmul_result;
  logic [31:0] multicycle_result;

  if (RV32B != RV32BNone) begin : g_alu_rvb

    /////////////////
    // Bitcounting //
    /////////////////

    // The bit-counter structure computes the number of set bits in its operand. Partial results
    // (from left to right) are needed to compute the control masks for computation of bext/bdep
    // by the butterfly network, if implemented.
    // For pcnt, clz and ctz, only the end result is used.

    logic        zbe_op;
    logic        bitcnt_ctz;
    logic        bitcnt_clz;
    logic        bitcnt_cz;
    logic [31:0] bitcnt_bits;
    logic [31:0] bitcnt_mask_op;
    logic [31:0] bitcnt_bit_mask;
    logic [ 5:0] bitcnt_partial [32];
    logic [31:0] bitcnt_partial_lsb_d;
    logic [31:0] bitcnt_partial_msb_d;


    assign bitcnt_ctz    = operator_i == ALU_CTZ;
    assign bitcnt_clz    = operator_i == ALU_CLZ;
    assign bitcnt_cz     = bitcnt_ctz | bitcnt_clz;
    assign bitcnt_result = bitcnt_partial[31];

    // Bit-mask generation for clz and ctz:
    // The bit mask is generated by spreading the lowest-order set bit in the operand to all
    // higher order bits. The resulting mask is inverted to cover the lowest order zeros. In order
    // to create the bit mask for leading zeros, the input operand needs to be reversed.
    assign bitcnt_mask_op = bitcnt_clz ? operand_a_rev : operand_a_i;

    always_comb begin
      bitcnt_bit_mask = bitcnt_mask_op;
      bitcnt_bit_mask |= bitcnt_bit_mask << 1;
      bitcnt_bit_mask |= bitcnt_bit_mask << 2;
      bitcnt_bit_mask |= bitcnt_bit_mask << 4;
      bitcnt_bit_mask |= bitcnt_bit_mask << 8;
      bitcnt_bit_mask |= bitcnt_bit_mask << 16;
      bitcnt_bit_mask = ~bitcnt_bit_mask;
    end

    assign zbe_op = (operator_i == ALU_BEXT) | (operator_i == ALU_BDEP);

    always_comb begin
      case(1'b1)
        zbe_op:      bitcnt_bits = operand_b_i;
        bitcnt_cz:   bitcnt_bits = bitcnt_bit_mask & ~bitcnt_mask_op; // clz / ctz
        default:     bitcnt_bits = operand_a_i; // pcnt
      endcase
    end

    // The parallel prefix counter is of the structure of a Brent-Kung Adder. In the first
    // log2(width) stages, the sum of the n preceding bit lines is computed for the bit lines at
    // positions 2**n-1 (power-of-two positions) where n denotes the current stage.
    // In stage n=log2(width), the count for position width-1 (the MSB) is finished.
    // For the intermediate values, an inverse adder tree then computes the bit counts for the bit
    // lines at positions
    // m = 2**(n-1) + i*2**(n-2), where i = [1 ... width / 2**(n-1)-1] and n = [log2(width) ... 2].
    // Thus, at every subsequent stage the result of two previously unconnected sub-trees is
    // summed, starting at the node summing bits [width/2-1 : 0] and [3*width/4-1: width/2]
    // and moving to iteratively sum up all the sub-trees.
    // The inverse adder tree thus features log2(width) - 1 stages the first of these stages is a
    // single addition at position 3*width/4 - 1. It does not interfere with the last
    // stage of the primary adder tree. These stages can thus be folded together, resulting in a
    // total of 2*log2(width)-2 stages.
    // For more details refer to R. Brent, H. T. Kung, "A Regular Layout for Parallel Adders",
    // (1982).
    // For a bitline at position p, only bits
    // bitcnt_partial[max(i, such that p % log2(i) == 0)-1 : 0] are needed for generation of the
    // butterfly network control signals. The adders in the intermediate value adder tree thus need
    // not be full 5-bit adders. We leave the optimization to the synthesis tools.
    //
    // Consider the following 8-bit example for illustraton.
    //
    // let bitcnt_bits = 8'babcdefgh.
    //
    //                   a  b  c  d  e  f  g  h
    //                   | /:  | /:  | /:  | /:
    //                   |/ :  |/ :  |/ :  |/ :
    // stage 1:          +  :  +  :  +  :  +  :
    //                   |  : /:  :  |  : /:  :
    //                   |,--+ :  :  |,--+ :  :
    // stage 2:          +  :  :  :  +  :  :  :
    //                   |  :  |  : /:  :  :  :
    //                   |,-----,--+ :  :  :  : ^-primary adder tree
    // stage 3:          +  :  +  :  :  :  :  : -------------------------
    //                   :  | /| /| /| /| /|  : ,-intermediate adder tree
    //                   :  |/ |/ |/ |/ |/ :  :
    // stage 4           :  +  +  +  +  +  :  :
    //                   :  :  :  :  :  :  :  :
    // bitcnt_partial[i] 7  6  5  4  3  2  1  0

    always_comb begin
      bitcnt_partial = '{default: '0};
      // stage 1
      for (int unsigned i=1; i<32; i+=2) begin
        bitcnt_partial[i] = {5'h0, bitcnt_bits[i]} + {5'h0, bitcnt_bits[i-1]};
      end
      // stage 2
      for (int unsigned i=3; i<32; i+=4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 3
      for (int unsigned i=7; i<32; i+=8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end
      // stage 4
      for (int unsigned i=15; i <32; i+=16) begin
        bitcnt_partial[i] = bitcnt_partial[i-8] + bitcnt_partial[i];
      end
      // stage 5
      bitcnt_partial[31] = bitcnt_partial[15] + bitcnt_partial[31];
      // ^- primary adder tree
      // -------------------------------
      // ,-intermediate value adder tree
      bitcnt_partial[23] = bitcnt_partial[15] + bitcnt_partial[23];

      // stage 6
      for (int unsigned i=11; i<32; i+=8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end

      // stage 7
      for (int unsigned i=5; i<32; i+=4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 8
      bitcnt_partial[0] = {5'h0, bitcnt_bits[0]};
      for (int unsigned i=2; i<32; i+=2) begin
        bitcnt_partial[i] = bitcnt_partial[i-1] + {5'h0, bitcnt_bits[i]};
      end
    end

    ///////////////
    // Min / Max //
    ///////////////

    assign minmax_result = cmp_result ? operand_a_i : operand_b_i;

    //////////
    // Pack //
    //////////

    logic packu;
    logic packh;
    assign packu = operator_i == ALU_PACKU;
    assign packh = operator_i == ALU_PACKH;

    always_comb begin
      unique case (1'b1)
        packu:   pack_result = {operand_b_i[31:16], operand_a_i[31:16]};
        packh:   pack_result = {16'h0, operand_b_i[7:0], operand_a_i[7:0]};
        default: pack_result = {operand_b_i[15:0], operand_a_i[15:0]};
      endcase
    end

    //////////
    // Sext //
    //////////

    assign sext_result = (operator_i == ALU_SEXTB) ?
        { {24{operand_a_i[7]}}, operand_a_i[7:0]} : { {16{operand_a_i[15]}}, operand_a_i[15:0]};

    /////////////////////////////
    // Single-bit Instructions //
    /////////////////////////////

    always_comb begin
      unique case (operator_i)
        ALU_SBSET: singlebit_result = operand_a_i | shift_result;
        ALU_SBCLR: singlebit_result = operand_a_i & ~shift_result;
        ALU_SBINV: singlebit_result = operand_a_i ^ shift_result;
        default:   singlebit_result = {31'h0, shift_result[0]}; // ALU_SBEXT
      endcase
    end

    ////////////////////////////////////
    // General Reverse and Or-combine //
    ////////////////////////////////////

    // Only a subset of the General reverse and or-combine instructions are implemented in the
    // balanced version of the B extension. Currently rev, rev8 and orc.b are supported in the
    // base extension.

    logic [4:0] zbp_shift_amt;
    logic gorc_op;

    assign gorc_op = (operator_i == ALU_GORC);
    assign zbp_shift_amt[2:0] = (RV32B == RV32BFull) ? shift_amt[2:0] : {3{&shift_amt[2:0]}};
    assign zbp_shift_amt[4:3] = (RV32B == RV32BFull) ? shift_amt[4:3] : {2{&shift_amt[4:3]}};

    always_comb begin
      rev_result = operand_a_i;

      if (zbp_shift_amt[0]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h5555_5555) <<  1) |
                     ((rev_result & 32'haaaa_aaaa) >>  1);
      end

      if (zbp_shift_amt[1]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h3333_3333) <<  2) |
                     ((rev_result & 32'hcccc_cccc) >>  2);
      end

      if (zbp_shift_amt[2]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h0f0f_0f0f) <<  4) |
                     ((rev_result & 32'hf0f0_f0f0) >>  4);
      end

      if (zbp_shift_amt[3]) begin
        rev_result = (gorc_op & (RV32B == RV32BFull) ? rev_result : 32'h0) |
                     ((rev_result & 32'h00ff_00ff) <<  8) |
                     ((rev_result & 32'hff00_ff00) >>  8);
      end

      if (zbp_shift_amt[4]) begin
        rev_result = (gorc_op & (RV32B == RV32BFull) ? rev_result : 32'h0) |
                     ((rev_result & 32'h0000_ffff) << 16) |
                     ((rev_result & 32'hffff_0000) >> 16);
      end
    end

    logic crc_hmode;
    logic crc_bmode;
    logic [31:0] clmul_result_rev;

    if (RV32B == RV32BFull) begin : gen_alu_rvb_full

      /////////////////////////
      // Shuffle / Unshuffle //
      /////////////////////////

      localparam logic [31:0] SHUFFLE_MASK_L [4] =
          '{32'h00ff_0000, 32'h0f00_0f00, 32'h3030_3030, 32'h4444_4444};
      localparam logic [31:0] SHUFFLE_MASK_R [4] =
          '{32'h0000_ff00, 32'h00f0_00f0, 32'h0c0c_0c0c, 32'h2222_2222};

      localparam logic [31:0] FLIP_MASK_L [4] =
          '{32'h2200_1100, 32'h0044_0000, 32'h4411_0000, 32'h1100_0000};
      localparam logic [31:0] FLIP_MASK_R [4] =
          '{32'h0088_0044, 32'h0000_2200, 32'h0000_8822, 32'h0000_0088};

      logic [31:0] SHUFFLE_MASK_NOT [4];
      for(genvar i = 0; i < 4; i++) begin : gen_shuffle_mask_not
        assign SHUFFLE_MASK_NOT[i] = ~(SHUFFLE_MASK_L[i] | SHUFFLE_MASK_R[i]);
      end

      logic shuffle_flip;
      assign shuffle_flip = operator_i == ALU_UNSHFL;

      logic [3:0] shuffle_mode;

      always_comb begin
        shuffle_result = operand_a_i;

        if (shuffle_flip) begin
          shuffle_mode[3] = shift_amt[0];
          shuffle_mode[2] = shift_amt[1];
          shuffle_mode[1] = shift_amt[2];
          shuffle_mode[0] = shift_amt[3];
        end else begin
          shuffle_mode = shift_amt[3:0];
        end

        if (shuffle_flip) begin
          shuffle_result = (shuffle_result & 32'h8822_4411) |
              ((shuffle_result << 6)  & FLIP_MASK_L[0]) |
              ((shuffle_result >> 6)  & FLIP_MASK_R[0]) |
              ((shuffle_result << 9)  & FLIP_MASK_L[1]) |
              ((shuffle_result >> 9)  & FLIP_MASK_R[1]) |
              ((shuffle_result << 15) & FLIP_MASK_L[2]) |
              ((shuffle_result >> 15) & FLIP_MASK_R[2]) |
              ((shuffle_result << 21) & FLIP_MASK_L[3]) |
              ((shuffle_result >> 21) & FLIP_MASK_R[3]);
        end

        if (shuffle_mode[3]) begin
          shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[0]) |
              (((shuffle_result << 8) & SHUFFLE_MASK_L[0]) |
              ((shuffle_result >> 8) & SHUFFLE_MASK_R[0]));
        end
        if (shuffle_mode[2]) begin
          shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[1]) |
              (((shuffle_result << 4) & SHUFFLE_MASK_L[1]) |
              ((shuffle_result >> 4) & SHUFFLE_MASK_R[1]));
        end
        if (shuffle_mode[1]) begin
          shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[2]) |
              (((shuffle_result << 2) & SHUFFLE_MASK_L[2]) |
              ((shuffle_result >> 2) & SHUFFLE_MASK_R[2]));
        end
        if (shuffle_mode[0]) begin
          shuffle_result = (shuffle_result & SHUFFLE_MASK_NOT[3]) |
              (((shuffle_result << 1) & SHUFFLE_MASK_L[3]) |
              ((shuffle_result >> 1) & SHUFFLE_MASK_R[3]));
        end

        if (shuffle_flip) begin
          shuffle_result = (shuffle_result & 32'h8822_4411) |
              ((shuffle_result << 6)  & FLIP_MASK_L[0]) |
              ((shuffle_result >> 6)  & FLIP_MASK_R[0]) |
              ((shuffle_result << 9)  & FLIP_MASK_L[1]) |
              ((shuffle_result >> 9)  & FLIP_MASK_R[1]) |
              ((shuffle_result << 15) & FLIP_MASK_L[2]) |
              ((shuffle_result >> 15) & FLIP_MASK_R[2]) |
              ((shuffle_result << 21) & FLIP_MASK_L[3]) |
              ((shuffle_result >> 21) & FLIP_MASK_R[3]);
        end
      end

      ///////////////
      // Butterfly //
      ///////////////

      // The butterfly / inverse butterfly network executing bext/bdep (zbe) instructions.
      // For bdep, the control bits mask of a local left region is generated by
      // the inverse of a n-bit left rotate and complement upon wrap (LROTC) operation by the number
      // of ones in the deposit bitmask to the right of the segment. n hereby denotes the width
      // of the according segment. The bitmask for a pertaining local right region is equal to the
      // corresponding local left region. Bext uses an analogue inverse process.
      // Consider the following 8-bit example.  For details, see Hilewitz et al. "Fast Bit Gather,
      // Bit Scatter and Bit Permuation Instructions for Commodity Microprocessors", (2008).
      //
      // The bext/bdep instructions are completed in 2 cycles. In the first cycle, the control
      // bitmask is prepared by executing the parallel prefix bit count. In the second cycle,
      // the bit swapping is executed according to the control masks.

      // 8-bit example:  (Hilewitz et al.)
      // Consider the instruction bdep operand_a_i deposit_mask
      // Let operand_a_i = 8'babcd_efgh
      //    deposit_mask = 8'b1010_1101
      //
      // control bitmask for stage 1:
      //  - number of ones in the right half of the deposit bitmask: 3
      //  - width of the segment: 4
      //  - control bitmask = ~LROTC(4'b0, 3)[3:0] = 4'b1000
      //
      // control bitmask:   c3 c2  c1 c0  c3 c2  c1 c0
      //                    1  0   0  0   1  0   0  0
      //                    <- L ----->   <- R ----->
      // operand_a_i        a  b   c  d   e  f   g  h
      //                    :\ |   |  |  /:  |   |  |
      //                    : +|---|--|-+ :  |   |  |
      //                    :/ |   |  |  \:  |   |  |
      // stage 1            e  b   c  d   a  f   g  h
      //                    <L->   <R->   <L->   <R->
      // control bitmask:   c3 c2  c3 c2  c1 c0  c1 c0
      //                    1  1   1  1   1  0   1  0
      //                    :\ :\ /: /:   :\ |  /:  |
      //                    : +:-+-:+ :   : +|-+ :  |
      //                    :/ :/ \: \:   :/ |  \:  |
      // stage 2            c  d   e  b   g  f   a  h
      //                    L  R   L  R   L  R   L  R
      // control bitmask:   c3 c3  c2 c2  c1 c1  c0 c0
      //                    1  1   0  0   1  1   0  0
      //                    :\/:   |  |   :\/:   |  |
      //                    :  :   |  |   :  :   |  |
      //                    :/\:   |  |   :/\:   |  |
      // stage 3            d  c   e  b   f  g   a  h
      // & deposit bitmask: 1  0   1  0   1  1   0  1
      // result:            d  0   e  0   f  g   0  h

      logic [ 5:0] bitcnt_partial_q [32];

      // first cycle
      // Store partial bitcnts
      for (genvar i=0; i<32; i++) begin : gen_bitcnt_reg_in_lsb
        assign bitcnt_partial_lsb_d[i] = bitcnt_partial[i][0];
      end

      for (genvar i=0; i<16; i++) begin : gen_bitcnt_reg_in_b1
        assign bitcnt_partial_msb_d[i] = bitcnt_partial[2*i+1][1];
      end

      for (genvar i=0; i<8; i++) begin : gen_bitcnt_reg_in_b2
        assign bitcnt_partial_msb_d[16+i] = bitcnt_partial[4*i+3][2];
      end

      for (genvar i=0; i<4; i++) begin : gen_bitcnt_reg_in_b3
        assign bitcnt_partial_msb_d[24+i] = bitcnt_partial[8*i+7][3];
      end

      for (genvar i=0; i<2; i++) begin : gen_bitcnt_reg_in_b4
        assign bitcnt_partial_msb_d[28+i] = bitcnt_partial[16*i+15][4];
      end

      assign bitcnt_partial_msb_d[30] = bitcnt_partial[31][5];
      assign bitcnt_partial_msb_d[31] = 1'b0; // unused

      // Second cycle
      // Load partial bitcnts
      always_comb begin
        bitcnt_partial_q = '{default: '0};

        for (int unsigned i=0; i<32; i++) begin : gen_bitcnt_reg_out_lsb
          bitcnt_partial_q[i][0] = imd_val_q_i[0][i];
        end

        for (int unsigned i=0; i<16; i++) begin : gen_bitcnt_reg_out_b1
          bitcnt_partial_q[2*i+1][1] = imd_val_q_i[1][i];
        end

        for (int unsigned i=0; i<8; i++) begin : gen_bitcnt_reg_out_b2
          bitcnt_partial_q[4*i+3][2] = imd_val_q_i[1][16+i];
        end

        for (int unsigned i=0; i<4; i++) begin : gen_bitcnt_reg_out_b3
          bitcnt_partial_q[8*i+7][3] = imd_val_q_i[1][24+i];
        end

        for (int unsigned i=0; i<2; i++) begin : gen_bitcnt_reg_out_b4
          bitcnt_partial_q[16*i+15][4] = imd_val_q_i[1][28+i];
        end

        bitcnt_partial_q[31][5] = imd_val_q_i[1][30];
      end

      logic [31:0] butterfly_mask_l[5];
      logic [31:0] butterfly_mask_r[5];
      logic [31:0] butterfly_mask_not[5];
      logic [31:0] lrotc_stage [5]; // left rotate and complement upon wrap

      // number of bits in local r = 32 / 2**(stage + 1) = 16/2**stage
      `define _N(stg) (16 >> stg)

      // bext / bdep control bit generation
      for (genvar stg=0; stg<5; stg++) begin : gen_butterfly_ctrl_stage
        // number of segs: 2** stg
        for (genvar seg=0; seg<2**stg; seg++) begin : gen_butterfly_ctrl

          assign lrotc_stage[stg][2*`_N(stg)*(seg+1)-1 : 2*`_N(stg)*seg] =
              {{`_N(stg){1'b0}},{`_N(stg){1'b1}}} <<
                bitcnt_partial_q[`_N(stg)*(2*seg+1)-1][$clog2(`_N(stg)):0];

          assign butterfly_mask_l[stg][`_N(stg)*(2*seg+2)-1 : `_N(stg)*(2*seg+1)]
                   = ~lrotc_stage[stg][`_N(stg)*(2*seg+2)-1 : `_N(stg)*(2*seg+1)];

          assign butterfly_mask_r[stg][`_N(stg)*(2*seg+1)-1 : `_N(stg)*(2*seg)]
                   = ~lrotc_stage[stg][`_N(stg)*(2*seg+2)-1 : `_N(stg)*(2*seg+1)];

          assign butterfly_mask_l[stg][`_N(stg)*(2*seg+1)-1 : `_N(stg)*(2*seg)]   = '0;
          assign butterfly_mask_r[stg][`_N(stg)*(2*seg+2)-1 : `_N(stg)*(2*seg+1)] = '0;
        end
      end
      `undef _N

      for (genvar stg=0; stg<5; stg++) begin : gen_butterfly_not
        assign butterfly_mask_not[stg] =
            ~(butterfly_mask_l[stg] | butterfly_mask_r[stg]);
      end

      always_comb begin
        butterfly_result = operand_a_i;

        butterfly_result = butterfly_result & butterfly_mask_not[0] |
            ((butterfly_result & butterfly_mask_l[0]) >> 16)|
            ((butterfly_result & butterfly_mask_r[0]) << 16);

        butterfly_result = butterfly_result & butterfly_mask_not[1] |
            ((butterfly_result & butterfly_mask_l[1]) >> 8)|
            ((butterfly_result & butterfly_mask_r[1]) << 8);

        butterfly_result = butterfly_result & butterfly_mask_not[2] |
            ((butterfly_result & butterfly_mask_l[2]) >> 4)|
            ((butterfly_result & butterfly_mask_r[2]) << 4);

        butterfly_result = butterfly_result & butterfly_mask_not[3] |
            ((butterfly_result & butterfly_mask_l[3]) >> 2)|
            ((butterfly_result & butterfly_mask_r[3]) << 2);

        butterfly_result = butterfly_result & butterfly_mask_not[4] |
            ((butterfly_result & butterfly_mask_l[4]) >> 1)|
            ((butterfly_result & butterfly_mask_r[4]) << 1);

        butterfly_result = butterfly_result & operand_b_i;
      end

      always_comb begin
        invbutterfly_result = operand_a_i & operand_b_i;

        invbutterfly_result = invbutterfly_result & butterfly_mask_not[4] |
            ((invbutterfly_result & butterfly_mask_l[4]) >> 1)|
            ((invbutterfly_result & butterfly_mask_r[4]) << 1);

        invbutterfly_result = invbutterfly_result & butterfly_mask_not[3] |
            ((invbutterfly_result & butterfly_mask_l[3]) >> 2)|
            ((invbutterfly_result & butterfly_mask_r[3]) << 2);

        invbutterfly_result = invbutterfly_result & butterfly_mask_not[2] |
            ((invbutterfly_result & butterfly_mask_l[2]) >> 4)|
            ((invbutterfly_result & butterfly_mask_r[2]) << 4);

        invbutterfly_result = invbutterfly_result & butterfly_mask_not[1] |
            ((invbutterfly_result & butterfly_mask_l[1]) >> 8)|
            ((invbutterfly_result & butterfly_mask_r[1]) << 8);

        invbutterfly_result = invbutterfly_result & butterfly_mask_not[0] |
            ((invbutterfly_result & butterfly_mask_l[0]) >> 16)|
            ((invbutterfly_result & butterfly_mask_r[0]) << 16);
      end

      ///////////////////////////////////////////////////
      // Carry-less Multiply + Cyclic Redundancy Check //
      ///////////////////////////////////////////////////

      // Carry-less multiplication can be understood as multiplication based on
      // the addition interpreted as the bit-wise xor operation.
      //
      // Example: 1101 X 1011 = 1111111:
      //
      //       1011 X 1101
      //       -----------
      //              1101
      //         xor 1101
      //         ---------
      //             10111
      //        xor 0000
      //        ----------
      //            010111
      //       xor 1101
      //       -----------
      //           1111111
      //
      // Architectural details:
      //         A 32 x 32-bit array
      //         [ operand_b[i] ? (operand_a << i) : '0 for i in 0 ... 31 ]
      //         is generated. The entries of the array are pairwise 'xor-ed'
      //         together in a 5-stage binary tree.
      //
      //
      // Cyclic Redundancy Check:
      //
      // CRC-32 (CRC-32/ISO-HDLC) and CRC-32C (CRC-32/ISCSI) are directly implemented. For
      // documentation of the crc configuration (crc-polynomials, initialization, reflection, etc.)
      // see http://reveng.sourceforge.net/crc-catalogue/all.htm
      // A useful guide to crc arithmetic and algorithms is given here:
      // http://www.piclist.com/techref/method/math/crcguide.html.
      //
      // The CRC operation solves the following equation using binary polynomial arithmetic:
      //
      // rev(rd)(x) = rev(rs1)(x) * x**n mod {1, P}(x)
      //
      // where P denotes lower 32 bits of the corresponding CRC polynomial, rev(a) the bit reversal
      // of a, n = 8,16, or 32 for .b, .h, .w -variants. {a, b} denotes bit concatenation.
      //
      // Using barret reduction, one can show that
      //
      // M(x) mod P(x) = R(x) =
      //          (M(x) * x**n) & {deg(P(x)'{1'b1}}) ^ (M(x) x**-(deg(P(x) - n)) cx mu(x) cx P(x),
      //
      // Where mu(x) = polydiv(x**64, {1,P}) & 0xffffffff. Here, 'cx' refers to carry-less
      // multiplication. Substituting rev(rd)(x) for R(x) and rev(rs1)(x) for M(x) and solving for
      // rd(x) with P(x) a crc32 polynomial (deg(P(x)) = 32), we get
      //
      // rd = rev( (rev(rs1) << n)  ^ ((rev(rs1) >> (32-n)) cx mu cx P)
      //    = (rs1 >> n) ^ rev(rev( (rs1 << (32-n)) cx rev(mu)) cx P)
      //                       ^-- cycle 0--------------------^
      //      ^- cycle 1 -------------------------------------------^
      //
      // In the last step we used the fact that carry-less multiplication is bit-order agnostic:
      // rev(a cx b) = rev(a) cx rev(b).

      logic clmul_rmode;
      logic clmul_hmode;
      logic [31:0] clmul_op_a;
      logic [31:0] clmul_op_b;
      logic [31:0] operand_b_rev;
      logic [31:0] clmul_and_stage[32];
      logic [31:0] clmul_xor_stage1[16];
      logic [31:0] clmul_xor_stage2[8];
      logic [31:0] clmul_xor_stage3[4];
      logic [31:0] clmul_xor_stage4[2];

      logic [31:0] clmul_result_raw;

      for (genvar i=0; i<32; i++) begin: gen_rev_operand_b
        assign operand_b_rev[i] = operand_b_i[31-i];
      end

      assign clmul_rmode = operator_i == ALU_CLMULR;
      assign clmul_hmode = operator_i == ALU_CLMULH;

      // CRC
      localparam logic [31:0] CRC32_POLYNOMIAL = 32'h04c1_1db7;
      localparam logic [31:0] CRC32_MU_REV = 32'hf701_1641;

      localparam logic [31:0] CRC32C_POLYNOMIAL = 32'h1edc_6f41;
      localparam logic [31:0] CRC32C_MU_REV = 32'hdea7_13f1;

      logic crc_op;

      logic crc_cpoly;

      logic [31:0] crc_operand;
      logic [31:0] crc_poly;
      logic [31:0] crc_mu_rev;

      assign crc_op = (operator_i == ALU_CRC32C_W) | (operator_i == ALU_CRC32_W) |
                      (operator_i == ALU_CRC32C_H) | (operator_i == ALU_CRC32_H) |
                      (operator_i == ALU_CRC32C_B) | (operator_i == ALU_CRC32_B);

      assign crc_cpoly = (operator_i == ALU_CRC32C_W) |
                         (operator_i == ALU_CRC32C_H) |
                         (operator_i == ALU_CRC32C_B);

      assign crc_hmode = (operator_i == ALU_CRC32_H) | (operator_i == ALU_CRC32C_H);
      assign crc_bmode = (operator_i == ALU_CRC32_B) | (operator_i == ALU_CRC32C_B);

      assign crc_poly   = crc_cpoly ? CRC32C_POLYNOMIAL : CRC32_POLYNOMIAL;
      assign crc_mu_rev = crc_cpoly ? CRC32C_MU_REV : CRC32_MU_REV;

      always_comb begin
        unique case(1'b1)
          crc_bmode: crc_operand = {operand_a_i[7:0], 24'h0};
          crc_hmode: crc_operand = {operand_a_i[15:0], 16'h0};
          default:   crc_operand = operand_a_i;
        endcase
      end

      // Select clmul input
      always_comb begin
        if (crc_op) begin
          clmul_op_a = instr_first_cycle_i ? crc_operand : imd_val_q_i[0];
          clmul_op_b = instr_first_cycle_i ? crc_mu_rev : crc_poly;
        end else begin
          clmul_op_a = clmul_rmode | clmul_hmode ? operand_a_rev : operand_a_i;
          clmul_op_b = clmul_rmode | clmul_hmode ? operand_b_rev : operand_b_i;
        end
      end

      for (genvar i=0; i<32; i++) begin : gen_clmul_and_op
        assign clmul_and_stage[i] = clmul_op_b[i] ? clmul_op_a << i : '0;
      end

      for (genvar i=0; i<16; i++) begin : gen_clmul_xor_op_l1
        assign clmul_xor_stage1[i] = clmul_and_stage[2*i] ^ clmul_and_stage[2*i+1];
      end

      for (genvar i=0; i<8; i++) begin : gen_clmul_xor_op_l2
        assign clmul_xor_stage2[i] = clmul_xor_stage1[2*i] ^ clmul_xor_stage1[2*i+1];
      end

      for (genvar i=0; i<4; i++) begin : gen_clmul_xor_op_l3
        assign clmul_xor_stage3[i] = clmul_xor_stage2[2*i] ^ clmul_xor_stage2[2*i+1];
      end

      for (genvar i=0; i<2; i++) begin : gen_clmul_xor_op_l4
        assign clmul_xor_stage4[i] = clmul_xor_stage3[2*i] ^ clmul_xor_stage3[2*i+1];
      end

      assign clmul_result_raw = clmul_xor_stage4[0] ^ clmul_xor_stage4[1];

      for (genvar i=0; i<32; i++) begin : gen_rev_clmul_result
        assign clmul_result_rev[i] = clmul_result_raw[31-i];
      end

      // clmulr_result = rev(clmul(rev(a), rev(b)))
      // clmulh_result = clmulr_result >> 1
      always_comb begin
        case(1'b1)
          clmul_rmode: clmul_result = clmul_result_rev;
          clmul_hmode: clmul_result = {1'b0, clmul_result_rev[31:1]};
          default:     clmul_result = clmul_result_raw;
        endcase
      end
    end else begin : gen_alu_rvb_notfull
      logic [31:0] unused_imd_val_q_1;
      assign unused_imd_val_q_1   = imd_val_q_i[1];
      assign shuffle_result       = '0;
      assign butterfly_result     = '0;
      assign invbutterfly_result  = '0;
      assign clmul_result         = '0;
      // support signals
      assign bitcnt_partial_lsb_d = '0;
      assign bitcnt_partial_msb_d = '0;
      assign clmul_result_rev     = '0;
      assign crc_bmode            = '0;
      assign crc_hmode            = '0;
    end

    //////////////////////////////////////
    // Multicycle Bitmanip Instructions //
    //////////////////////////////////////
    // Ternary instructions + Shift Rotations + Bit extract/deposit + CRC
    // For ternary instructions (zbt), operand_a_i is tied to rs1 in the first cycle and rs3 in the
    // second cycle. operand_b_i is always tied to rs2.

    always_comb begin
      unique case (operator_i)
        ALU_CMOV: begin
          multicycle_result = (operand_b_i == 32'h0) ? operand_a_i : imd_val_q_i[0];
          imd_val_d_o = '{operand_a_i, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_CMIX: begin
          multicycle_result = imd_val_q_i[0] | bwlogic_and_result;
          imd_val_d_o = '{bwlogic_and_result, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_FSR, ALU_FSL,
        ALU_ROL, ALU_ROR: begin
          if (shift_amt[4:0] == 5'h0) begin
            multicycle_result = shift_amt[5] ? operand_a_i : imd_val_q_i[0];
          end else begin
            multicycle_result = imd_val_q_i[0] | shift_result;
          end
          imd_val_d_o = '{shift_result, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_CRC32_W, ALU_CRC32C_W,
        ALU_CRC32_H, ALU_CRC32C_H,
        ALU_CRC32_B, ALU_CRC32C_B: begin
          if (RV32B == RV32BFull) begin
            unique case(1'b1)
              crc_bmode: multicycle_result = clmul_result_rev ^ (operand_a_i >> 8);
              crc_hmode: multicycle_result = clmul_result_rev ^ (operand_a_i >> 16);
              default:   multicycle_result = clmul_result_rev;
            endcase
            imd_val_d_o = '{clmul_result_rev, 32'h0};
            if (instr_first_cycle_i) begin
              imd_val_we_o = 2'b01;
            end else begin
              imd_val_we_o = 2'b00;
            end
          end else begin
            imd_val_d_o = '{operand_a_i, 32'h0};
            imd_val_we_o = 2'b00;
            multicycle_result = '0;
          end
        end

        ALU_BEXT, ALU_BDEP: begin
          if (RV32B == RV32BFull) begin
            multicycle_result = (operator_i == ALU_BDEP) ? butterfly_result : invbutterfly_result;
            imd_val_d_o = '{bitcnt_partial_lsb_d, bitcnt_partial_msb_d};
            if (instr_first_cycle_i) begin
              imd_val_we_o = 2'b11;
            end else begin
              imd_val_we_o = 2'b00;
            end
          end else begin
            imd_val_d_o = '{operand_a_i, 32'h0};
            imd_val_we_o = 2'b00;
            multicycle_result = '0;
          end
        end

        default: begin
          imd_val_d_o = '{operand_a_i, 32'h0};
          imd_val_we_o = 2'b00;
          multicycle_result = '0;
        end
      endcase
    end


  end else begin : g_no_alu_rvb
    logic [31:0] unused_imd_val_q[2];
    assign unused_imd_val_q           = imd_val_q_i;
    logic [31:0] unused_butterfly_result;
    assign unused_butterfly_result    = butterfly_result;
    logic [31:0] unused_invbutterfly_result;
    assign unused_invbutterfly_result = invbutterfly_result;
    // RV32B result signals
    assign bitcnt_result       = '0;
    assign minmax_result       = '0;
    assign pack_result         = '0;
    assign sext_result         = '0;
    assign singlebit_result    = '0;
    assign rev_result          = '0;
    assign shuffle_result      = '0;
    assign butterfly_result    = '0;
    assign invbutterfly_result = '0;
    assign clmul_result        = '0;
    assign multicycle_result   = '0;
    // RV32B support signals
    assign imd_val_d_o         = '{default: '0};
    assign imd_val_we_o        = '{default: '0};
  end

  ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B)
      ALU_XOR,  ALU_XNOR,
      ALU_OR,   ALU_ORN,
      ALU_AND,  ALU_ANDN: result_o = bwlogic_result;

      // Adder Operations
      ALU_ADD,  ALU_SUB: result_o = adder_result;

      // Shift Operations
      ALU_SLL,  ALU_SRL,
      ALU_SRA,
      // RV32B
      ALU_SLO,  ALU_SRO: result_o = shift_result;

      // Shuffle Operations (RV32B)
      ALU_SHFL, ALU_UNSHFL: result_o = shuffle_result;

      // Comparison Operations
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: result_o = {31'h0,cmp_result};

      // MinMax Operations (RV32B)
      ALU_MIN,  ALU_MAX,
      ALU_MINU, ALU_MAXU: result_o = minmax_result;

      // Bitcount Operations (RV32B)
      ALU_CLZ, ALU_CTZ,
      ALU_PCNT: result_o = {26'h0, bitcnt_result};

      // Pack Operations (RV32B)
      ALU_PACK, ALU_PACKH,
      ALU_PACKU: result_o = pack_result;

      // Sign-Extend (RV32B)
      ALU_SEXTB, ALU_SEXTH: result_o = sext_result;

      // Ternary Bitmanip Operations (RV32B)
      ALU_CMIX, ALU_CMOV,
      ALU_FSL,  ALU_FSR,
      // Rotate Shift (RV32B)
      ALU_ROL, ALU_ROR,
      // Cyclic Redundancy Checks (RV32B)
      ALU_CRC32_W, ALU_CRC32C_W,
      ALU_CRC32_H, ALU_CRC32C_H,
      ALU_CRC32_B, ALU_CRC32C_B,
      // Bit Extract / Deposit (RV32B)
      ALU_BEXT, ALU_BDEP: result_o = multicycle_result;

      // Single-Bit Bitmanip Operations (RV32B)
      ALU_SBSET, ALU_SBCLR,
      ALU_SBINV, ALU_SBEXT: result_o = singlebit_result;

      // General Reverse / Or-combine (RV32B)
      ALU_GREV, ALU_GORC: result_o = rev_result;

      // Bit Field Place (RV32B)
      ALU_BFP: result_o = bfp_result;

      // Carry-less Multiply Operations (RV32B)
      ALU_CLMUL, ALU_CLMULR,
      ALU_CLMULH: result_o = clmul_result;

      default: ;
    endcase
  end

  logic unused_shift_amt_compl;
  assign unused_shift_amt_compl = shift_amt_compl[5];

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Branch Predictor
 *
 * This implements static branch prediction. It takes an instruction and its PC and determines if
 * it's a branch or a jump and calculates its target. For jumps it will always predict taken. For
 * branches it will predict taken if the PC offset is negative.
 *
 * This handles both compressed and uncompressed instructions. Compressed instructions must be in
 * the lower 16-bits of instr.
 *
 * The predictor is entirely combinational but takes clk/rst_n signals for use by assertions.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_branch_predict (
  input  logic clk_i,
  input  logic rst_ni,

  // Instruction from fetch stage
  input  logic [31:0] fetch_rdata_i,
  input  logic [31:0] fetch_pc_i,
  input  logic        fetch_valid_i,

  // Prediction for supplied instruction
  output logic        predict_branch_taken_o,
  output logic [31:0] predict_branch_pc_o
);
  import ibex_pkg::*;

  logic [31:0] imm_j_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_cj_type;
  logic [31:0] imm_cb_type;

  logic [31:0] branch_imm;

  logic [31:0] instr;

  logic instr_j;
  logic instr_b;
  logic instr_cj;
  logic instr_cb;

  logic instr_b_taken;

  // Provide short internal name for fetch_rdata_i due to reduce line wrapping
  assign instr = fetch_rdata_i;

  // Extract and sign-extend to 32-bit the various immediates that may be used to calculate the
  // target

  // Uncompressed immediates
  assign imm_j_type = { {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };
  assign imm_b_type = { {19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };

  // Compressed immediates
  assign imm_cj_type = { {20{instr[12]}}, instr[12], instr[8], instr[10:9], instr[6], instr[7],
    instr[2], instr[11], instr[5:3], 1'b0 };

  assign imm_cb_type = { {23{instr[12]}}, instr[12], instr[6:5], instr[2], instr[11:10],
    instr[4:3], 1'b0};

  // Determine if the instruction is a branch or a jump

  // Uncompressed branch/jump
  assign instr_b = opcode_e'(instr[6:0]) == OPCODE_BRANCH;
  assign instr_j = opcode_e'(instr[6:0]) == OPCODE_JAL;

  // Compressed branch/jump
  assign instr_cb = (instr[1:0] == 2'b01) & ((instr[15:13] == 3'b110) | (instr[15:13] == 3'b111));
  assign instr_cj = (instr[1:0] == 2'b01) & ((instr[15:13] == 3'b101) | (instr[15:13] == 3'b001));

  // Select out the branch offset for target calculation based upon the instruction type
  always_comb begin
    branch_imm = imm_b_type;

    unique case (1'b1)
      instr_j  : branch_imm = imm_j_type;
      instr_b  : branch_imm = imm_b_type;
      instr_cj : branch_imm = imm_cj_type;
      instr_cb : branch_imm = imm_cb_type;
      default : ;
    endcase
  end

  `ASSERT_IF(BranchInsTypeOneHot, $onehot0({instr_j, instr_b, instr_cj, instr_cb}), fetch_valid_i)

  // Determine branch prediction, taken if offset is negative
  assign instr_b_taken = (instr_b & imm_b_type[31]) | (instr_cb & imm_cb_type[31]);

  // Always predict jumps taken otherwise take prediction from `instr_b_taken`
  assign predict_branch_taken_o = fetch_valid_i & (instr_j | instr_cj | instr_b_taken);
  // Calculate target
  assign predict_branch_pc_o    = fetch_pc_i + branch_imm;
endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Compressed instruction decoder
 *
 * Decodes RISC-V compressed instructions into their RV32 equivalent.
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_compressed_decoder (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        valid_i,
    input  logic [31:0] instr_i,
    output logic [31:0] instr_o,
    output logic        is_compressed_o,
    output logic        illegal_instr_o
);
  import ibex_pkg::*;

  // valid_i indicates if instr_i is valid and is used for assertions only.
  // The following signal is used to avoid possible lint errors.
  logic unused_valid;
  assign unused_valid = valid_i;

  ////////////////////////
  // Compressed decoder //
  ////////////////////////

  always_comb begin
    // By default, forward incoming instruction, mark it as legal.
    instr_o         = instr_i;
    illegal_instr_o = 1'b0;

    // Check if incoming instruction is compressed.
    unique case (instr_i[1:0])
      // C0
      2'b00: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.addi4spn -> addi rd', x2, imm
            instr_o = {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5],
                       instr_i[6], 2'b00, 5'h02, 3'b000, 2'b01, instr_i[4:2], {OPCODE_OP_IMM}};
            if (instr_i[12:5] == 8'b0)  illegal_instr_o = 1'b1;
          end

          3'b010: begin
            // c.lw -> lw rd', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12:10], instr_i[6],
                       2'b00, 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], {OPCODE_LOAD}};
          end

          3'b110: begin
            // c.sw -> sw rs2', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12], 2'b01, instr_i[4:2],
                       2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6],
                       2'b00, {OPCODE_STORE}};
          end

          3'b001,
          3'b011,
          3'b100,
          3'b101,
          3'b111: begin
            illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C1
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b01: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop
            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2],
                       instr_i[11:7], 3'b0, instr_i[11:7], {OPCODE_OP_IMM}};
          end

          3'b001, 3'b101: begin
            // 001: c.jal -> jal x1, imm
            // 101: c.j   -> jal x0, imm
            instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6],
                       instr_i[7], instr_i[2], instr_i[11], instr_i[5:3],
                       {9 {instr_i[12]}}, 4'b0, ~instr_i[15], {OPCODE_JAL}};
          end

          3'b010: begin
            // c.li -> addi rd, x0, nzimm
            // (c.li hints are translated into an addi hint)
            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0,
                       3'b0, instr_i[11:7], {OPCODE_OP_IMM}};
          end

          3'b011: begin
            // c.lui -> lui rd, imm
            // (c.lui hints are translated into a lui hint)
            instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], {OPCODE_LUI}};

            if (instr_i[11:7] == 5'h02) begin
              // c.addi16sp -> addi x2, x2, nzimm
              instr_o = {{3 {instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2],
                         instr_i[6], 4'b0, 5'h02, 3'b000, 5'h02, {OPCODE_OP_IMM}};
            end

            if ({instr_i[12], instr_i[6:2]} == 6'b0) illegal_instr_o = 1'b1;
          end

          3'b100: begin
            unique case (instr_i[11:10])
              2'b00,
              2'b01: begin
                // 00: c.srli -> srli rd, rd, shamt
                // 01: c.srai -> srai rd, rd, shamt
                // (c.srli/c.srai hints are translated into a srli/srai hint)
                instr_o = {1'b0, instr_i[10], 5'b0, instr_i[6:2], 2'b01, instr_i[9:7],
                           3'b101, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                if (instr_i[12] == 1'b1)  illegal_instr_o = 1'b1;
              end

              2'b10: begin
                // c.andi -> andi rd, rd, imm
                instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7],
                           3'b111, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
              end

              2'b11: begin
                unique case ({instr_i[12], instr_i[6:5]})
                  3'b000: begin
                    // c.sub -> sub rd', rd', rs2'
                    instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7],
                               3'b000, 2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b001: begin
                    // c.xor -> xor rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b100,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b010: begin
                    // c.or  -> or  rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b110,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b011: begin
                    // c.and -> and rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b111,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b100,
                  3'b101,
                  3'b110,
                  3'b111: begin
                    // 100: c.subw
                    // 101: c.addw
                    illegal_instr_o = 1'b1;
                  end

                  default: begin
                    illegal_instr_o = 1'b1;
                  end
                endcase
              end

              default: begin
                illegal_instr_o = 1'b1;
              end
            endcase
          end

          3'b110, 3'b111: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            instr_o = {{4 {instr_i[12]}}, instr_i[6:5], instr_i[2], 5'b0, 2'b01,
                       instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3],
                       instr_i[12], {OPCODE_BRANCH}};
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C2
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b10: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.slli -> slli rd, rd, shamt
            // (c.ssli hints are translated into a slli hint)
            instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], {OPCODE_OP_IMM}};
            if (instr_i[12] == 1'b1)  illegal_instr_o = 1'b1; // reserved for custom extensions
          end

          3'b010: begin
            // c.lwsp -> lw rd, imm(x2)
            instr_o = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00, 5'h02,
                       3'b010, instr_i[11:7], OPCODE_LOAD};
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b100: begin
            if (instr_i[12] == 1'b0) begin
              if (instr_i[6:2] != 5'b0) begin
                // c.mv -> add rd/rs1, x0, rs2
                // (c.mv hints are translated into an add hint)
                instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], {OPCODE_OP}};
              end else begin
                // c.jr -> jalr x0, rd/rs1, 0
                instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, {OPCODE_JALR}};
                if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
              end
            end else begin
              if (instr_i[6:2] != 5'b0) begin
                // c.add -> add rd, rd, rs2
                // (c.add hints are translated into an add hint)
                instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], {OPCODE_OP}};
              end else begin
                if (instr_i[11:7] == 5'b0) begin
                  // c.ebreak -> ebreak
                  instr_o = {32'h00_10_00_73};
                end else begin
                  // c.jalr -> jalr x1, rs1, 0
                  instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, {OPCODE_JALR}};
                end
              end
            end
          end

          3'b110: begin
            // c.swsp -> sw rs2, imm(x2)
            instr_o = {4'b0, instr_i[8:7], instr_i[12], instr_i[6:2], 5'h02, 3'b010,
                       instr_i[11:9], 2'b00, {OPCODE_STORE}};
          end

          3'b001,
          3'b011,
          3'b101,
          3'b111: begin
            illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // Incoming instruction is not compressed.
      2'b11:;

      default: begin
        illegal_instr_o = 1'b1;
      end
    endcase
  end

  assign is_compressed_o = (instr_i[1:0] != 2'b11);

  ////////////////
  // Assertions //
  ////////////////

  // The valid_i signal used to gate below assertions must be known.
  `ASSERT_KNOWN(IbexInstrValidKnown, valid_i)

  // Selectors must be known/valid.
  `ASSERT(IbexInstrLSBsKnown, valid_i |->
      !$isunknown(instr_i[1:0]))
  `ASSERT(IbexC0Known1, (valid_i && (instr_i[1:0] == 2'b00)) |->
      !$isunknown(instr_i[15:13]))
  `ASSERT(IbexC1Known1, (valid_i && (instr_i[1:0] == 2'b01)) |->
      !$isunknown(instr_i[15:13]))
  `ASSERT(IbexC1Known2, (valid_i && (instr_i[1:0] == 2'b01) && (instr_i[15:13] == 3'b100)) |->
      !$isunknown(instr_i[11:10]))
  `ASSERT(IbexC1Known3, (valid_i &&
      (instr_i[1:0] == 2'b01) && (instr_i[15:13] == 3'b100) && (instr_i[11:10] == 2'b11)) |->
      !$isunknown({instr_i[12], instr_i[6:5]}))
  `ASSERT(IbexC2Known1, (valid_i && (instr_i[1:0] == 2'b10)) |->
      !$isunknown(instr_i[15:13]))

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Main controller of the processor
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Disable it for synthesis and where explicitly requested (by defining
// DV_FCOV_DISABLE).
`ifdef SYNTHESIS
  `define DV_FCOV_DISABLE
`elsif YOSYS
  `define DV_FCOV_DISABLE
`endif

// Disable instantiations of FCOV coverpoints or covergroups.
`ifdef VERILATOR
  `define DV_FCOV_DISABLE_CP
`elsif DV_FCOV_DISABLE
  `define DV_FCOV_DISABLE_CP
`endif

// Instantiates a covergroup in an interface or module.
//
// This macro assumes that a covergroup of the same name as the NAME_ arg is defined in the
// interface or module. It just adds some extra signals and logic to control the creation of the
// covergroup instance with ~bit en_<cg_name>~. This defaults to 0. It is ORed with the external
// COND_ signal. The testbench can modify it at t = 0 based on the test being run.
// NOTE: This is not meant to be invoked inside a class.
//
// NAME_ : Name of the covergroup.
// COND_ : External condition / expr that controls the creation of the covergroup.
// ARGS_ : Arguments to covergroup instance, if any. Args MUST BE wrapped in (..).
`ifndef DV_FCOV_INSTANTIATE_CG
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ())
`else
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ()) \
    bit en_``NAME_ = 1'b0; \
    NAME_ NAME_``_inst; \
    initial begin \
      /* The #1 delay below allows any part of the tb to control the conditions first at t = 0. */ \
      #1; \
      if ((en_``NAME_) || (COND_)) begin \
        $display("%0t: (%0s:%0d) [%m] %0s", $time, `__FILE__, `__LINE__, \
                 {"Creating covergroup ", `"NAME_`"}); \
        NAME_``_inst = new``ARGS_; \
      end \
    end
`endif
`endif

// Creates a coverpoint for an expression where only the expression true case is of interest for
// coverage (e.g. where the expression indicates an event has occured).
`ifndef DV_FCOV_EXPR_SEEN
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_)
`else
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_) cp_``NAME_: coverpoint EXPR_ { bins seen = {1}; }
`endif
`endif

// Creates a SVA cover that can be used in a covergroup.
//
// This macro creates an unnamed SVA cover from the property (or an expression) `PROP_` and an event
// with the name `EV_NAME_`. When the SVA cover is hit, the event is triggered. A coverpoint can
// cover the `triggered` property of the event.
`ifndef DV_FCOV_SVA
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni)
`else
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni) \
    event EV_NAME_; \
    cover property (@(posedge CLK_) disable iff (RST_ == 0) (PROP_)) begin \
      -> EV_NAME_; \
    end
`endif
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef DV_FCOV_MARK_UNUSED
  `define DV_FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef DV_FCOV_SIGNAL
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef DV_FCOV_SIGNAL_GEN_IF
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

module ibex_controller #(
    parameter bit WritebackStage  = 0,
    parameter bit BranchPredictor = 0
 ) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    output logic                  ctrl_busy_o,           // core is busy processing instrs

    // decoder related signals
    input  logic                  illegal_insn_i,          // decoder has an invalid instr
    input  logic                  ecall_insn_i,            // decoder has ECALL instr
    input  logic                  mret_insn_i,             // decoder has MRET instr
    input  logic                  dret_insn_i,             // decoder has DRET instr
    input  logic                  wfi_insn_i,              // decoder has WFI instr
    input  logic                  ebrk_insn_i,             // decoder has EBREAK instr
    input  logic                  csr_pipe_flush_i,        // do CSR-related pipeline flush

    // instr from IF-ID pipeline stage
    input  logic                  instr_valid_i,           // instr is valid
    input  logic [31:0]           instr_i,                 // uncompressed instr data for mtval
    input  logic [15:0]           instr_compressed_i,      // instr compressed data for mtval
    input  logic                  instr_is_compressed_i,   // instr is compressed
    input  logic                  instr_bp_taken_i,        // instr was predicted taken branch
    input  logic                  instr_fetch_err_i,       // instr has error
    input  logic                  instr_fetch_err_plus2_i, // instr error is x32
    input  logic [31:0]           pc_id_i,                 // instr address

    // to IF-ID pipeline stage
    output logic                  instr_valid_clear_o,     // kill instr in IF-ID reg
    output logic                  id_in_ready_o,           // ID stage is ready for new instr
    output logic                  controller_run_o,        // Controller is in standard instruction
                                                           // run mode

    // to prefetcher
    output logic                  instr_req_o,             // start fetching instructions
    output logic                  pc_set_o,                // jump to address set by pc_mux
    output logic                  pc_set_spec_o,           // speculative branch
    output ibex_pkg::pc_sel_e     pc_mux_o,                // IF stage fetch address selector
                                                           // (boot, normal, exception...)
    output logic                  nt_branch_mispredict_o,  // Not-taken branch in ID/EX was
                                                           // mispredicted (predicted taken)
    output ibex_pkg::exc_pc_sel_e exc_pc_mux_o,            // IF stage selector for exception PC
    output ibex_pkg::exc_cause_e  exc_cause_o,             // for IF stage, CSRs

    // LSU
    input  logic [31:0]           lsu_addr_last_i,         // for mtval
    input  logic                  load_err_i,
    input  logic                  store_err_i,
    output logic                  wb_exception_o,          // Instruction in WB taking an exception

    // jump/branch signals
    input  logic                  branch_set_i,            // branch set signal (branch definitely
                                                           // taken)
    input  logic                  branch_set_spec_i,       // speculative branch signal (branch
                                                           // may be taken)
    input  logic                  branch_not_set_i,        // branch is definitely not taken
    input  logic                  jump_set_i,              // jump taken set signal

    // interrupt signals
    input  logic                  csr_mstatus_mie_i,       // M-mode interrupt enable bit
    input  logic                  irq_pending_i,           // interrupt request pending
    input  ibex_pkg::irqs_t       irqs_i,                  // interrupt requests qualified with
                                                           // mie CSR
    input  logic                  irq_nm_i,                // non-maskeable interrupt
    output logic                  nmi_mode_o,              // core executing NMI handler

    // debug signals
    input  logic                  debug_req_i,
    output ibex_pkg::dbg_cause_e  debug_cause_o,
    output logic                  debug_csr_save_o,
    output logic                  debug_mode_o,
    input  logic                  debug_single_step_i,
    input  logic                  debug_ebreakm_i,
    input  logic                  debug_ebreaku_i,
    input  logic                  trigger_match_i,

    output logic                  csr_save_if_o,
    output logic                  csr_save_id_o,
    output logic                  csr_save_wb_o,
    output logic                  csr_restore_mret_id_o,
    output logic                  csr_restore_dret_id_o,
    output logic                  csr_save_cause_o,
    output logic [31:0]           csr_mtval_o,
    input  ibex_pkg::priv_lvl_e   priv_mode_i,
    input  logic                  csr_mstatus_tw_i,

    // stall & flush signals
    input  logic                  stall_id_i,
    input  logic                  stall_wb_i,
    output logic                  flush_id_o,
    input  logic                  ready_wb_i,

    // performance monitors
    output logic                  perf_jump_o,             // we are executing a jump
                                                           // instruction (j, jr, jal, jalr)
    output logic                  perf_tbranch_o           // we are executing a taken branch
                                                           // instruction
);
  import ibex_pkg::*;

  // FSM state encoding
  typedef enum logic [3:0] {
    RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
    IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID
  } ctrl_fsm_e;

  ctrl_fsm_e ctrl_fsm_cs, ctrl_fsm_ns;

  logic nmi_mode_q, nmi_mode_d;
  logic debug_mode_q, debug_mode_d;
  logic load_err_q, load_err_d;
  logic store_err_q, store_err_d;
  logic exc_req_q, exc_req_d;
  logic illegal_insn_q, illegal_insn_d;

  // Of the various exception/fault signals, which one takes priority in FLUSH and hence controls
  // what happens next (setting exc_cause, csr_mtval etc)
  logic instr_fetch_err_prio;
  logic illegal_insn_prio;
  logic ecall_insn_prio;
  logic ebrk_insn_prio;
  logic store_err_prio;
  logic load_err_prio;

  logic stall;
  logic halt_if;
  logic retain_id;
  logic flush_id;
  logic illegal_dret;
  logic illegal_umode;
  logic exc_req_lsu;
  logic special_req;
  logic special_req_pc_change;
  logic special_req_flush_only;
  logic do_single_step_d;
  logic do_single_step_q;
  logic enter_debug_mode_prio_d;
  logic enter_debug_mode_prio_q;
  logic enter_debug_mode;
  logic ebreak_into_debug;
  logic handle_irq;
  logic id_wb_pending;

  logic [3:0] mfip_id;
  logic       unused_irq_timer;

  logic ecall_insn;
  logic mret_insn;
  logic dret_insn;
  logic wfi_insn;
  logic ebrk_insn;
  logic csr_pipe_flush;
  logic instr_fetch_err;

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk_i) begin
    // print warning in case of decoding errors
    if ((ctrl_fsm_cs == DECODE) && instr_valid_i && !instr_fetch_err_i && illegal_insn_d) begin
      $display("%t: Illegal instruction (hart %0x) at PC 0x%h: 0x%h", $time, ibex_core.hart_id_i,
               ibex_id_stage.pc_id_i, ibex_id_stage.instr_rdata_i);
    end
  end
  // synopsys translate_on
`endif

  ////////////////
  // Exceptions //
  ////////////////

  assign load_err_d  = load_err_i;
  assign store_err_d = store_err_i;

  // Decoder doesn't take instr_valid into account, factor it in here.
  assign ecall_insn      = ecall_insn_i      & instr_valid_i;
  assign mret_insn       = mret_insn_i       & instr_valid_i;
  assign dret_insn       = dret_insn_i       & instr_valid_i;
  assign wfi_insn        = wfi_insn_i        & instr_valid_i;
  assign ebrk_insn       = ebrk_insn_i       & instr_valid_i;
  assign csr_pipe_flush  = csr_pipe_flush_i  & instr_valid_i;
  assign instr_fetch_err = instr_fetch_err_i & instr_valid_i;

  // "Executing DRET outside of Debug Mode causes an illegal instruction exception."
  // [Debug Spec v0.13.2, p.41]
  assign illegal_dret = dret_insn & ~debug_mode_q;

  // Some instructions can only be executed in M-Mode
  assign illegal_umode = (priv_mode_i != PRIV_LVL_M) &
                         // MRET must be in M-Mode. TW means trap WFI to M-Mode.
                         (mret_insn | (csr_mstatus_tw_i & wfi_insn));

  // This is recorded in the illegal_insn_q flop to help timing.  Specifically
  // it is needed to break the path from ibex_cs_registers/illegal_csr_insn_o
  // to pc_set_o.  Clear when controller is in FLUSH so it won't remain set
  // once illegal instruction is handled.
  // All terms in this expression are qualified by instr_valid_i
  assign illegal_insn_d = (illegal_insn_i | illegal_dret | illegal_umode) & (ctrl_fsm_cs != FLUSH);

  // exception requests
  // requests are flopped in exc_req_q.  This is cleared when controller is in
  // the FLUSH state so the cycle following exc_req_q won't remain set for an
  // exception request that has just been handled.
  // All terms in this expression are qualified by instr_valid_i
  assign exc_req_d = (ecall_insn | ebrk_insn | illegal_insn_d | instr_fetch_err) &
                     (ctrl_fsm_cs != FLUSH);

  // LSU exception requests
  assign exc_req_lsu = store_err_i | load_err_i;


  // special requests: special instructions, pipeline flushes, exceptions...
  // All terms in these expressions are qualified by instr_valid_i except exc_req_lsu which can come
  // from the Writeback stage with no instr_valid_i from the ID stage

  // These special requests only cause a pipeline flush and in particular don't cause a PC change
  // that is outside the normal execution flow
  assign special_req_flush_only = wfi_insn | csr_pipe_flush;

  // These special requests cause a change in PC
  assign special_req_pc_change = mret_insn | dret_insn | exc_req_d | exc_req_lsu;

  // generic special request signal, applies to all instructions
  assign special_req = special_req_pc_change | special_req_flush_only;

  // Is there an instruction in ID or WB that has yet to complete?
  assign id_wb_pending = instr_valid_i | ~ready_wb_i;

  // Exception/fault prioritisation is taken from Table 3.7 of Priviledged Spec v1.11
  if (WritebackStage) begin : g_wb_exceptions
    always_comb begin
      instr_fetch_err_prio = 0;
      illegal_insn_prio    = 0;
      ecall_insn_prio      = 0;
      ebrk_insn_prio       = 0;
      store_err_prio       = 0;
      load_err_prio        = 0;

      // Note that with the writeback stage store/load errors occur on the instruction in writeback,
      // all other exception/faults occur on the instruction in ID/EX. The faults from writeback
      // must take priority as that instruction is architecurally ordered before the one in ID/EX.
      if (store_err_q) begin
        store_err_prio = 1'b1;
      end else if (load_err_q) begin
        load_err_prio  = 1'b1;
      end else if (instr_fetch_err) begin
        instr_fetch_err_prio = 1'b1;
      end else if (illegal_insn_q) begin
        illegal_insn_prio = 1'b1;
      end else if (ecall_insn) begin
        ecall_insn_prio = 1'b1;
      end else if (ebrk_insn) begin
        ebrk_insn_prio = 1'b1;
      end
    end

    // Instruction in writeback is generating an exception so instruction in ID must not execute
    assign wb_exception_o = load_err_q | store_err_q | load_err_i | store_err_i;
  end else begin : g_no_wb_exceptions
    always_comb begin
      instr_fetch_err_prio = 0;
      illegal_insn_prio    = 0;
      ecall_insn_prio      = 0;
      ebrk_insn_prio       = 0;
      store_err_prio       = 0;
      load_err_prio        = 0;

      if (instr_fetch_err) begin
        instr_fetch_err_prio = 1'b1;
      end else if (illegal_insn_q) begin
        illegal_insn_prio = 1'b1;
      end else if (ecall_insn) begin
        ecall_insn_prio = 1'b1;
      end else if (ebrk_insn) begin
        ebrk_insn_prio = 1'b1;
      end else if (store_err_q) begin
        store_err_prio = 1'b1;
      end else if (load_err_q) begin
        load_err_prio  = 1'b1;
      end
    end
    assign wb_exception_o = 1'b0;
  end

  `ASSERT_IF(IbexExceptionPrioOnehot,
             $onehot({instr_fetch_err_prio,
                      illegal_insn_prio,
                      ecall_insn_prio,
                      ebrk_insn_prio,
                      store_err_prio,
                      load_err_prio}),
             (ctrl_fsm_cs == FLUSH) & exc_req_q)

  ////////////////
  // Interrupts //
  ////////////////

  // Enter debug mode due to an external debug_req_i or because the core is in
  // single step mode (dcsr.step == 1). Single step must be qualified with
  // instruction valid otherwise the core will immediately enter debug mode
  // due to a recently flushed IF (or a delay in an instruction returning from
  // memory) before it has had anything to single step.
  // Also enter debug mode on a trigger match (hardware breakpoint)

  // Set `do_single_step_q` when a valid instruction is seen outside of debug mode and core is in
  // single step mode. The first valid instruction on debug mode entry will clear it. Hold its value
  // when there is no valid instruction so `do_single_step_d` remains asserted until debug mode is
  // entered.
  assign do_single_step_d = instr_valid_i ? ~debug_mode_q & debug_single_step_i : do_single_step_q;
  // Enter debug mode due to:
  // * external `debug_req_i`
  // * core in single step mode (dcsr.step == 1).
  // * trigger match (hardware breakpoint)
  //
  // `debug_req_i` and `do_single_step_d` request debug mode with priority. This results in a debug
  // mode entry even if the controller goes to `FLUSH` in preparation for handling an exception or
  // interrupt. `trigger_match_i` is not a priority entry into debug mode as it must be ignored
  // where control flow changes such that the instruction causing the trigger is no longer being
  // executed.
  assign enter_debug_mode_prio_d = (debug_req_i | do_single_step_d) & ~debug_mode_q;
  assign enter_debug_mode = enter_debug_mode_prio_d | (trigger_match_i & ~debug_mode_q);

  // Set when an ebreak should enter debug mode rather than jump to exception
  // handler
  assign ebreak_into_debug = priv_mode_i == PRIV_LVL_M ? debug_ebreakm_i :
                             priv_mode_i == PRIV_LVL_U ? debug_ebreaku_i :
                                                         1'b0;

  // Interrupts including NMI are ignored,
  // - while in debug mode [Debug Spec v0.13.2, p.39],
  // - while in NMI mode (nested NMIs are not supported, NMI has highest priority and
  //   cannot be interrupted by regular interrupts).
  assign handle_irq = ~debug_mode_q & ~nmi_mode_q &
      (irq_nm_i | (irq_pending_i & csr_mstatus_mie_i));

  // generate ID of fast interrupts, highest priority to highest ID
  always_comb begin : gen_mfip_id
    if      (irqs_i.irq_fast[14]) mfip_id = 4'd14;
    else if (irqs_i.irq_fast[13]) mfip_id = 4'd13;
    else if (irqs_i.irq_fast[12]) mfip_id = 4'd12;
    else if (irqs_i.irq_fast[11]) mfip_id = 4'd11;
    else if (irqs_i.irq_fast[10]) mfip_id = 4'd10;
    else if (irqs_i.irq_fast[ 9]) mfip_id = 4'd9;
    else if (irqs_i.irq_fast[ 8]) mfip_id = 4'd8;
    else if (irqs_i.irq_fast[ 7]) mfip_id = 4'd7;
    else if (irqs_i.irq_fast[ 6]) mfip_id = 4'd6;
    else if (irqs_i.irq_fast[ 5]) mfip_id = 4'd5;
    else if (irqs_i.irq_fast[ 4]) mfip_id = 4'd4;
    else if (irqs_i.irq_fast[ 3]) mfip_id = 4'd3;
    else if (irqs_i.irq_fast[ 2]) mfip_id = 4'd2;
    else if (irqs_i.irq_fast[ 1]) mfip_id = 4'd1;
    else                          mfip_id = 4'd0;
  end

  assign unused_irq_timer = irqs_i.irq_timer;

  /////////////////////
  // Core controller //
  /////////////////////

  always_comb begin
    // Default values
    instr_req_o           = 1'b1;

    csr_save_if_o         = 1'b0;
    csr_save_id_o         = 1'b0;
    csr_save_wb_o         = 1'b0;
    csr_restore_mret_id_o = 1'b0;
    csr_restore_dret_id_o = 1'b0;
    csr_save_cause_o      = 1'b0;
    csr_mtval_o           = '0;

    // The values of pc_mux and exc_pc_mux are only relevant if pc_set is set. Some of the states
    // below always set pc_mux and exc_pc_mux but only set pc_set if certain conditions are met.
    // This avoid having to factor those conditions into the pc_mux and exc_pc_mux select signals
    // helping timing.
    pc_mux_o               = PC_BOOT;
    pc_set_o               = 1'b0;
    pc_set_spec_o          = 1'b0;
    nt_branch_mispredict_o = 1'b0;

    exc_pc_mux_o           = EXC_PC_IRQ;
    exc_cause_o            = EXC_CAUSE_INSN_ADDR_MISA; // = 6'h00

    ctrl_fsm_ns            = ctrl_fsm_cs;

    ctrl_busy_o            = 1'b1;

    halt_if                = 1'b0;
    retain_id              = 1'b0;
    flush_id               = 1'b0;

    debug_csr_save_o       = 1'b0;
    debug_cause_o          = DBG_CAUSE_EBREAK;
    debug_mode_d           = debug_mode_q;
    nmi_mode_d             = nmi_mode_q;

    perf_tbranch_o         = 1'b0;
    perf_jump_o            = 1'b0;

    controller_run_o       = 1'b0;

    unique case (ctrl_fsm_cs)
      RESET: begin
        instr_req_o   = 1'b0;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;
        ctrl_fsm_ns   = BOOT_SET;
      end

      BOOT_SET: begin
        // copy boot address to instr fetch address
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;

        ctrl_fsm_ns = FIRST_FETCH;
      end

      WAIT_SLEEP: begin
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if       = 1'b1;
        flush_id      = 1'b1;
        ctrl_fsm_ns   = SLEEP;
      end

      SLEEP: begin
        // instruction in IF stage is already valid
        // we begin execution when an interrupt has arrived
        instr_req_o   = 1'b0;
        halt_if       = 1'b1;
        flush_id      = 1'b1;

        // normal execution flow
        // in debug mode or single step mode we leave immediately (wfi=nop)
        if (irq_nm_i || irq_pending_i || debug_req_i || debug_mode_q || debug_single_step_i) begin
          ctrl_fsm_ns = FIRST_FETCH;
        end else begin
          // Make sure clock remains disabled.
          ctrl_busy_o = 1'b0;
        end
      end

      FIRST_FETCH: begin
        // Stall because of IF miss
        if (id_in_ready_o) begin
          ctrl_fsm_ns = DECODE;
        end

        // handle interrupts
        if (handle_irq) begin
          // We are handling an interrupt. Set halt_if to tell IF not to give
          // us any more instructions before it redirects to the handler, but
          // don't set flush_id: we must allow this instruction to complete
          // (since it might have outstanding loads or stores).
          ctrl_fsm_ns = IRQ_TAKEN;
          halt_if     = 1'b1;
        end

        // enter debug mode
        if (enter_debug_mode) begin
          ctrl_fsm_ns = DBG_TAKEN_IF;
          // Halt IF only for now, ID will be flushed in DBG_TAKEN_IF as the
          // ID state is needed for correct debug mode entry
          halt_if     = 1'b1;
        end
      end

      DECODE: begin
        // normal operating mode of the ID stage, in case of debug and interrupt requests,
        // priorities are as follows (lower number == higher priority)
        // 1. currently running (multicycle) instructions and exceptions caused by these
        // 2. debug requests
        // 3. interrupt requests

        controller_run_o = 1'b1;

        // Set PC mux for branch and jump here to ease timing. Value is only relevant if pc_set_o is
        // also set. Setting the mux value here avoids factoring in special_req and instr_valid_i
        // which helps timing.
        pc_mux_o = PC_JUMP;


        // Get ready for special instructions, exceptions, pipeline flushes
        if (special_req) begin
          // Halt IF but don't flush ID. This leaves a valid instruction in
          // ID so controller can determine appropriate action in the
          // FLUSH state.
          retain_id = 1'b1;

          // Wait for the writeback stage to either be ready for a new instruction or raise its own
          // exception before going to FLUSH. If the instruction in writeback raises an exception it
          // must take priority over any exception from an instruction in ID/EX. Only once the
          // writeback stage is ready can we be certain that won't happen. Without a writeback
          // stage ready_wb_i == 1 so the FSM will always go directly to FLUSH.

          if (ready_wb_i | wb_exception_o) begin
            ctrl_fsm_ns = FLUSH;
          end
        end

        if (branch_set_i || jump_set_i) begin
          // Only set the PC if the branch predictor hasn't already done the branch for us
          pc_set_o       = BranchPredictor ? ~instr_bp_taken_i : 1'b1;

          perf_tbranch_o = branch_set_i;
          perf_jump_o    = jump_set_i;
        end

        if (BranchPredictor) begin
          if (instr_bp_taken_i & branch_not_set_i) begin
            // If the instruction is a branch that was predicted to be taken but was not taken
            // signal a mispredict.
            nt_branch_mispredict_o = 1'b1;
          end
        end

        // pc_set signal excluding branch taken condition
        if (branch_set_spec_i || jump_set_i) begin
          // Only speculatively set the PC if the branch predictor hasn't already done the branch
          // for us
          pc_set_spec_o = BranchPredictor ? ~instr_bp_taken_i : 1'b1;
        end

        // If entering debug mode or handling an IRQ the core needs to wait until any instruction in
        // ID or WB has finished executing. Stall IF during that time.
        if ((enter_debug_mode || handle_irq) && (stall || id_wb_pending)) begin
          halt_if = 1'b1;
        end

        if (!stall && !special_req && !id_wb_pending) begin
          if (enter_debug_mode) begin
            // enter debug mode
            ctrl_fsm_ns = DBG_TAKEN_IF;
            // Halt IF only for now, ID will be flushed in DBG_TAKEN_IF as the
            // ID state is needed for correct debug mode entry
            halt_if     = 1'b1;
          end else if (handle_irq) begin
            // handle interrupt (not in debug mode)
            ctrl_fsm_ns = IRQ_TAKEN;
            // We are handling an interrupt (not in debug mode). Set halt_if to
            // tell IF not to give us any more instructions before it redirects
            // to the handler, but don't set flush_id: we must allow this
            // instruction to complete (since it might have outstanding loads
            // or stores).
            halt_if     = 1'b1;
          end
        end

      end // DECODE

      IRQ_TAKEN: begin
        pc_mux_o     = PC_EXC;
        exc_pc_mux_o = EXC_PC_IRQ;

        if (handle_irq) begin
          pc_set_o         = 1'b1;
          pc_set_spec_o    = 1'b1;

          csr_save_if_o    = 1'b1;
          csr_save_cause_o = 1'b1;

          // interrupt priorities according to Privileged Spec v1.11 p.31
          if (irq_nm_i && !nmi_mode_q) begin
            exc_cause_o = EXC_CAUSE_IRQ_NM;
            nmi_mode_d  = 1'b1; // enter NMI mode
          end else if (irqs_i.irq_fast != 15'b0) begin
            // generate exception cause ID from fast interrupt ID:
            // - first bit distinguishes interrupts from exceptions,
            // - second bit adds 16 to fast interrupt ID
            // for example EXC_CAUSE_IRQ_FAST_0 = {1'b1, 5'd16}
            exc_cause_o = exc_cause_e'({2'b11, mfip_id});
          end else if (irqs_i.irq_external) begin
            exc_cause_o = EXC_CAUSE_IRQ_EXTERNAL_M;
          end else if (irqs_i.irq_software) begin
            exc_cause_o = EXC_CAUSE_IRQ_SOFTWARE_M;
          end else begin // irqs_i.irq_timer
            exc_cause_o = EXC_CAUSE_IRQ_TIMER_M;
          end
        end

        ctrl_fsm_ns = DECODE;
      end

      DBG_TAKEN_IF: begin
        pc_mux_o     = PC_EXC;
        exc_pc_mux_o = EXC_PC_DBD;

        // enter debug mode and save PC in IF to dpc
        // jump to debug exception handler in debug memory
        flush_id         = 1'b1;
        pc_set_o         = 1'b1;
        pc_set_spec_o    = 1'b1;

        csr_save_if_o    = 1'b1;
        debug_csr_save_o = 1'b1;

        csr_save_cause_o = 1'b1;
        if (trigger_match_i) begin
          debug_cause_o = DBG_CAUSE_TRIGGER;
        end else if (debug_single_step_i) begin
          debug_cause_o = DBG_CAUSE_STEP;
        end else begin
          debug_cause_o = DBG_CAUSE_HALTREQ;
        end

        // enter debug mode
        debug_mode_d = 1'b1;

        ctrl_fsm_ns  = DECODE;
      end

      DBG_TAKEN_ID: begin
        // enter debug mode and save PC in ID to dpc, used when encountering
        // 1. EBREAK during debug mode
        // 2. EBREAK with forced entry into debug mode (ebreakm or ebreaku set).
        // regular ebreak's go through FLUSH.
        //
        // for 1. do not update dcsr and dpc, for 2. do so [Debug Spec v0.13.2, p.39]
        // jump to debug exception handler in debug memory
        flush_id      = 1'b1;
        pc_mux_o      = PC_EXC;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;
        exc_pc_mux_o  = EXC_PC_DBD;

        // update dcsr and dpc
        if (ebreak_into_debug && !debug_mode_q) begin // ebreak with forced entry

          // dpc (set to the address of the EBREAK, i.e. set to PC in ID stage)
          csr_save_cause_o = 1'b1;
          csr_save_id_o    = 1'b1;

          // dcsr
          debug_csr_save_o = 1'b1;
          debug_cause_o    = DBG_CAUSE_EBREAK;
        end

        // enter debug mode
        debug_mode_d = 1'b1;

        ctrl_fsm_ns  = DECODE;
      end

      FLUSH: begin
        // flush the pipeline
        halt_if     = 1'b1;
        flush_id    = 1'b1;
        ctrl_fsm_ns = DECODE;

        // As pc_mux and exc_pc_mux can take various values in this state they aren't set early
        // here.

        // exceptions: set exception PC, save PC and exception cause
        // exc_req_lsu is high for one clock cycle only (in DECODE)
        if (exc_req_q || store_err_q || load_err_q) begin
          pc_set_o         = 1'b1;
          pc_set_spec_o    = 1'b1;
          pc_mux_o         = PC_EXC;
          exc_pc_mux_o     = debug_mode_q ? EXC_PC_DBG_EXC : EXC_PC_EXC;

          if (WritebackStage) begin : g_writeback_mepc_save
            // With the writeback stage present whether an instruction accessing memory will cause
            // an exception is only known when it is in writeback. So when taking such an exception
            // epc must come from writeback.
            csr_save_id_o  = ~(store_err_q | load_err_q);
            csr_save_wb_o  = store_err_q | load_err_q;
          end else begin : g_no_writeback_mepc_save
            csr_save_id_o  = 1'b0;
          end

          csr_save_cause_o = 1'b1;

          // Exception/fault prioritisation logic will have set exactly 1 X_prio signal
          unique case (1'b1)
            instr_fetch_err_prio: begin
                exc_cause_o = EXC_CAUSE_INSTR_ACCESS_FAULT;
                csr_mtval_o = instr_fetch_err_plus2_i ? (pc_id_i + 32'd2) : pc_id_i;
            end
            illegal_insn_prio: begin
              exc_cause_o = EXC_CAUSE_ILLEGAL_INSN;
              csr_mtval_o = instr_is_compressed_i ? {16'b0, instr_compressed_i} : instr_i;
            end
            ecall_insn_prio: begin
              exc_cause_o = (priv_mode_i == PRIV_LVL_M) ? EXC_CAUSE_ECALL_MMODE :
                                                          EXC_CAUSE_ECALL_UMODE;
            end
            ebrk_insn_prio: begin
              if (debug_mode_q | ebreak_into_debug) begin
                /*
                 * EBREAK in debug mode re-enters debug mode
                 *
                 * "The only exception is EBREAK. When that is executed in Debug
                 * Mode, it halts the hart again but without updating dpc or
                 * dcsr." [Debug Spec v0.13.2, p.39]
                 */

                /*
                 * dcsr.ebreakm == 1:
                 * "EBREAK instructions in M-mode enter Debug Mode."
                 * [Debug Spec v0.13.2, p.42]
                 */
                pc_set_o         = 1'b0;
                pc_set_spec_o    = 1'b0;
                csr_save_id_o    = 1'b0;
                csr_save_cause_o = 1'b0;
                ctrl_fsm_ns      = DBG_TAKEN_ID;
                flush_id         = 1'b0;
              end else begin
                /*
                 * "The EBREAK instruction is used by debuggers to cause control
                 * to be transferred back to a debugging environment. It
                 * generates a breakpoint exception and performs no other
                 * operation. [...] ECALL and EBREAK cause the receiving
                 * privilege mode's epc register to be set to the address of the
                 * ECALL or EBREAK instruction itself, not the address of the
                 * following instruction." [Privileged Spec v1.11, p.40]
                 */
                exc_cause_o      = EXC_CAUSE_BREAKPOINT;
              end
            end
            store_err_prio: begin
              exc_cause_o = EXC_CAUSE_STORE_ACCESS_FAULT;
              csr_mtval_o = lsu_addr_last_i;
            end
            load_err_prio: begin
              exc_cause_o = EXC_CAUSE_LOAD_ACCESS_FAULT;
              csr_mtval_o = lsu_addr_last_i;
            end
            default: ;
          endcase
        end else begin
          // special instructions and pipeline flushes
          if (mret_insn) begin
            pc_mux_o              = PC_ERET;
            pc_set_o              = 1'b1;
            pc_set_spec_o         = 1'b1;
            csr_restore_mret_id_o = 1'b1;
            if (nmi_mode_q) begin
              nmi_mode_d          = 1'b0; // exit NMI mode
            end
          end else if (dret_insn) begin
            pc_mux_o              = PC_DRET;
            pc_set_o              = 1'b1;
            pc_set_spec_o         = 1'b1;
            debug_mode_d          = 1'b0;
            csr_restore_dret_id_o = 1'b1;
          end else if (wfi_insn) begin
            ctrl_fsm_ns           = WAIT_SLEEP;
          end else if (csr_pipe_flush && handle_irq) begin
            // start handling IRQs when doing CSR-related pipeline flushes
            ctrl_fsm_ns           = IRQ_TAKEN;
          end
        end // exc_req_q

        // Entering debug mode due to either single step or debug_req. Ensure
        // registers are set for exception but then enter debug handler rather
        // than exception handler [Debug Spec v0.13.2, p.44]
        // Leave all other signals as is to ensure CSRs and PC get set as if
        // core was entering exception handler, entry to debug mode will then
        // see the appropriate state and setup dpc correctly.
        // If an EBREAK instruction is causing us to enter debug mode on the
        // same cycle as a debug_req or single step, honor the EBREAK and
        // proceed to DBG_TAKEN_ID.
        if (enter_debug_mode_prio_q && !(ebrk_insn_prio && ebreak_into_debug)) begin
          ctrl_fsm_ns = DBG_TAKEN_IF;
        end
      end // FLUSH

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  assign flush_id_o = flush_id;

  // signal to CSR when in debug mode
  assign debug_mode_o = debug_mode_q;

  // signal to CSR when in an NMI handler (for nested exception handling)
  assign nmi_mode_o = nmi_mode_q;

  ///////////////////
  // Stall control //
  ///////////////////

  // If high current instruction cannot complete this cycle. Either because it needs more cycles to
  // finish (stall_id_i) or because the writeback stage cannot accept it yet (stall_wb_i). If there
  // is no writeback stage stall_wb_i is a constant 0.
  assign stall = stall_id_i | stall_wb_i;

  // signal to IF stage that ID stage is ready for next instr
  assign id_in_ready_o = ~stall & ~halt_if & ~retain_id;

  // kill instr in IF-ID pipeline reg that are done, or if a
  // multicycle instr causes an exception for example
  // retain_id is another kind of stall, where the instr_valid bit must remain
  // set (unless flush_id is set also). It cannot be factored directly into
  // stall as this causes a combinational loop.
  assign instr_valid_clear_o = ~(stall | retain_id) | flush_id;

  // update registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : update_regs
    if (!rst_ni) begin
      ctrl_fsm_cs             <= RESET;
      nmi_mode_q              <= 1'b0;
      do_single_step_q        <= 1'b0;
      debug_mode_q            <= 1'b0;
      enter_debug_mode_prio_q <= 1'b0;
      load_err_q              <= 1'b0;
      store_err_q             <= 1'b0;
      exc_req_q               <= 1'b0;
      illegal_insn_q          <= 1'b0;
    end else begin
      ctrl_fsm_cs             <= ctrl_fsm_ns;
      nmi_mode_q              <= nmi_mode_d;
      do_single_step_q        <= do_single_step_d;
      debug_mode_q            <= debug_mode_d;
      enter_debug_mode_prio_q <= enter_debug_mode_prio_d;
      load_err_q              <= load_err_d;
      store_err_q             <= store_err_d;
      exc_req_q               <= exc_req_d;
      illegal_insn_q          <= illegal_insn_d;
    end
  end

  //////////
  // FCOV //
  //////////

  `DV_FCOV_SIGNAL(logic, interrupt_taken, (ctrl_fsm_cs != IRQ_TAKEN) & (ctrl_fsm_ns == IRQ_TAKEN))
  `DV_FCOV_SIGNAL(logic, debug_entry_if,
      (ctrl_fsm_cs != DBG_TAKEN_IF) & (ctrl_fsm_ns == DBG_TAKEN_IF))
  `DV_FCOV_SIGNAL(logic, debug_entry_id,
      (ctrl_fsm_cs != DBG_TAKEN_ID) & (ctrl_fsm_ns == DBG_TAKEN_ID))
  `DV_FCOV_SIGNAL(logic, pipe_flush, (ctrl_fsm_cs != FLUSH) & (ctrl_fsm_ns == FLUSH))
  `DV_FCOV_SIGNAL(logic, debug_req, debug_req_i & ~debug_mode_q)

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(AlwaysInstrClearOnMispredict, nt_branch_mispredict_o |-> instr_valid_clear_o)

  // Selectors must be known/valid.
  `ASSERT(IbexCtrlStateValid, ctrl_fsm_cs inside {
      RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
      IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID})

  // The speculative branch signal should be set whenever the actual branch signal is set
  `ASSERT(IbexSpecImpliesSetPC, pc_set_o |-> pc_set_spec_o)

  `ifdef INC_ASSERT
    // If something that causes a jump into an exception handler is seen that jump must occur before
    // the next instruction executes. The logic tracks whether a jump into an exception handler is
    // expected. Assertions check the jump occurs.

    logic exception_req, exception_req_pending, exception_req_accepted, exception_req_done;
    logic exception_pc_set, seen_exception_pc_set, expect_exception_pc_set;
    logic exception_req_needs_pc_set;

    assign exception_req = (special_req | enter_debug_mode | handle_irq);
    // Any exception rquest will cause a transition out of DECODE, once the controller transitions
    // back into DECODE we're done handling the request.
    assign exception_req_done =
      exception_req_pending & (ctrl_fsm_cs != DECODE) & (ctrl_fsm_ns == DECODE);

    assign exception_req_needs_pc_set = enter_debug_mode | handle_irq | special_req_pc_change;

    // An exception PC set uses specific PC types
    assign exception_pc_set =
      exception_req_pending & (pc_set_o & (pc_mux_o inside {PC_EXC, PC_ERET, PC_DRET}));

    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        exception_req_pending   <= 1'b0;
        exception_req_accepted  <= 1'b0;
        expect_exception_pc_set <= 1'b0;
        seen_exception_pc_set   <= 1'b0;
      end else begin
        // Keep `exception_req_pending` asserted once an exception_req is seen until it is done
        exception_req_pending <= (exception_req_pending | exception_req) & ~exception_req_done;

        // The exception req has been accepted once the controller transitions out of decode
        exception_req_accepted <= (exception_req_accepted & ~exception_req_done) |
          (exception_req & ctrl_fsm_ns != DECODE);

        // Set `expect_exception_pc_set` if exception req needs one and keep it asserted until
        // exception req is done
        expect_exception_pc_set <= (expect_exception_pc_set | exception_req_needs_pc_set) &
          ~exception_req_done;

        // Keep `seen_exception_pc_set` asserted once an exception PC set is seen until the
        // exception req is done
        seen_exception_pc_set <= (seen_exception_pc_set | exception_pc_set) & ~exception_req_done;
      end
    end

    // Once an exception request has been accepted it must be handled before controller goes back to
    // DECODE
    `ASSERT(IbexNoDoubleExceptionReq, exception_req_accepted |-> ctrl_fsm_cs != DECODE)

    // Only signal ready, allowing a new instruction into ID, if there is no exception request
    // pending or it is done this cycle.
    `ASSERT(IbexDontSkipExceptionReq,
      id_in_ready_o |-> !exception_req_pending || exception_req_done)

    // Once a PC set has been performed for an exception request there must not be any other
    // excepting those to move into debug mode.
    `ASSERT(IbexNoDoubleSpecialReqPCSet,
      seen_exception_pc_set &&
        !((ctrl_fsm_cs inside {DBG_TAKEN_IF, DBG_TAKEN_ID}) &&
          (pc_mux_o == PC_EXC) && (exc_pc_mux_o == EXC_PC_DBD))
      |-> !pc_set_o)

    // When an exception request is done there must have been an appropriate PC set (either this
    // cycle or a previous one).
    `ASSERT(IbexSetExceptionPCOnSpecialReqIfExpected,
      exception_req_pending && expect_exception_pc_set && exception_req_done |->
      seen_exception_pc_set || exception_pc_set)

    // If there's a pending exception req that doesn't need a PC set we must not see one
    `ASSERT(IbexNoPCSetOnSpecialReqIfNotExpected,
      exception_req_pending && !expect_exception_pc_set |-> ~pc_set_o)
  `endif
endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core import ibex_pkg::*; #(
    parameter bit          PMPEnable         = 1'b0,
    parameter int unsigned PMPGranularity    = 0,
    parameter int unsigned PMPNumRegions     = 4,
    parameter int unsigned MHPMCounterNum    = 0,
    parameter int unsigned MHPMCounterWidth  = 40,
    parameter bit          RV32E             = 1'b0,
    parameter rv32m_e      RV32M             = RV32MFast,
    parameter rv32b_e      RV32B             = RV32BNone,
    parameter bit          BranchTargetALU   = 1'b0,
    parameter bit          WritebackStage    = 1'b0,
    parameter bit          ICache            = 1'b0,
    parameter bit          ICacheECC         = 1'b0,
    parameter int unsigned BusSizeECC        = BUS_SIZE,
    parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
    parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
    parameter bit          BranchPredictor   = 1'b0,
    parameter bit          DbgTriggerEn      = 1'b0,
    parameter int unsigned DbgHwBreakNum     = 1,
    parameter bit          ResetAll          = 1'b0,
    parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
    parameter bit          SecureIbex        = 1'b0,
    parameter bit          DummyInstructions = 1'b0,
    parameter bit          RegFileECC        = 1'b0,
    parameter int unsigned RegFileDataWidth  = 32,
    parameter int unsigned DmHaltAddr        = 32'h1A110800,
    parameter int unsigned DmExceptionAddr   = 32'h1A110808
) (
    // Clock and Reset
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    // Instruction memory interface
    output logic                         instr_req_o,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    output logic [31:0]                  instr_addr_o,
    input  logic [31:0]                  instr_rdata_i,
    input  logic                         instr_err_i,

    // Data memory interface
    output logic                         data_req_o,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    output logic                         data_we_o,
    output logic [3:0]                   data_be_o,
    output logic [31:0]                  data_addr_o,
    output logic [31:0]                  data_wdata_o,
    input  logic [31:0]                  data_rdata_i,
    input  logic                         data_err_i,

    // Register file interface
    output logic                         dummy_instr_id_o,
    output logic [4:0]                   rf_raddr_a_o,
    output logic [4:0]                   rf_raddr_b_o,
    output logic [4:0]                   rf_waddr_wb_o,
    output logic                         rf_we_wb_o,
    output logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_o,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

    // RAMs interface
    output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
    output logic                         ic_tag_write_o,
    output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
    output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
    input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
    output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
    output logic                         ic_data_write_o,
    output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
    output logic [LineSizeECC-1:0]       ic_data_wdata_o,
    input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],

    // Interrupt inputs
    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,       // non-maskeable interrupt
    output logic                         irq_pending_o,

    // Debug Interface
    input  logic                         debug_req_i,
    output crash_dump_t                  crash_dump_o,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic                         rvfi_valid,
    output logic [63:0]                  rvfi_order,
    output logic [31:0]                  rvfi_insn,
    output logic                         rvfi_trap,
    output logic                         rvfi_halt,
    output logic                         rvfi_intr,
    output logic [ 1:0]                  rvfi_mode,
    output logic [ 1:0]                  rvfi_ixl,
    output logic [ 4:0]                  rvfi_rs1_addr,
    output logic [ 4:0]                  rvfi_rs2_addr,
    output logic [ 4:0]                  rvfi_rs3_addr,
    output logic [31:0]                  rvfi_rs1_rdata,
    output logic [31:0]                  rvfi_rs2_rdata,
    output logic [31:0]                  rvfi_rs3_rdata,
    output logic [ 4:0]                  rvfi_rd_addr,
    output logic [31:0]                  rvfi_rd_wdata,
    output logic [31:0]                  rvfi_pc_rdata,
    output logic [31:0]                  rvfi_pc_wdata,
    output logic [31:0]                  rvfi_mem_addr,
    output logic [ 3:0]                  rvfi_mem_rmask,
    output logic [ 3:0]                  rvfi_mem_wmask,
    output logic [31:0]                  rvfi_mem_rdata,
    output logic [31:0]                  rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic                         fetch_enable_i,
    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    output logic                         core_busy_o
);

  localparam int unsigned PMP_NUM_CHAN      = 2;
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          PCIncrCheck       = SecureIbex;
  localparam bit          ShadowCSR         = 1'b0;
  // Speculative branch option, trades-off performance against timing.
  // Setting this to 1 eases branch target critical paths significantly but reduces performance
  // by ~3% (based on CoreMark/MHz score).
  // Set by default in the max PMP config which has the tightest budget for branch target timing.
  localparam bit          SpecBranch        = PMPEnable & (PMPNumRegions == 16);

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to
                                               // ease fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_perf_count_id;
  logic        instr_bp_taken_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex[2];                // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex[2];                // Intermediate register for multicycle Ops
  logic [1:0]  imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;
  logic        pc_mismatch_alert;
  logic        csr_shadow_err;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        pc_set_spec;
  logic        nt_branch_mispredict;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_e  exc_cause;                      // Exception cause

  logic        lsu_load_err;
  logic        lsu_store_err;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic        rf_ren_a;
  logic        rf_ren_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;
  logic        rf_ecc_err_comb;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;
  logic        rf_rd_a_wb_match;
  logic        rf_rd_b_wb_match;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;
  logic        lsu_resp_err;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface
  logic        instr_req_gated;

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;

  // Interrupts
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0]  csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t     csr_pmp_cfg  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg;
  logic         pmp_req_err  [PMP_NUM_CHAN];
  logic         instr_req_out;
  logic         data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_if;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_done_wb;

  logic        perf_instr_ret_wb;
  logic        perf_instr_ret_compressed_wb;
  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  // RISC-V Formal Interface signals
`ifdef RVFI
  logic        rvfi_instr_new_wb;
  logic        rvfi_intr_d;
  logic        rvfi_intr_q;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs1_addr_q;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [4:0]  rvfi_rs2_addr_q;
  logic [4:0]  rvfi_rs3_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_q;
  logic [31:0] rvfi_rs3_data_d;
  logic [4:0]  rvfi_rd_addr_wb;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_wb;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_wb;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
`endif

  //////////////////////
  // Clock management //
  //////////////////////

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
  assign core_busy_o = ctrl_busy | if_busy | lsu_busy;

  //////////////
  // IF stage //
  //////////////

  ibex_if_stage #(
      .DmHaltAddr        ( DmHaltAddr        ),
      .DmExceptionAddr   ( DmExceptionAddr   ),
      .DummyInstructions ( DummyInstructions ),
      .ICache            ( ICache            ),
      .ICacheECC         ( ICacheECC         ),
      .BusSizeECC        ( BusSizeECC        ),
      .TagSizeECC        ( TagSizeECC        ),
      .LineSizeECC       ( LineSizeECC       ),
      .PCIncrCheck       ( PCIncrCheck       ),
      .ResetAll          ( ResetAll          ),
      .RndCnstLfsrSeed   ( RndCnstLfsrSeed   ),
      .RndCnstLfsrPerm   ( RndCnstLfsrPerm   ),
      .BranchPredictor   ( BranchPredictor   )
  ) if_stage_i (
      .clk_i                    ( clk_i                  ),
      .rst_ni                   ( rst_ni                 ),

      .boot_addr_i              ( boot_addr_i            ),
      .req_i                    ( instr_req_gated        ), // instruction request control

      // instruction cache interface
      .instr_req_o              ( instr_req_out          ),
      .instr_addr_o             ( instr_addr_o           ),
      .instr_gnt_i              ( instr_gnt_i            ),
      .instr_rvalid_i           ( instr_rvalid_i         ),
      .instr_rdata_i            ( instr_rdata_i          ),
      .instr_err_i              ( instr_err_i            ),
      .instr_pmp_err_i          ( pmp_req_err[PMP_I]     ),

      .ic_tag_req_o             ( ic_tag_req_o           ),
      .ic_tag_write_o           ( ic_tag_write_o         ),
      .ic_tag_addr_o            ( ic_tag_addr_o          ),
      .ic_tag_wdata_o           ( ic_tag_wdata_o         ),
      .ic_tag_rdata_i           ( ic_tag_rdata_i         ),
      .ic_data_req_o            ( ic_data_req_o          ),
      .ic_data_write_o          ( ic_data_write_o        ),
      .ic_data_addr_o           ( ic_data_addr_o         ),
      .ic_data_wdata_o          ( ic_data_wdata_o        ),
      .ic_data_rdata_i          ( ic_data_rdata_i        ),

      // outputs to ID stage
      .instr_valid_id_o         ( instr_valid_id         ),
      .instr_new_id_o           ( instr_new_id           ),
      .instr_rdata_id_o         ( instr_rdata_id         ),
      .instr_rdata_alu_id_o     ( instr_rdata_alu_id     ),
      .instr_rdata_c_id_o       ( instr_rdata_c_id       ),
      .instr_is_compressed_id_o ( instr_is_compressed_id ),
      .instr_bp_taken_o         ( instr_bp_taken_id      ),
      .instr_fetch_err_o        ( instr_fetch_err        ),
      .instr_fetch_err_plus2_o  ( instr_fetch_err_plus2  ),
      .illegal_c_insn_id_o      ( illegal_c_insn_id      ),
      .dummy_instr_id_o         ( dummy_instr_id         ),
      .pc_if_o                  ( pc_if                  ),
      .pc_id_o                  ( pc_id                  ),

      // control signals
      .instr_valid_clear_i      ( instr_valid_clear      ),
      .pc_set_i                 ( pc_set                 ),
      .pc_set_spec_i            ( pc_set_spec            ),
      .pc_mux_i                 ( pc_mux_id              ),
      .nt_branch_mispredict_i   ( nt_branch_mispredict   ),
      .exc_pc_mux_i             ( exc_pc_mux_id          ),
      .exc_cause                ( exc_cause              ),
      .dummy_instr_en_i         ( dummy_instr_en         ),
      .dummy_instr_mask_i       ( dummy_instr_mask       ),
      .dummy_instr_seed_en_i    ( dummy_instr_seed_en    ),
      .dummy_instr_seed_i       ( dummy_instr_seed       ),
      .icache_enable_i          ( icache_enable          ),
      .icache_inval_i           ( icache_inval           ),

      // branch targets
      .branch_target_ex_i       ( branch_target_ex       ),

      // CSRs
      .csr_mepc_i               ( csr_mepc               ), // exception return address
      .csr_depc_i               ( csr_depc               ), // debug return address
      .csr_mtvec_i              ( csr_mtvec              ), // trap-vector base address
      .csr_mtvec_init_o         ( csr_mtvec_init         ),

      // pipeline stalls
      .id_in_ready_i            ( id_in_ready            ),

      .pc_mismatch_alert_o      ( pc_mismatch_alert      ),
      .if_busy_o                ( if_busy                )
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;

  // Qualify the instruction request with PMP error
  assign instr_req_o = instr_req_out & ~pmp_req_err[PMP_I];

  // fetch_enable_i can be used to stop the core fetching new instructions
  assign instr_req_gated = instr_req_int & fetch_enable_i;

  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
      .RV32E           ( RV32E           ),
      .RV32M           ( RV32M           ),
      .RV32B           ( RV32B           ),
      .BranchTargetALU ( BranchTargetALU ),
      .DataIndTiming   ( DataIndTiming   ),
      .SpecBranch      ( SpecBranch      ),
      .WritebackStage  ( WritebackStage  ),
      .BranchPredictor ( BranchPredictor )
  ) id_stage_i (
      .clk_i                        ( clk_i                    ),
      .rst_ni                       ( rst_ni                   ),

      // Processor Enable
      .ctrl_busy_o                  ( ctrl_busy                ),
      .illegal_insn_o               ( illegal_insn_id          ),

      // from/to IF-ID pipeline register
      .instr_valid_i                ( instr_valid_id           ),
      .instr_rdata_i                ( instr_rdata_id           ),
      .instr_rdata_alu_i            ( instr_rdata_alu_id       ),
      .instr_rdata_c_i              ( instr_rdata_c_id         ),
      .instr_is_compressed_i        ( instr_is_compressed_id   ),
      .instr_bp_taken_i             ( instr_bp_taken_id        ),

      // Jumps and branches
      .branch_decision_i            ( branch_decision          ),

      // IF and ID control signals
      .instr_first_cycle_id_o       ( instr_first_cycle_id     ),
      .instr_valid_clear_o          ( instr_valid_clear        ),
      .id_in_ready_o                ( id_in_ready              ),
      .instr_req_o                  ( instr_req_int            ),
      .pc_set_o                     ( pc_set                   ),
      .pc_set_spec_o                ( pc_set_spec              ),
      .pc_mux_o                     ( pc_mux_id                ),
      .nt_branch_mispredict_o       ( nt_branch_mispredict     ),
      .exc_pc_mux_o                 ( exc_pc_mux_id            ),
      .exc_cause_o                  ( exc_cause                ),
      .icache_inval_o               ( icache_inval             ),

      .instr_fetch_err_i            ( instr_fetch_err          ),
      .instr_fetch_err_plus2_i      ( instr_fetch_err_plus2    ),
      .illegal_c_insn_i             ( illegal_c_insn_id        ),

      .pc_id_i                      ( pc_id                    ),

      // Stalls
      .ex_valid_i                   ( ex_valid                 ),
      .lsu_resp_valid_i             ( lsu_resp_valid           ),

      .alu_operator_ex_o            ( alu_operator_ex          ),
      .alu_operand_a_ex_o           ( alu_operand_a_ex         ),
      .alu_operand_b_ex_o           ( alu_operand_b_ex         ),

      .imd_val_q_ex_o               ( imd_val_q_ex             ),
      .imd_val_d_ex_i               ( imd_val_d_ex             ),
      .imd_val_we_ex_i              ( imd_val_we_ex            ),

      .bt_a_operand_o               ( bt_a_operand             ),
      .bt_b_operand_o               ( bt_b_operand             ),

      .mult_en_ex_o                 ( mult_en_ex               ),
      .div_en_ex_o                  ( div_en_ex                ),
      .mult_sel_ex_o                ( mult_sel_ex              ),
      .div_sel_ex_o                 ( div_sel_ex               ),
      .multdiv_operator_ex_o        ( multdiv_operator_ex      ),
      .multdiv_signed_mode_ex_o     ( multdiv_signed_mode_ex   ),
      .multdiv_operand_a_ex_o       ( multdiv_operand_a_ex     ),
      .multdiv_operand_b_ex_o       ( multdiv_operand_b_ex     ),
      .multdiv_ready_id_o           ( multdiv_ready_id         ),

      // CSR ID/EX
      .csr_access_o                 ( csr_access               ),
      .csr_op_o                     ( csr_op                   ),
      .csr_op_en_o                  ( csr_op_en                ),
      .csr_save_if_o                ( csr_save_if              ), // control signal to save PC
      .csr_save_id_o                ( csr_save_id              ), // control signal to save PC
      .csr_save_wb_o                ( csr_save_wb              ), // control signal to save PC
      .csr_restore_mret_id_o        ( csr_restore_mret_id      ), // restore mstatus upon MRET
      .csr_restore_dret_id_o        ( csr_restore_dret_id      ), // restore mstatus upon MRET
      .csr_save_cause_o             ( csr_save_cause           ),
      .csr_mtval_o                  ( csr_mtval                ),
      .priv_mode_i                  ( priv_mode_id             ),
      .csr_mstatus_tw_i             ( csr_mstatus_tw           ),
      .illegal_csr_insn_i           ( illegal_csr_insn_id      ),
      .data_ind_timing_i            ( data_ind_timing          ),

      // LSU
      .lsu_req_o                    ( lsu_req                  ), // to load store unit
      .lsu_we_o                     ( lsu_we                   ), // to load store unit
      .lsu_type_o                   ( lsu_type                 ), // to load store unit
      .lsu_sign_ext_o               ( lsu_sign_ext             ), // to load store unit
      .lsu_wdata_o                  ( lsu_wdata                ), // to load store unit
      .lsu_req_done_i               ( lsu_req_done             ), // from load store unit

      .lsu_addr_incr_req_i          ( lsu_addr_incr_req        ),
      .lsu_addr_last_i              ( lsu_addr_last            ),

      .lsu_load_err_i               ( lsu_load_err             ),
      .lsu_store_err_i              ( lsu_store_err            ),

      // Interrupt Signals
      .csr_mstatus_mie_i            ( csr_mstatus_mie          ),
      .irq_pending_i                ( irq_pending_o            ),
      .irqs_i                       ( irqs                     ),
      .irq_nm_i                     ( irq_nm_i                 ),
      .nmi_mode_o                   ( nmi_mode                 ),

      // Debug Signal
      .debug_mode_o                 ( debug_mode               ),
      .debug_cause_o                ( debug_cause              ),
      .debug_csr_save_o             ( debug_csr_save           ),
      .debug_req_i                  ( debug_req_i              ),
      .debug_single_step_i          ( debug_single_step        ),
      .debug_ebreakm_i              ( debug_ebreakm            ),
      .debug_ebreaku_i              ( debug_ebreaku            ),
      .trigger_match_i              ( trigger_match            ),

      // write data to commit in the register file
      .result_ex_i                  ( result_ex                ),
      .csr_rdata_i                  ( csr_rdata                ),

      .rf_raddr_a_o                 ( rf_raddr_a               ),
      .rf_rdata_a_i                 ( rf_rdata_a               ),
      .rf_raddr_b_o                 ( rf_raddr_b               ),
      .rf_rdata_b_i                 ( rf_rdata_b               ),
      .rf_ren_a_o                   ( rf_ren_a                 ),
      .rf_ren_b_o                   ( rf_ren_b                 ),
      .rf_waddr_id_o                ( rf_waddr_id              ),
      .rf_wdata_id_o                ( rf_wdata_id              ),
      .rf_we_id_o                   ( rf_we_id                 ),
      .rf_rd_a_wb_match_o           ( rf_rd_a_wb_match         ),
      .rf_rd_b_wb_match_o           ( rf_rd_b_wb_match         ),

      .rf_waddr_wb_i                ( rf_waddr_wb              ),
      .rf_wdata_fwd_wb_i            ( rf_wdata_fwd_wb          ),
      .rf_write_wb_i                ( rf_write_wb              ),

      .en_wb_o                      ( en_wb                    ),
      .instr_type_wb_o              ( instr_type_wb            ),
      .instr_perf_count_id_o        ( instr_perf_count_id      ),
      .ready_wb_i                   ( ready_wb                 ),
      .outstanding_load_wb_i        ( outstanding_load_wb      ),
      .outstanding_store_wb_i       ( outstanding_store_wb     ),

      // Performance Counters
      .perf_jump_o                  ( perf_jump                ),
      .perf_branch_o                ( perf_branch              ),
      .perf_tbranch_o               ( perf_tbranch             ),
      .perf_dside_wait_o            ( perf_dside_wait          ),
      .perf_mul_wait_o              ( perf_mul_wait            ),
      .perf_div_wait_o              ( perf_div_wait            ),
      .instr_id_done_o              ( instr_id_done            )
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ibex_ex_block #(
      .RV32M                    ( RV32M                    ),
      .RV32B                    ( RV32B                    ),
      .BranchTargetALU          ( BranchTargetALU          )
  ) ex_block_i (
      .clk_i                    ( clk_i                    ),
      .rst_ni                   ( rst_ni                   ),

      // ALU signal from ID stage
      .alu_operator_i           ( alu_operator_ex          ),
      .alu_operand_a_i          ( alu_operand_a_ex         ),
      .alu_operand_b_i          ( alu_operand_b_ex         ),
      .alu_instr_first_cycle_i  ( instr_first_cycle_id     ),

      // Branch target ALU signal from ID stage
      .bt_a_operand_i           ( bt_a_operand             ),
      .bt_b_operand_i           ( bt_b_operand             ),

      // Multipler/Divider signal from ID stage
      .multdiv_operator_i       ( multdiv_operator_ex      ),
      .mult_en_i                ( mult_en_ex               ),
      .div_en_i                 ( div_en_ex                ),
      .mult_sel_i               ( mult_sel_ex              ),
      .div_sel_i                ( div_sel_ex               ),
      .multdiv_signed_mode_i    ( multdiv_signed_mode_ex   ),
      .multdiv_operand_a_i      ( multdiv_operand_a_ex     ),
      .multdiv_operand_b_i      ( multdiv_operand_b_ex     ),
      .multdiv_ready_id_i       ( multdiv_ready_id         ),
      .data_ind_timing_i        ( data_ind_timing          ),

      // Intermediate value register
      .imd_val_we_o             ( imd_val_we_ex            ),
      .imd_val_d_o              ( imd_val_d_ex             ),
      .imd_val_q_i              ( imd_val_q_ex             ),

      // Outputs
      .alu_adder_result_ex_o    ( alu_adder_result_ex      ), // to LSU
      .result_ex_o              ( result_ex                ), // to ID

      .branch_target_o          ( branch_target_ex         ), // to IF
      .branch_decision_o        ( branch_decision          ), // to ID

      .ex_valid_o               ( ex_valid                 )
  );

  /////////////////////
  // Load/store unit //
  /////////////////////

  assign data_req_o   = data_req_out & ~pmp_req_err[PMP_D];
  assign lsu_resp_err = lsu_load_err | lsu_store_err;

  ibex_load_store_unit load_store_unit_i (
      .clk_i                 ( clk_i               ),
      .rst_ni                ( rst_ni              ),

      // data interface
      .data_req_o            ( data_req_out        ),
      .data_gnt_i            ( data_gnt_i          ),
      .data_rvalid_i         ( data_rvalid_i       ),
      .data_err_i            ( data_err_i          ),
      .data_pmp_err_i        ( pmp_req_err[PMP_D]  ),

      .data_addr_o           ( data_addr_o         ),
      .data_we_o             ( data_we_o           ),
      .data_be_o             ( data_be_o           ),
      .data_wdata_o          ( data_wdata_o        ),
      .data_rdata_i          ( data_rdata_i        ),

      // signals to/from ID/EX stage
      .lsu_we_i              ( lsu_we              ),
      .lsu_type_i            ( lsu_type            ),
      .lsu_wdata_i           ( lsu_wdata           ),
      .lsu_sign_ext_i        ( lsu_sign_ext        ),

      .lsu_rdata_o           ( rf_wdata_lsu        ),
      .lsu_rdata_valid_o     ( rf_we_lsu           ),
      .lsu_req_i             ( lsu_req             ),
      .lsu_req_done_o        ( lsu_req_done        ),

      .adder_result_ex_i     ( alu_adder_result_ex ),

      .addr_incr_req_o       ( lsu_addr_incr_req   ),
      .addr_last_o           ( lsu_addr_last       ),


      .lsu_resp_valid_o      ( lsu_resp_valid      ),

      // exception signals
      .load_err_o            ( lsu_load_err        ),
      .store_err_o           ( lsu_store_err       ),

      .busy_o                ( lsu_busy            ),

      .perf_load_o           ( perf_load           ),
      .perf_store_o          ( perf_store          )
  );

  ibex_wb_stage #(
    .ResetAll       ( ResetAll       ),
    .WritebackStage ( WritebackStage )
  ) wb_stage_i (
    .clk_i                          ( clk_i                        ),
    .rst_ni                         ( rst_ni                       ),
    .en_wb_i                        ( en_wb                        ),
    .instr_type_wb_i                ( instr_type_wb                ),
    .pc_id_i                        ( pc_id                        ),
    .instr_is_compressed_id_i       ( instr_is_compressed_id       ),
    .instr_perf_count_id_i          ( instr_perf_count_id          ),

    .ready_wb_o                     ( ready_wb                     ),
    .rf_write_wb_o                  ( rf_write_wb                  ),
    .outstanding_load_wb_o          ( outstanding_load_wb          ),
    .outstanding_store_wb_o         ( outstanding_store_wb         ),
    .pc_wb_o                        ( pc_wb                        ),
    .perf_instr_ret_wb_o            ( perf_instr_ret_wb            ),
    .perf_instr_ret_compressed_wb_o ( perf_instr_ret_compressed_wb ),

    .rf_waddr_id_i                  ( rf_waddr_id                  ),
    .rf_wdata_id_i                  ( rf_wdata_id                  ),
    .rf_we_id_i                     ( rf_we_id                     ),

    .rf_wdata_lsu_i                 ( rf_wdata_lsu                 ),
    .rf_we_lsu_i                    ( rf_we_lsu                    ),

    .rf_wdata_fwd_wb_o              ( rf_wdata_fwd_wb              ),

    .rf_waddr_wb_o                  ( rf_waddr_wb                  ),
    .rf_wdata_wb_o                  ( rf_wdata_wb                  ),
    .rf_we_wb_o                     ( rf_we_wb                     ),

    .lsu_resp_valid_i               ( lsu_resp_valid               ),
    .lsu_resp_err_i                 ( lsu_resp_err                 ),

    .instr_done_wb_o                ( instr_done_wb                )
  );

  /////////////////////////////
  // Register file interface //
  /////////////////////////////

  assign dummy_instr_id_o = dummy_instr_id;
  assign rf_raddr_a_o     = rf_raddr_a;
  assign rf_waddr_wb_o    = rf_waddr_wb;
  assign rf_we_wb_o       = rf_we_wb;
  assign rf_raddr_b_o     = rf_raddr_b;

  if (RegFileECC) begin : gen_regfile_ecc

    logic [1:0] rf_ecc_err_a, rf_ecc_err_b;
    logic       rf_ecc_err_a_id, rf_ecc_err_b_id;

    // ECC checkbit generation for regiter file wdata
    prim_secded_39_32_enc regfile_ecc_enc (
      .data_i (rf_wdata_wb),
      .data_o (rf_wdata_wb_ecc_o)
    );

    // ECC checking on register file rdata
    prim_secded_39_32_dec regfile_ecc_dec_a (
      .data_i     (rf_rdata_a_ecc_i),
      .data_o     (),
      .syndrome_o (),
      .err_o      (rf_ecc_err_a)
    );
    prim_secded_39_32_dec regfile_ecc_dec_b (
      .data_i     (rf_rdata_b_ecc_i),
      .data_o     (),
      .syndrome_o (),
      .err_o      (rf_ecc_err_b)
    );

    // Assign read outputs - no error correction, just trigger an alert
    assign rf_rdata_a = rf_rdata_a_ecc_i[31:0];
    assign rf_rdata_b = rf_rdata_b_ecc_i[31:0];

    // Calculate errors - qualify with WB forwarding to avoid xprop into the alert signal
    assign rf_ecc_err_a_id = |rf_ecc_err_a & rf_ren_a & ~rf_rd_a_wb_match;
    assign rf_ecc_err_b_id = |rf_ecc_err_b & rf_ren_b & ~rf_rd_b_wb_match;

    // Combined error
    assign rf_ecc_err_comb = instr_valid_id & (rf_ecc_err_a_id | rf_ecc_err_b_id);

  end else begin : gen_no_regfile_ecc
    logic unused_rf_ren_a, unused_rf_ren_b;
    logic unused_rf_rd_a_wb_match, unused_rf_rd_b_wb_match;

    assign unused_rf_ren_a         = rf_ren_a;
    assign unused_rf_ren_b         = rf_ren_b;
    assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
    assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
    assign rf_wdata_wb_ecc_o       = rf_wdata_wb;
    assign rf_rdata_a              = rf_rdata_a_ecc_i;
    assign rf_rdata_b              = rf_rdata_b_ecc_i;
    assign rf_ecc_err_comb         = 1'b0;
  end

  ///////////////////////
  // Crash dump output //
  ///////////////////////

  assign crash_dump_o.current_pc     = pc_id;
  assign crash_dump_o.next_pc        = pc_if;
  assign crash_dump_o.last_data_addr = lsu_addr_last;
  assign crash_dump_o.exception_addr = csr_mepc;

  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  // TODO add I$ ECC errors here
  assign alert_minor_o = 1'b0;

  // Major alert - core is unrecoverable
  assign alert_major_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;

  // Explict INC_ASSERT block to avoid unused signal lint warnings were asserts are not included
  `ifdef INC_ASSERT
  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;

  assign outstanding_load_id  = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                ~id_stage_i.lsu_we;
  assign outstanding_store_id = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                id_stage_i.lsu_we;

  if (WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & load_store_unit_i.split_misaligned_access);

    assign outstanding_store_resp = outstanding_store_wb |
      (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_wb, clk_i, !rst_ni)
  end else begin : gen_no_wb_stage
    // Without writeback stage only look into whether load or store is in ID to determine if
    // a response is expected.
    assign outstanding_load_resp  = outstanding_load_id;
    assign outstanding_store_resp = outstanding_store_id;

    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_id, clk_i, !rst_ni)
  end

  `ASSERT(NoMemResponseWithoutPendingAccess,
    data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp, clk_i, !rst_ni)
  `endif

  ////////////////////////
  // RF (Register File) //
  ////////////////////////
`ifdef RVFI
  assign rvfi_rd_addr_wb  = rf_waddr_wb;
  assign rvfi_rd_wdata_wb = rf_we_wb ? rf_wdata_wb : rf_wdata_lsu;
  assign rvfi_rd_we_wb    = rf_we_wb | rf_we_lsu;
`endif


  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;
  assign csr_addr   = csr_num_e'(csr_access ? alu_operand_b_ex[11:0] : 12'b0);

  ibex_cs_registers #(
      .DbgTriggerEn      ( DbgTriggerEn      ),
      .DbgHwBreakNum     ( DbgHwBreakNum     ),
      .DataIndTiming     ( DataIndTiming     ),
      .DummyInstructions ( DummyInstructions ),
      .ShadowCSR         ( ShadowCSR         ),
      .ICache            ( ICache            ),
      .MHPMCounterNum    ( MHPMCounterNum    ),
      .MHPMCounterWidth  ( MHPMCounterWidth  ),
      .PMPEnable         ( PMPEnable         ),
      .PMPGranularity    ( PMPGranularity    ),
      .PMPNumRegions     ( PMPNumRegions     ),
      .RV32E             ( RV32E             ),
      .RV32M             ( RV32M             ),
      .RV32B             ( RV32B             )
  ) cs_registers_i (
      .clk_i                   ( clk_i                        ),
      .rst_ni                  ( rst_ni                       ),

      // Hart ID from outside
      .hart_id_i               ( hart_id_i                    ),
      .priv_mode_id_o          ( priv_mode_id                 ),
      .priv_mode_if_o          ( priv_mode_if                 ),
      .priv_mode_lsu_o         ( priv_mode_lsu                ),

      // mtvec
      .csr_mtvec_o             ( csr_mtvec                    ),
      .csr_mtvec_init_i        ( csr_mtvec_init               ),
      .boot_addr_i             ( boot_addr_i                  ),

      // Interface to CSRs     ( SRAM like                    )
      .csr_access_i            ( csr_access                   ),
      .csr_addr_i              ( csr_addr                     ),
      .csr_wdata_i             ( csr_wdata                    ),
      .csr_op_i                ( csr_op                       ),
      .csr_op_en_i             ( csr_op_en                    ),
      .csr_rdata_o             ( csr_rdata                    ),

      // Interrupt related control signals
      .irq_software_i          ( irq_software_i               ),
      .irq_timer_i             ( irq_timer_i                  ),
      .irq_external_i          ( irq_external_i               ),
      .irq_fast_i              ( irq_fast_i                   ),
      .nmi_mode_i              ( nmi_mode                     ),
      .irq_pending_o           ( irq_pending_o                ),
      .irqs_o                  ( irqs                         ),
      .csr_mstatus_mie_o       ( csr_mstatus_mie              ),
      .csr_mstatus_tw_o        ( csr_mstatus_tw               ),
      .csr_mepc_o              ( csr_mepc                     ),

      // PMP
      .csr_pmp_cfg_o           ( csr_pmp_cfg                  ),
      .csr_pmp_addr_o          ( csr_pmp_addr                 ),
      .csr_pmp_mseccfg_o       ( csr_pmp_mseccfg              ),

      // debug
      .csr_depc_o              ( csr_depc                     ),
      .debug_mode_i            ( debug_mode                   ),
      .debug_cause_i           ( debug_cause                  ),
      .debug_csr_save_i        ( debug_csr_save               ),
      .debug_single_step_o     ( debug_single_step            ),
      .debug_ebreakm_o         ( debug_ebreakm                ),
      .debug_ebreaku_o         ( debug_ebreaku                ),
      .trigger_match_o         ( trigger_match                ),

      .pc_if_i                 ( pc_if                        ),
      .pc_id_i                 ( pc_id                        ),
      .pc_wb_i                 ( pc_wb                        ),

      .data_ind_timing_o       ( data_ind_timing              ),
      .dummy_instr_en_o        ( dummy_instr_en               ),
      .dummy_instr_mask_o      ( dummy_instr_mask             ),
      .dummy_instr_seed_en_o   ( dummy_instr_seed_en          ),
      .dummy_instr_seed_o      ( dummy_instr_seed             ),
      .icache_enable_o         ( icache_enable                ),
      .csr_shadow_err_o        ( csr_shadow_err               ),

      .csr_save_if_i           ( csr_save_if                  ),
      .csr_save_id_i           ( csr_save_id                  ),
      .csr_save_wb_i           ( csr_save_wb                  ),
      .csr_restore_mret_i      ( csr_restore_mret_id          ),
      .csr_restore_dret_i      ( csr_restore_dret_id          ),
      .csr_save_cause_i        ( csr_save_cause               ),
      .csr_mcause_i            ( exc_cause                    ),
      .csr_mtval_i             ( csr_mtval                    ),
      .illegal_csr_insn_o      ( illegal_csr_insn_id          ),

      // performance counter related signals
      .instr_ret_i             ( perf_instr_ret_wb            ),
      .instr_ret_compressed_i  ( perf_instr_ret_compressed_wb ),
      .iside_wait_i            ( perf_iside_wait              ),
      .jump_i                  ( perf_jump                    ),
      .branch_i                ( perf_branch                  ),
      .branch_taken_i          ( perf_tbranch                 ),
      .mem_load_i              ( perf_load                    ),
      .mem_store_i             ( perf_store                   ),
      .dside_wait_i            ( perf_dside_wait              ),
      .mul_wait_i              ( perf_mul_wait                ),
      .div_wait_i              ( perf_div_wait                )
  );

  // These assertions are in top-level as instr_valid_id required as the enable term
  `ASSERT(IbexCsrOpValid, instr_valid_id |-> csr_op inside {
      CSR_OP_READ,
      CSR_OP_WRITE,
      CSR_OP_SET,
      CSR_OP_CLEAR
      })
  `ASSERT_KNOWN_IF(IbexCsrWdataIntKnown, cs_registers_i.csr_wdata_int, csr_op_en)

  if (PMPEnable) begin : g_pmp
    logic [33:0] pmp_req_addr [PMP_NUM_CHAN];
    pmp_req_e    pmp_req_type [PMP_NUM_CHAN];
    priv_lvl_e   pmp_priv_lvl [PMP_NUM_CHAN];

    assign pmp_req_addr[PMP_I] = {2'b00,instr_addr_o[31:0]};
    assign pmp_req_type[PMP_I] = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I] = priv_mode_if;
    assign pmp_req_addr[PMP_D] = {2'b00,data_addr_o[31:0]};
    assign pmp_req_type[PMP_D] = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
    assign pmp_priv_lvl[PMP_D] = priv_mode_lsu;

    ibex_pmp #(
        .PMPGranularity        ( PMPGranularity  ),
        .PMPNumChan            ( PMP_NUM_CHAN    ),
        .PMPNumRegions         ( PMPNumRegions   )
    ) pmp_i (
        .clk_i                 ( clk_i           ),
        .rst_ni                ( rst_ni          ),
        // Interface to CSRs
        .csr_pmp_cfg_i         ( csr_pmp_cfg     ),
        .csr_pmp_addr_i        ( csr_pmp_addr    ),
        .csr_pmp_mseccfg_i     ( csr_pmp_mseccfg ),
        .priv_mode_i           ( pmp_priv_lvl    ),
        // Access checking channels
        .pmp_req_addr_i        ( pmp_req_addr    ),
        .pmp_req_type_i        ( pmp_req_type    ),
        .pmp_req_err_o         ( pmp_req_err     )
    );
  end else begin : g_no_pmp
    // Unused signal tieoff
    priv_lvl_e unused_priv_lvl_if, unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    pmp_mseccfg_t unused_csr_pmp_mseccfg;
    assign unused_priv_lvl_if = priv_mode_if;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;
    assign unused_csr_pmp_mseccfg = csr_pmp_mseccfg;

    // Output tieoff
    assign pmp_req_err[PMP_I] = 1'b0;
    assign pmp_req_err[PMP_D] = 1'b0;
  end

`ifdef RVFI
  // When writeback stage is present RVFI information is emitted when instruction is finished in
  // third stage but some information must be captured whilst the instruction is in the second
  // stage. Without writeback stage RVFI information is all emitted when instruction retires in
  // second stage. RVFI outputs are all straight from flops. So 2 stage pipeline requires a single
  // set of flops (instr_info => RVFI_out), 3 stage pipeline requires two sets (instr_info => wb
  // => RVFI_out)
  localparam int RVFI_STAGES = WritebackStage ? 2 : 1;

  logic        rvfi_stage_valid     [RVFI_STAGES];
  logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  logic        rvfi_stage_trap      [RVFI_STAGES];
  logic        rvfi_stage_halt      [RVFI_STAGES];
  logic        rvfi_stage_intr      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];

  logic        rvfi_stage_valid_d   [RVFI_STAGES];

  assign rvfi_valid     = rvfi_stage_valid    [RVFI_STAGES-1];
  assign rvfi_order     = rvfi_stage_order    [RVFI_STAGES-1];
  assign rvfi_insn      = rvfi_stage_insn     [RVFI_STAGES-1];
  assign rvfi_trap      = rvfi_stage_trap     [RVFI_STAGES-1];
  assign rvfi_halt      = rvfi_stage_halt     [RVFI_STAGES-1];
  assign rvfi_intr      = rvfi_stage_intr     [RVFI_STAGES-1];
  assign rvfi_mode      = rvfi_stage_mode     [RVFI_STAGES-1];
  assign rvfi_ixl       = rvfi_stage_ixl      [RVFI_STAGES-1];
  assign rvfi_rs1_addr  = rvfi_stage_rs1_addr [RVFI_STAGES-1];
  assign rvfi_rs2_addr  = rvfi_stage_rs2_addr [RVFI_STAGES-1];
  assign rvfi_rs3_addr  = rvfi_stage_rs3_addr [RVFI_STAGES-1];
  assign rvfi_rs1_rdata = rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  assign rvfi_rs2_rdata = rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  assign rvfi_rs3_rdata = rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  assign rvfi_rd_addr   = rvfi_stage_rd_addr  [RVFI_STAGES-1];
  assign rvfi_rd_wdata  = rvfi_stage_rd_wdata [RVFI_STAGES-1];
  assign rvfi_pc_rdata  = rvfi_stage_pc_rdata [RVFI_STAGES-1];
  assign rvfi_pc_wdata  = rvfi_stage_pc_wdata [RVFI_STAGES-1];
  assign rvfi_mem_addr  = rvfi_stage_mem_addr [RVFI_STAGES-1];
  assign rvfi_mem_rmask = rvfi_stage_mem_rmask[RVFI_STAGES-1];
  assign rvfi_mem_wmask = rvfi_stage_mem_wmask[RVFI_STAGES-1];
  assign rvfi_mem_rdata = rvfi_stage_mem_rdata[RVFI_STAGES-1];
  assign rvfi_mem_wdata = rvfi_stage_mem_wdata[RVFI_STAGES-1];

  if (WritebackStage) begin : gen_rvfi_wb_stage
    logic unused_instr_new_id;

    assign unused_instr_new_id = instr_new_id;

    // With writeback stage first RVFI stage buffers instruction information captured in ID/EX
    // awaiting instruction retirement and RF Write data/Mem read data whilst instruction is in WB
    // So first stage becomes valid when instruction leaves ID/EX stage and remains valid until
    // instruction leaves WB
    assign rvfi_stage_valid_d[0] = (instr_id_done & ~dummy_instr_id) |
                                   (rvfi_stage_valid[0] & ~instr_done_wb);
    // Second stage is output stage so simple valid cycle after instruction leaves WB (and so has
    // retired)
    assign rvfi_stage_valid_d[1] = instr_done_wb;

    // Signal new instruction in WB cycle after instruction leaves ID/EX (to enter WB)
    logic rvfi_instr_new_wb_q;

    assign rvfi_instr_new_wb = rvfi_instr_new_wb_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) begin
        rvfi_instr_new_wb_q <= 0;
      end else begin
        rvfi_instr_new_wb_q <= instr_id_done;
      end
    end
  end else begin : gen_rvfi_no_wb_stage
    // Without writeback stage first RVFI stage is output stage so simply valid the cycle after
    // instruction leaves ID/EX (and so has retired)
    assign rvfi_stage_valid_d[0] = instr_id_done & ~dummy_instr_id;
    // Without writeback stage signal new instr_new_wb when instruction enters ID/EX to correctly
    // setup register write signals
    assign rvfi_instr_new_wb = instr_new_id;
  end

  for (genvar i = 0;i < RVFI_STAGES; i = i + 1) begin : g_rvfi_stages
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_stage_halt[i]      <= '0;
        rvfi_stage_trap[i]      <= '0;
        rvfi_stage_intr[i]      <= '0;
        rvfi_stage_order[i]     <= '0;
        rvfi_stage_insn[i]      <= '0;
        rvfi_stage_mode[i]      <= {PRIV_LVL_M};
        rvfi_stage_ixl[i]       <= CSR_MISA_MXL;
        rvfi_stage_rs1_addr[i]  <= '0;
        rvfi_stage_rs2_addr[i]  <= '0;
        rvfi_stage_rs3_addr[i]  <= '0;
        rvfi_stage_pc_rdata[i]  <= '0;
        rvfi_stage_pc_wdata[i]  <= '0;
        rvfi_stage_mem_rmask[i] <= '0;
        rvfi_stage_mem_wmask[i] <= '0;
        rvfi_stage_valid[i]     <= '0;
        rvfi_stage_rs1_rdata[i] <= '0;
        rvfi_stage_rs2_rdata[i] <= '0;
        rvfi_stage_rs3_rdata[i] <= '0;
        rvfi_stage_rd_wdata[i]  <= '0;
        rvfi_stage_rd_addr[i]   <= '0;
        rvfi_stage_mem_rdata[i] <= '0;
        rvfi_stage_mem_wdata[i] <= '0;
        rvfi_stage_mem_addr[i]  <= '0;
      end else begin
        rvfi_stage_valid[i] <= rvfi_stage_valid_d[i];

        if (i == 0) begin
          if(instr_id_done) begin
            rvfi_stage_halt[i]      <= '0;
            rvfi_stage_trap[i]      <= illegal_insn_id;
            rvfi_stage_intr[i]      <= rvfi_intr_d;
            rvfi_stage_order[i]     <= rvfi_stage_order[i] + 64'(rvfi_stage_valid_d[i]);
            rvfi_stage_insn[i]      <= rvfi_insn_id;
            rvfi_stage_mode[i]      <= {priv_mode_id};
            rvfi_stage_ixl[i]       <= CSR_MISA_MXL;
            rvfi_stage_rs1_addr[i]  <= rvfi_rs1_addr_d;
            rvfi_stage_rs2_addr[i]  <= rvfi_rs2_addr_d;
            rvfi_stage_rs3_addr[i]  <= rvfi_rs3_addr_d;
            rvfi_stage_pc_rdata[i]  <= pc_id;
            rvfi_stage_pc_wdata[i]  <= pc_set ? branch_target_ex : pc_if;
            rvfi_stage_mem_rmask[i] <= rvfi_mem_mask_int;
            rvfi_stage_mem_wmask[i] <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
            rvfi_stage_rs1_rdata[i] <= rvfi_rs1_data_d;
            rvfi_stage_rs2_rdata[i] <= rvfi_rs2_data_d;
            rvfi_stage_rs3_rdata[i] <= rvfi_rs3_data_d;
            rvfi_stage_rd_addr[i]   <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]  <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i] <= rvfi_mem_rdata_d;
            rvfi_stage_mem_wdata[i] <= rvfi_mem_wdata_d;
            rvfi_stage_mem_addr[i]  <= rvfi_mem_addr_d;
          end
        end else begin
          if(instr_done_wb) begin
            rvfi_stage_halt[i]      <= rvfi_stage_halt[i-1];
            rvfi_stage_trap[i]      <= rvfi_stage_trap[i-1];
            rvfi_stage_intr[i]      <= rvfi_stage_intr[i-1];
            rvfi_stage_order[i]     <= rvfi_stage_order[i-1];
            rvfi_stage_insn[i]      <= rvfi_stage_insn[i-1];
            rvfi_stage_mode[i]      <= rvfi_stage_mode[i-1];
            rvfi_stage_ixl[i]       <= rvfi_stage_ixl[i-1];
            rvfi_stage_rs1_addr[i]  <= rvfi_stage_rs1_addr[i-1];
            rvfi_stage_rs2_addr[i]  <= rvfi_stage_rs2_addr[i-1];
            rvfi_stage_rs3_addr[i]  <= rvfi_stage_rs3_addr[i-1];
            rvfi_stage_pc_rdata[i]  <= rvfi_stage_pc_rdata[i-1];
            rvfi_stage_pc_wdata[i]  <= rvfi_stage_pc_wdata[i-1];
            rvfi_stage_mem_rmask[i] <= rvfi_stage_mem_rmask[i-1];
            rvfi_stage_mem_wmask[i] <= rvfi_stage_mem_wmask[i-1];
            rvfi_stage_rs1_rdata[i] <= rvfi_stage_rs1_rdata[i-1];
            rvfi_stage_rs2_rdata[i] <= rvfi_stage_rs2_rdata[i-1];
            rvfi_stage_rs3_rdata[i] <= rvfi_stage_rs3_rdata[i-1];
            rvfi_stage_mem_wdata[i] <= rvfi_stage_mem_wdata[i-1];
            rvfi_stage_mem_addr[i]  <= rvfi_stage_mem_addr[i-1];

            // For 2 RVFI_STAGES/Writeback Stage ignore first stage flops for rd_addr, rd_wdata and
            // mem_rdata. For RF write addr/data actual write happens in writeback so capture
            // address/data there. For mem_rdata that is only available from the writeback stage.
            // Previous stage flops still exist in RTL as they are used by the non writeback config
            rvfi_stage_rd_addr[i]   <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]  <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i] <= rvfi_mem_rdata_d;
          end
        end
      end
    end
  end


  // Memory adddress/write data available first cycle of ld/st instruction from register read
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_wdata_d = lsu_wdata;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end

  // Capture read data from LSU when it becomes valid
  always_comb begin
    if (lsu_resp_valid) begin
      rvfi_mem_rdata_d = rf_wdata_lsu;
    end else begin
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_mem_addr_q  <= '0;
      rvfi_mem_rdata_q <= '0;
      rvfi_mem_wdata_q <= '0;
    end else begin
      rvfi_mem_addr_q  <= rvfi_mem_addr_d;
      rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
      rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
    end
  end
  // Byte enable based on data type
  always_comb begin
    unique case (lsu_type)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  always_comb begin
    if (instr_is_compressed_id) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id};
    end else begin
      rvfi_insn_id = instr_rdata_id;
    end
  end

  // Source registers 1 and 2 are read in the first instruction cycle
  // Source register 3 is read in the second instruction cycle.
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_rs1_data_d = rf_ren_a ? multdiv_operand_a_ex : '0;
      rvfi_rs1_addr_d = rf_ren_a ? rf_raddr_a : '0;
      rvfi_rs2_data_d = rf_ren_b ? multdiv_operand_b_ex : '0;
      rvfi_rs2_addr_d = rf_ren_b ? rf_raddr_b : '0;
      rvfi_rs3_data_d = '0;
      rvfi_rs3_addr_d = '0;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs1_addr_d = rvfi_rs1_addr_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
      rvfi_rs2_addr_d = rvfi_rs2_addr_q;
      rvfi_rs3_data_d = multdiv_operand_a_ex;
      rvfi_rs3_addr_d = rf_raddr_a;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rs1_data_q <= '0;
      rvfi_rs1_addr_q <= '0;
      rvfi_rs2_data_q <= '0;
      rvfi_rs2_addr_q <= '0;

    end else begin
      rvfi_rs1_data_q <= rvfi_rs1_data_d;
      rvfi_rs1_addr_q <= rvfi_rs1_addr_d;
      rvfi_rs2_data_q <= rvfi_rs2_data_d;
      rvfi_rs2_addr_q <= rvfi_rs2_addr_d;
    end
  end

  always_comb begin
    if(rvfi_rd_we_wb) begin
      // Capture address/data of write to register file
      rvfi_rd_addr_d  = rvfi_rd_addr_wb;
      // If writing to x0 zero write data as required by RVFI specification
      if(rvfi_rd_addr_wb == 5'b0) begin
        rvfi_rd_wdata_d = '0;
      end else begin
        rvfi_rd_wdata_d = rvfi_rd_wdata_wb;
      end
    end else if(rvfi_instr_new_wb) begin
      // If no RF write but new instruction in Writeback (when present) or ID/EX (when no writeback
      // stage present) then zero RF write address/data as required by RVFI specification
      rvfi_rd_addr_d  = '0;
      rvfi_rd_wdata_d = '0;
    end else begin
      // Otherwise maintain previous value
      rvfi_rd_addr_d  = rvfi_rd_addr_q;
      rvfi_rd_wdata_d = rvfi_rd_wdata_q;
    end
  end

  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rd_addr_q    <= '0;
      rvfi_rd_wdata_q   <= '0;
    end else begin
      rvfi_rd_addr_q    <= rvfi_rd_addr_d;
      rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
    end
  end

  // rvfi_intr must be set for first instruction that is part of a trap handler.
  // On the first cycle of a new instruction see if a trap PC was set by the previous instruction,
  // otherwise maintain value.
  assign rvfi_intr_d = instr_first_cycle_id ? rvfi_set_trap_pc_q : rvfi_intr_q;

  always_comb begin
    rvfi_set_trap_pc_d = rvfi_set_trap_pc_q;

    if (pc_set && pc_mux_id == PC_EXC &&
        (exc_pc_mux_id == EXC_PC_EXC || exc_pc_mux_id == EXC_PC_IRQ)) begin
      // PC is set to enter a trap handler
      rvfi_set_trap_pc_d = 1'b1;
    end else if (rvfi_set_trap_pc_q && instr_id_done) begin
      // first instruction has been executed after PC is set to trap handler
      rvfi_set_trap_pc_d = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_set_trap_pc_q <= 1'b0;
      rvfi_intr_q        <= 1'b0;
    end else begin
      rvfi_set_trap_pc_q <= rvfi_set_trap_pc_d;
      rvfi_intr_q        <= rvfi_intr_d;
    end
  end

`else
  logic unused_instr_new_id, unused_instr_id_done, unused_instr_done_wb;
  assign unused_instr_id_done = instr_id_done;
  assign unused_instr_new_id = instr_new_id;
  assign unused_instr_done_wb = instr_done_wb;
`endif

  // Certain parameter combinations are not supported
  `ASSERT_INIT(IllegalParamSecure, !(SecureIbex && (RV32M == RV32MNone)))

endmodule
module ibex_counter #(
  parameter int CounterWidth = 32
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        counter_inc_i,
  input  logic        counterh_we_i,
  input  logic        counter_we_i,
  input  logic [31:0] counter_val_i,
  output logic [63:0] counter_val_o
);

  logic [63:0]             counter;
  logic [CounterWidth-1:0] counter_upd;
  logic [63:0]             counter_load;
  logic                    we;
  logic [CounterWidth-1:0] counter_d;

  // Update
  always_comb begin

    // Write
    we = counter_we_i | counterh_we_i;
    counter_load[63:32] = counter[63:32];
    counter_load[31:0]  = counter_val_i;
    if (counterh_we_i) begin
      counter_load[63:32] = counter_val_i;
      counter_load[31:0]  = counter[31:0];
    end

    // Increment
    counter_upd = counter[CounterWidth-1:0] + {{CounterWidth-1{1'b0}},1'b1};

    // Next value logic
    if (we) begin
      counter_d = counter_load[CounterWidth-1:0];
    end else if (counter_inc_i)begin
      counter_d = counter_upd[CounterWidth-1:0];
    end else begin
      counter_d = counter[CounterWidth-1:0];
    end
  end

`ifdef FPGA_XILINX
  // Set DSP pragma for supported xilinx FPGAs
  localparam int DspPragma = CounterWidth < 49  ? "yes" : "no";
  (* use_dsp = DspPragma *) logic [CounterWidth-1:0] counter_q;

  // DSP output register requires synchronous reset.
  `define COUNTER_FLOP_RST posedge clk_i
`else
  logic [CounterWidth-1:0] counter_q;

  `define COUNTER_FLOP_RST posedge clk_i or negedge rst_ni
`endif

  // Counter flop
  always_ff @(`COUNTER_FLOP_RST) begin
    if (!rst_ni) begin
      counter_q <= '0;
    end else begin
      counter_q <= counter_d;
    end
  end

  if (CounterWidth < 64) begin : g_counter_narrow
    logic [63:CounterWidth] unused_counter_load;

    assign counter[CounterWidth-1:0] = counter_q;
    assign counter[63:CounterWidth]  = '0;
    assign unused_counter_load       = counter_load[63:CounterWidth];
  end else begin : g_counter_full
    assign counter = counter_q;
  end

  assign counter_val_o = counter;

endmodule

// Keep helper defines file-local.
`undef COUNTER_FLOP_RST
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control and Status Registers
 *
 * Control and Status Registers (CSRs) following the RISC-V Privileged
 * Specification, draft version 1.11
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_cs_registers #(
    parameter bit               DbgTriggerEn      = 0,
    parameter int unsigned      DbgHwBreakNum     = 1,
    parameter bit               DataIndTiming     = 1'b0,
    parameter bit               DummyInstructions = 1'b0,
    parameter bit               ShadowCSR         = 1'b0,
    parameter bit               ICache            = 1'b0,
    parameter int unsigned      MHPMCounterNum    = 10,
    parameter int unsigned      MHPMCounterWidth  = 40,
    parameter bit               PMPEnable         = 0,
    parameter int unsigned      PMPGranularity    = 0,
    parameter int unsigned      PMPNumRegions     = 4,
    parameter bit               RV32E             = 0,
    parameter ibex_pkg::rv32m_e RV32M             = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e RV32B             = ibex_pkg::RV32BNone
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    // Hart ID
    input  logic [31:0]          hart_id_i,

    // Privilege mode
    output ibex_pkg::priv_lvl_e  priv_mode_id_o,
    output ibex_pkg::priv_lvl_e  priv_mode_if_o,
    output ibex_pkg::priv_lvl_e  priv_mode_lsu_o,
    output logic                 csr_mstatus_tw_o,

    // mtvec
    output logic [31:0]          csr_mtvec_o,
    input  logic                 csr_mtvec_init_i,
    input  logic [31:0]          boot_addr_i,

    // Interface to registers (SRAM like)
    input  logic                 csr_access_i,
    input  ibex_pkg::csr_num_e   csr_addr_i,
    input  logic [31:0]          csr_wdata_i,
    input  ibex_pkg::csr_op_e    csr_op_i,
    input                        csr_op_en_i,
    output logic [31:0]          csr_rdata_o,

    // interrupts
    input  logic                 irq_software_i,
    input  logic                 irq_timer_i,
    input  logic                 irq_external_i,
    input  logic [14:0]          irq_fast_i,
    input  logic                 nmi_mode_i,
    output logic                 irq_pending_o,          // interrupt request pending
    output ibex_pkg::irqs_t      irqs_o,                 // interrupt requests qualified with mie
    output logic                 csr_mstatus_mie_o,
    output logic [31:0]          csr_mepc_o,

    // PMP
    output ibex_pkg::pmp_cfg_t     csr_pmp_cfg_o  [PMPNumRegions],
    output logic [33:0]            csr_pmp_addr_o [PMPNumRegions],
    output ibex_pkg::pmp_mseccfg_t csr_pmp_mseccfg_o,

    // debug
    input  logic                 debug_mode_i,
    input  ibex_pkg::dbg_cause_e debug_cause_i,
    input  logic                 debug_csr_save_i,
    output logic [31:0]          csr_depc_o,
    output logic                 debug_single_step_o,
    output logic                 debug_ebreakm_o,
    output logic                 debug_ebreaku_o,
    output logic                 trigger_match_o,

    input  logic [31:0]          pc_if_i,
    input  logic [31:0]          pc_id_i,
    input  logic [31:0]          pc_wb_i,

    // CPU control bits
    output logic                 data_ind_timing_o,
    output logic                 dummy_instr_en_o,
    output logic [2:0]           dummy_instr_mask_o,
    output logic                 dummy_instr_seed_en_o,
    output logic [31:0]          dummy_instr_seed_o,
    output logic                 icache_enable_o,
    output logic                 csr_shadow_err_o,

    // Exception save/restore
    input  logic                 csr_save_if_i,
    input  logic                 csr_save_id_i,
    input  logic                 csr_save_wb_i,
    input  logic                 csr_restore_mret_i,
    input  logic                 csr_restore_dret_i,
    input  logic                 csr_save_cause_i,
    input  ibex_pkg::exc_cause_e csr_mcause_i,
    input  logic [31:0]          csr_mtval_i,
    output logic                 illegal_csr_insn_o,     // access to non-existent CSR,
                                                         // with wrong priviledge level, or
                                                         // missing write permissions
    // Performance Counters
    input  logic                 instr_ret_i,            // instr retired in ID/EX stage
    input  logic                 instr_ret_compressed_i, // compressed instr retired
    input  logic                 iside_wait_i,           // core waiting for the iside
    input  logic                 jump_i,                 // jump instr seen (j, jr, jal, jalr)
    input  logic                 branch_i,               // branch instr seen (bf, bnf)
    input  logic                 branch_taken_i,         // branch was taken
    input  logic                 mem_load_i,             // load from memory in this cycle
    input  logic                 mem_store_i,            // store to memory in this cycle
    input  logic                 dside_wait_i,           // core waiting for the dside
    input  logic                 mul_wait_i,             // core waiting for multiply
    input  logic                 div_wait_i              // core waiting for divide
);

  import ibex_pkg::*;

  localparam int unsigned RV32BEnabled = (RV32B == RV32BNone) ? 0 : 1;
  localparam int unsigned RV32MEnabled = (RV32M == RV32MNone) ? 0 : 1;
  localparam int unsigned PMPAddrWidth = (PMPGranularity > 0) ? 33 - PMPGranularity : 32;

  // misa
  localparam logic [31:0] MISA_VALUE =
      (0                 <<  0)  // A - Atomic Instructions extension
    | (RV32BEnabled      <<  1)  // B - Bit-Manipulation extension
    | (1                 <<  2)  // C - Compressed extension
    | (0                 <<  3)  // D - Double precision floating-point extension
    | (32'(RV32E)        <<  4)  // E - RV32E base ISA
    | (0                 <<  5)  // F - Single precision floating-point extension
    | (32'(!RV32E)       <<  8)  // I - RV32I/64I/128I base ISA
    | (RV32MEnabled      << 12)  // M - Integer Multiply/Divide extension
    | (0                 << 13)  // N - User level interrupts supported
    | (0                 << 18)  // S - Supervisor mode implemented
    | (1                 << 20)  // U - User mode implemented
    | (0                 << 23)  // X - Non-standard extensions present
    | (32'(CSR_MISA_MXL) << 30); // M-XLEN

  typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
  } status_t;

  typedef struct packed {
    logic      mpie;
    priv_lvl_e mpp;
  } status_stk_t;

  typedef struct packed {
      x_debug_ver_e xdebugver;
      logic [11:0]  zero2;
      logic         ebreakm;
      logic         zero1;
      logic         ebreaks;
      logic         ebreaku;
      logic         stepie;
      logic         stopcount;
      logic         stoptime;
      dbg_cause_e   cause;
      logic         zero0;
      logic         mprven;
      logic         nmip;
      logic         step;
      priv_lvl_e    prv;
  } dcsr_t;

  // CPU control register fields
  typedef struct packed {
    logic [2:0]  dummy_instr_mask;
    logic        dummy_instr_en;
    logic        data_ind_timing;
    logic        icache_enable;
  } cpu_ctrl_t;

  // Interrupt and exception control signals
  logic [31:0] exception_pc;

  // CSRs
  priv_lvl_e   priv_lvl_q, priv_lvl_d;
  status_t     mstatus_q, mstatus_d;
  logic        mstatus_err;
  logic        mstatus_en;
  irqs_t       mie_q, mie_d;
  logic        mie_en;
  logic [31:0] mscratch_q;
  logic        mscratch_en;
  logic [31:0] mepc_q, mepc_d;
  logic        mepc_en;
  logic  [5:0] mcause_q, mcause_d;
  logic        mcause_en;
  logic [31:0] mtval_q, mtval_d;
  logic        mtval_en;
  logic [31:0] mtvec_q, mtvec_d;
  logic        mtvec_err;
  logic        mtvec_en;
  irqs_t       mip;
  dcsr_t       dcsr_q, dcsr_d;
  logic        dcsr_en;
  logic [31:0] depc_q, depc_d;
  logic        depc_en;
  logic [31:0] dscratch0_q;
  logic [31:0] dscratch1_q;
  logic        dscratch0_en, dscratch1_en;

  // CSRs for recoverable NMIs
  // NOTE: these CSRS are nonstandard, see https://github.com/riscv/riscv-isa-manual/issues/261
  status_stk_t mstack_q, mstack_d;
  logic        mstack_en;
  logic [31:0] mstack_epc_q, mstack_epc_d;
  logic  [5:0] mstack_cause_q, mstack_cause_d;

  // PMP Signals
  logic [31:0]                 pmp_addr_rdata  [PMP_MAX_REGIONS];
  logic [PMP_CFG_W-1:0]        pmp_cfg_rdata   [PMP_MAX_REGIONS];
  logic                        pmp_csr_err;
  pmp_mseccfg_t                pmp_mseccfg;

  // Hardware performance monitor signals
  logic [31:0]                 mcountinhibit;
  // Only have mcountinhibit flops for counters that actually exist
  logic [MHPMCounterNum+3-1:0] mcountinhibit_d, mcountinhibit_q;
  logic                        mcountinhibit_we;

  // mhpmcounter flops are elaborated below providing only the precise number that is required based
  // on MHPMCounterNum/MHPMCounterWidth. This signal connects to the Q output of these flops
  // where they exist and is otherwise 0.
  logic [63:0] mhpmcounter [32];
  logic [31:0] mhpmcounter_we;
  logic [31:0] mhpmcounterh_we;
  logic [31:0] mhpmcounter_incr;
  logic [31:0] mhpmevent [32];
  logic  [4:0] mhpmcounter_idx;
  logic        unused_mhpmcounter_we_1;
  logic        unused_mhpmcounterh_we_1;
  logic        unused_mhpmcounter_incr_1;

  // Debug / trigger registers
  logic [31:0] tselect_rdata;
  logic [31:0] tmatch_control_rdata;
  logic [31:0] tmatch_value_rdata;

  // CPU control bits
  cpu_ctrl_t   cpuctrl_q, cpuctrl_d, cpuctrl_wdata;
  logic        cpuctrl_we;
  logic        cpuctrl_err;

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;
  logic        csr_wr;

  // Access violation signals
  logic        illegal_csr;
  logic        illegal_csr_priv;
  logic        illegal_csr_write;

  logic [7:0]  unused_boot_addr;
  logic [2:0]  unused_csr_addr;

  assign unused_boot_addr = boot_addr_i[7:0];

  /////////////
  // CSR reg //
  /////////////

  logic [$bits(csr_num_e)-1:0] csr_addr;
  assign csr_addr           = {csr_addr_i};
  assign unused_csr_addr    = csr_addr[7:5];
  assign mhpmcounter_idx    = csr_addr[4:0];

  // See RISC-V Privileged Specification, version 1.11, Section 2.1
  assign illegal_csr_priv   = (csr_addr[9:8] > {priv_lvl_q});
  assign illegal_csr_write  = (csr_addr[11:10] == 2'b11) && csr_wr;
  assign illegal_csr_insn_o = csr_access_i & (illegal_csr | illegal_csr_write | illegal_csr_priv);

  // mip CSR is purely combinational - must be able to re-enable the clock upon WFI
  assign mip.irq_software = irq_software_i;
  assign mip.irq_timer    = irq_timer_i;
  assign mip.irq_external = irq_external_i;
  assign mip.irq_fast     = irq_fast_i;

  // read logic
  always_comb begin
    csr_rdata_int = '0;
    illegal_csr   = 1'b0;

    unique case (csr_addr_i)
      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = hart_id_i;

      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: begin
        csr_rdata_int                                                   = '0;
        csr_rdata_int[CSR_MSTATUS_MIE_BIT]                              = mstatus_q.mie;
        csr_rdata_int[CSR_MSTATUS_MPIE_BIT]                             = mstatus_q.mpie;
        csr_rdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW] = mstatus_q.mpp;
        csr_rdata_int[CSR_MSTATUS_MPRV_BIT]                             = mstatus_q.mprv;
        csr_rdata_int[CSR_MSTATUS_TW_BIT]                               = mstatus_q.tw;
      end

      // misa
      CSR_MISA: csr_rdata_int = MISA_VALUE;

      // interrupt enable
      CSR_MIE: begin
        csr_rdata_int                                     = '0;
        csr_rdata_int[CSR_MSIX_BIT]                       = mie_q.irq_software;
        csr_rdata_int[CSR_MTIX_BIT]                       = mie_q.irq_timer;
        csr_rdata_int[CSR_MEIX_BIT]                       = mie_q.irq_external;
        csr_rdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] = mie_q.irq_fast;
      end

      // mcounteren: machine counter enable
      CSR_MCOUNTEREN: begin
        csr_rdata_int = '0;
      end

      CSR_MSCRATCH: csr_rdata_int = mscratch_q;

      // mtvec: trap-vector base address
      CSR_MTVEC: csr_rdata_int = mtvec_q;

      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;

      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};

      // mtval: trap value
      CSR_MTVAL: csr_rdata_int = mtval_q;

      // mip: interrupt pending
      CSR_MIP: begin
        csr_rdata_int                                     = '0;
        csr_rdata_int[CSR_MSIX_BIT]                       = mip.irq_software;
        csr_rdata_int[CSR_MTIX_BIT]                       = mip.irq_timer;
        csr_rdata_int[CSR_MEIX_BIT]                       = mip.irq_external;
        csr_rdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] = mip.irq_fast;
      end

      CSR_MSECCFG: begin
        if (PMPEnable) begin
          csr_rdata_int                       = '0;
          csr_rdata_int[CSR_MSECCFG_MML_BIT]  = pmp_mseccfg.mml;
          csr_rdata_int[CSR_MSECCFG_MMWP_BIT] = pmp_mseccfg.mmwp;
          csr_rdata_int[CSR_MSECCFG_RLB_BIT]  = pmp_mseccfg.rlb;
        end else begin
          illegal_csr = 1'b1;
        end
      end

      CSR_MSECCFGH: begin
        if (PMPEnable) begin
          csr_rdata_int = '0;
        end else begin
          illegal_csr = 1'b1;
        end
      end

      // PMP registers
      CSR_PMPCFG0:   csr_rdata_int = {pmp_cfg_rdata[3],  pmp_cfg_rdata[2],
                                      pmp_cfg_rdata[1],  pmp_cfg_rdata[0]};
      CSR_PMPCFG1:   csr_rdata_int = {pmp_cfg_rdata[7],  pmp_cfg_rdata[6],
                                      pmp_cfg_rdata[5],  pmp_cfg_rdata[4]};
      CSR_PMPCFG2:   csr_rdata_int = {pmp_cfg_rdata[11], pmp_cfg_rdata[10],
                                      pmp_cfg_rdata[9],  pmp_cfg_rdata[8]};
      CSR_PMPCFG3:   csr_rdata_int = {pmp_cfg_rdata[15], pmp_cfg_rdata[14],
                                      pmp_cfg_rdata[13], pmp_cfg_rdata[12]};
      CSR_PMPADDR0:  csr_rdata_int = pmp_addr_rdata[0];
      CSR_PMPADDR1:  csr_rdata_int = pmp_addr_rdata[1];
      CSR_PMPADDR2:  csr_rdata_int = pmp_addr_rdata[2];
      CSR_PMPADDR3:  csr_rdata_int = pmp_addr_rdata[3];
      CSR_PMPADDR4:  csr_rdata_int = pmp_addr_rdata[4];
      CSR_PMPADDR5:  csr_rdata_int = pmp_addr_rdata[5];
      CSR_PMPADDR6:  csr_rdata_int = pmp_addr_rdata[6];
      CSR_PMPADDR7:  csr_rdata_int = pmp_addr_rdata[7];
      CSR_PMPADDR8:  csr_rdata_int = pmp_addr_rdata[8];
      CSR_PMPADDR9:  csr_rdata_int = pmp_addr_rdata[9];
      CSR_PMPADDR10: csr_rdata_int = pmp_addr_rdata[10];
      CSR_PMPADDR11: csr_rdata_int = pmp_addr_rdata[11];
      CSR_PMPADDR12: csr_rdata_int = pmp_addr_rdata[12];
      CSR_PMPADDR13: csr_rdata_int = pmp_addr_rdata[13];
      CSR_PMPADDR14: csr_rdata_int = pmp_addr_rdata[14];
      CSR_PMPADDR15: csr_rdata_int = pmp_addr_rdata[15];

      CSR_DCSR: begin
        csr_rdata_int = dcsr_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DPC: begin
        csr_rdata_int = depc_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DSCRATCH0: begin
        csr_rdata_int = dscratch0_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DSCRATCH1: begin
        csr_rdata_int = dscratch1_q;
        illegal_csr = ~debug_mode_i;
      end

      // machine counter/timers
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit;
      CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31: begin
        csr_rdata_int = mhpmevent[mhpmcounter_idx];
      end

      CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31: begin
        csr_rdata_int = mhpmcounter[mhpmcounter_idx][31:0];
      end

      CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H: begin
        csr_rdata_int = mhpmcounter[mhpmcounter_idx][63:32];
      end

      // Debug triggers
      CSR_TSELECT: begin
        csr_rdata_int = tselect_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA1: begin
        csr_rdata_int = tmatch_control_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA2: begin
        csr_rdata_int = tmatch_value_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA3: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_MCONTEXT: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_SCONTEXT: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end

      // Custom CSR for controlling CPU features
      CSR_CPUCTRL: begin
        csr_rdata_int = {{32-$bits(cpu_ctrl_t){1'b0}},cpuctrl_q};
      end

      // Custom CSR for LFSR re-seeding (cannot be read)
      CSR_SECURESEED: begin
        csr_rdata_int = '0;
      end

      default: begin
        illegal_csr = 1'b1;
      end
    endcase
  end

  // write logic
  always_comb begin
    exception_pc = pc_id_i;

    priv_lvl_d   = priv_lvl_q;
    mstatus_en   = 1'b0;
    mstatus_d    = mstatus_q;
    mie_en       = 1'b0;
    mscratch_en  = 1'b0;
    mepc_en      = 1'b0;
    mepc_d       = {csr_wdata_int[31:1], 1'b0};
    mcause_en    = 1'b0;
    mcause_d     = {csr_wdata_int[31], csr_wdata_int[4:0]};
    mtval_en     = 1'b0;
    mtval_d      = csr_wdata_int;
    mtvec_en     = csr_mtvec_init_i;
    // mtvec.MODE set to vectored
    // mtvec.BASE must be 256-byte aligned
    mtvec_d      = csr_mtvec_init_i ? {boot_addr_i[31:8], 6'b0, 2'b01} :
                                      {csr_wdata_int[31:8], 6'b0, 2'b01};
    dcsr_en      = 1'b0;
    dcsr_d       = dcsr_q;
    depc_d       = {csr_wdata_int[31:1], 1'b0};
    depc_en      = 1'b0;
    dscratch0_en = 1'b0;
    dscratch1_en = 1'b0;

    mstack_en      = 1'b0;
    mstack_d.mpie  = mstatus_q.mpie;
    mstack_d.mpp   = mstatus_q.mpp;
    mstack_epc_d   = mepc_q;
    mstack_cause_d = mcause_q;

    mcountinhibit_we = 1'b0;
    mhpmcounter_we   = '0;
    mhpmcounterh_we  = '0;

    cpuctrl_we       = 1'b0;

    if (csr_we_int) begin
      unique case (csr_addr_i)
        // mstatus: IE bit
        CSR_MSTATUS: begin
          mstatus_en = 1'b1;
          mstatus_d    = '{
              mie:  csr_wdata_int[CSR_MSTATUS_MIE_BIT],
              mpie: csr_wdata_int[CSR_MSTATUS_MPIE_BIT],
              mpp:  priv_lvl_e'(csr_wdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW]),
              mprv: csr_wdata_int[CSR_MSTATUS_MPRV_BIT],
              tw:   csr_wdata_int[CSR_MSTATUS_TW_BIT]
          };
          // Convert illegal values to M-mode
          if ((mstatus_d.mpp != PRIV_LVL_M) && (mstatus_d.mpp != PRIV_LVL_U)) begin
            mstatus_d.mpp = PRIV_LVL_M;
          end
        end

        // interrupt enable
        CSR_MIE: mie_en = 1'b1;

        CSR_MSCRATCH: mscratch_en = 1'b1;

        // mepc: exception program counter
        CSR_MEPC: mepc_en = 1'b1;

        // mcause
        CSR_MCAUSE: mcause_en = 1'b1;

        // mtval: trap value
        CSR_MTVAL: mtval_en = 1'b1;

        // mtvec
        CSR_MTVEC: mtvec_en = 1'b1;

        CSR_DCSR: begin
          dcsr_d = csr_wdata_int;
          dcsr_d.xdebugver = XDEBUGVER_STD;
          // Change to PRIV_LVL_M if software writes an unsupported value
          if ((dcsr_d.prv != PRIV_LVL_M) && (dcsr_d.prv != PRIV_LVL_U)) begin
            dcsr_d.prv = PRIV_LVL_M;
          end

          // Read-only for SW
          dcsr_d.cause = dcsr_q.cause;

          // Interrupts always disabled during single stepping
          dcsr_d.stepie = 1'b0;

          // currently not supported:
          dcsr_d.nmip = 1'b0;
          dcsr_d.mprven = 1'b0;
          dcsr_d.stopcount = 1'b0;
          dcsr_d.stoptime = 1'b0;

          // forced to be zero
          dcsr_d.zero0 = 1'b0;
          dcsr_d.zero1 = 1'b0;
          dcsr_d.zero2 = 12'h0;
          dcsr_en      = 1'b1;
        end

        // dpc: debug program counter
        CSR_DPC: depc_en = 1'b1;

        CSR_DSCRATCH0: dscratch0_en = 1'b1;
        CSR_DSCRATCH1: dscratch1_en = 1'b1;

        // machine counter/timers
        CSR_MCOUNTINHIBIT: mcountinhibit_we = 1'b1;

        CSR_MCYCLE,
        CSR_MINSTRET,
        CSR_MHPMCOUNTER3,
        CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
        CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
        CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
        CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
        CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
        CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
        CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31: begin
          mhpmcounter_we[mhpmcounter_idx] = 1'b1;
        end

        CSR_MCYCLEH,
        CSR_MINSTRETH,
        CSR_MHPMCOUNTER3H,
        CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
        CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
        CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
        CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
        CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
        CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
        CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H: begin
          mhpmcounterh_we[mhpmcounter_idx] = 1'b1;
        end

        CSR_CPUCTRL: cpuctrl_we = 1'b1;

        default:;
      endcase
    end

    // exception controller gets priority over other writes
    unique case (1'b1)

      csr_save_cause_i: begin
        unique case (1'b1)
          csr_save_if_i: begin
            exception_pc = pc_if_i;
          end
          csr_save_id_i: begin
            exception_pc = pc_id_i;
          end
          csr_save_wb_i: begin
            exception_pc = pc_wb_i;
          end
          default:;
        endcase

        // Any exception, including debug mode, causes a switch to M-mode
        priv_lvl_d = PRIV_LVL_M;

        if (debug_csr_save_i) begin
          // all interrupts are masked
          // do not update cause, epc, tval, epc and status
          dcsr_d.prv   = priv_lvl_q;
          dcsr_d.cause = debug_cause_i;
          dcsr_en      = 1'b1;
          depc_d       = exception_pc;
          depc_en      = 1'b1;
        end else if (!debug_mode_i) begin
          // In debug mode, "exceptions do not update any registers. That
          // includes cause, epc, tval, dpc and mstatus." [Debug Spec v0.13.2, p.39]
          mtval_en       = 1'b1;
          mtval_d        = csr_mtval_i;
          mstatus_en     = 1'b1;
          mstatus_d.mie  = 1'b0; // disable interrupts
          // save current status
          mstatus_d.mpie = mstatus_q.mie;
          mstatus_d.mpp  = priv_lvl_q;
          mepc_en        = 1'b1;
          mepc_d         = exception_pc;
          mcause_en      = 1'b1;
          mcause_d       = {csr_mcause_i};
          // save previous status for recoverable NMI
          mstack_en      = 1'b1;
        end
      end // csr_save_cause_i

      csr_restore_dret_i: begin // DRET
        priv_lvl_d = dcsr_q.prv;
      end // csr_restore_dret_i

      csr_restore_mret_i: begin // MRET
        priv_lvl_d     = mstatus_q.mpp;
        mstatus_en     = 1'b1;
        mstatus_d.mie  = mstatus_q.mpie; // re-enable interrupts

        if (nmi_mode_i) begin
          // when returning from an NMI restore state from mstack CSR
          mstatus_d.mpie = mstack_q.mpie;
          mstatus_d.mpp  = mstack_q.mpp;
          mepc_en        = 1'b1;
          mepc_d         = mstack_epc_q;
          mcause_en      = 1'b1;
          mcause_d       = mstack_cause_q;
        end else begin
          // otherwise just set mstatus.MPIE/MPP
          // See RISC-V Privileged Specification, version 1.11, Section 3.1.6.1
          mstatus_d.mpie = 1'b1;
          mstatus_d.mpp  = PRIV_LVL_U;
        end
      end // csr_restore_mret_i

      default:;
    endcase
  end

  // Update current priv level
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      priv_lvl_q     <= PRIV_LVL_M;
    end else begin
      priv_lvl_q     <= priv_lvl_d;
    end
  end

  // Send current priv level to the decoder
  assign priv_mode_id_o = priv_lvl_q;
  // New instruction fetches need to account for updates to priv_lvl_q this cycle
  assign priv_mode_if_o = priv_lvl_d;
  // Load/store instructions must factor in MPRV for PMP checking
  assign priv_mode_lsu_o = mstatus_q.mprv ? mstatus_q.mpp : priv_lvl_q;

  // CSR operation logic
  always_comb begin
    unique case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int =  csr_wdata_i;
      CSR_OP_SET:   csr_wdata_int =  csr_wdata_i | csr_rdata_o;
      CSR_OP_CLEAR: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
      CSR_OP_READ:  csr_wdata_int = csr_wdata_i;
      default:      csr_wdata_int = csr_wdata_i;
    endcase
  end

  assign csr_wr = (csr_op_i inside {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR});

  // only write CSRs during one clock cycle
  assign csr_we_int  = csr_wr & csr_op_en_i & ~illegal_csr_insn_o;

  assign csr_rdata_o = csr_rdata_int;

  // directly output some registers
  assign csr_mepc_o  = mepc_q;
  assign csr_depc_o  = depc_q;
  assign csr_mtvec_o = mtvec_q;

  assign csr_mstatus_mie_o   = mstatus_q.mie;
  assign csr_mstatus_tw_o    = mstatus_q.tw;
  assign debug_single_step_o = dcsr_q.step;
  assign debug_ebreakm_o     = dcsr_q.ebreakm;
  assign debug_ebreaku_o     = dcsr_q.ebreaku;

  // Qualify incoming interrupt requests in mip CSR with mie CSR for controller and to re-enable
  // clock upon WFI (must be purely combinational).
  assign irqs_o        = mip & mie_q;
  assign irq_pending_o = |irqs_o;

  ////////////////////////
  // CSR instantiations //
  ////////////////////////

  // MSTATUS
  localparam status_t MSTATUS_RST_VAL = '{mie:  1'b0,
                                          mpie: 1'b1,
                                          mpp:  PRIV_LVL_U,
                                          mprv: 1'b0,
                                          tw:   1'b0};
  ibex_csr #(
    .Width      ($bits(status_t)),
    .ShadowCopy (ShadowCSR),
    .ResetValue ({MSTATUS_RST_VAL})
  ) u_mstatus_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  ({mstatus_d}),
    .wr_en_i    (mstatus_en),
    .rd_data_o  (mstatus_q),
    .rd_error_o (mstatus_err)
  );

  // MEPC
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mepc_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mepc_d),
    .wr_en_i    (mepc_en),
    .rd_data_o  (mepc_q),
    .rd_error_o ()
  );

  // MIE
  assign mie_d.irq_software = csr_wdata_int[CSR_MSIX_BIT];
  assign mie_d.irq_timer    = csr_wdata_int[CSR_MTIX_BIT];
  assign mie_d.irq_external = csr_wdata_int[CSR_MEIX_BIT];
  assign mie_d.irq_fast     = csr_wdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW];
  ibex_csr #(
    .Width      ($bits(irqs_t)),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mie_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  ({mie_d}),
    .wr_en_i    (mie_en),
    .rd_data_o  (mie_q),
    .rd_error_o ()
  );

  // MSCRATCH
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mscratch_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (csr_wdata_int),
    .wr_en_i    (mscratch_en),
    .rd_data_o  (mscratch_q),
    .rd_error_o ()
  );

  // MCAUSE
  ibex_csr #(
    .Width      (6),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mcause_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mcause_d),
    .wr_en_i    (mcause_en),
    .rd_data_o  (mcause_q),
    .rd_error_o ()
  );

  // MTVAL
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mtval_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mtval_d),
    .wr_en_i    (mtval_en),
    .rd_data_o  (mtval_q),
    .rd_error_o ()
  );

  // MTVEC
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (ShadowCSR),
    .ResetValue (32'd1)
  ) u_mtvec_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mtvec_d),
    .wr_en_i    (mtvec_en),
    .rd_data_o  (mtvec_q),
    .rd_error_o (mtvec_err)
  );

  // DCSR
  localparam dcsr_t DCSR_RESET_VAL = '{
      xdebugver: XDEBUGVER_STD,
      cause:     DBG_CAUSE_NONE, // 3'h0
      prv:       PRIV_LVL_M,
      default:   '0
  };
  ibex_csr #(
    .Width      ($bits(dcsr_t)),
    .ShadowCopy (1'b0),
    .ResetValue ({DCSR_RESET_VAL})
  ) u_dcsr_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  ({dcsr_d}),
    .wr_en_i    (dcsr_en),
    .rd_data_o  (dcsr_q),
    .rd_error_o ()
  );

  // DEPC
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_depc_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (depc_d),
    .wr_en_i    (depc_en),
    .rd_data_o  (depc_q),
    .rd_error_o ()
  );

  // DSCRATCH0
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_dscratch0_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (csr_wdata_int),
    .wr_en_i    (dscratch0_en),
    .rd_data_o  (dscratch0_q),
    .rd_error_o ()
  );

  // DSCRATCH1
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_dscratch1_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (csr_wdata_int),
    .wr_en_i    (dscratch1_en),
    .rd_data_o  (dscratch1_q),
    .rd_error_o ()
  );

  // MSTACK
  localparam status_stk_t MSTACK_RESET_VAL = '{
      mpie: 1'b1,
      mpp:  PRIV_LVL_U
  };
  ibex_csr #(
    .Width      ($bits(status_stk_t)),
    .ShadowCopy (1'b0),
    .ResetValue ({MSTACK_RESET_VAL})
  ) u_mstack_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  ({mstack_d}),
    .wr_en_i    (mstack_en),
    .rd_data_o  (mstack_q),
    .rd_error_o ()
  );

  // MSTACK_EPC
  ibex_csr #(
    .Width      (32),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mstack_epc_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mstack_epc_d),
    .wr_en_i    (mstack_en),
    .rd_data_o  (mstack_epc_q),
    .rd_error_o ()
  );

  // MSTACK_CAUSE
  ibex_csr #(
    .Width      (6),
    .ShadowCopy (1'b0),
    .ResetValue ('0)
  ) u_mstack_cause_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  (mstack_cause_d),
    .wr_en_i    (mstack_en),
    .rd_data_o  (mstack_cause_q),
    .rd_error_o ()
  );

  // -----------------
  // PMP registers
  // -----------------

  if (PMPEnable) begin : g_pmp_registers
    pmp_mseccfg_t                pmp_mseccfg_q, pmp_mseccfg_d;
    logic                        pmp_mseccfg_we;
    logic                        pmp_mseccfg_err;
    pmp_cfg_t                    pmp_cfg         [PMPNumRegions];
    logic [PMPNumRegions-1:0]    pmp_cfg_locked;
    pmp_cfg_t                    pmp_cfg_wdata   [PMPNumRegions];
    logic [PMPAddrWidth-1:0]     pmp_addr        [PMPNumRegions];
    logic [PMPNumRegions-1:0]    pmp_cfg_we;
    logic [PMPNumRegions-1:0]    pmp_cfg_err;
    logic [PMPNumRegions-1:0]    pmp_addr_we;
    logic [PMPNumRegions-1:0]    pmp_addr_err;
    logic                        any_pmp_entry_locked;

    // Expanded / qualified register read data
    for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_exp_rd_data
      if (i < PMPNumRegions) begin : g_implemented_regions
        // Add in zero padding for reserved fields
        assign pmp_cfg_rdata[i] = {pmp_cfg[i].lock, 2'b00, pmp_cfg[i].mode,
                                   pmp_cfg[i].exec, pmp_cfg[i].write, pmp_cfg[i].read};

        // Address field read data depends on the current programmed mode and the granularity
        // See RISC-V Privileged Specification, version 1.11, Section 3.6.1
        if (PMPGranularity == 0) begin : g_pmp_g0
          // If G == 0, read data is unmodified
          assign pmp_addr_rdata[i] = pmp_addr[i];

        end else if (PMPGranularity == 1) begin : g_pmp_g1
          // If G == 1, bit [G-1] reads as zero in TOR or OFF mode
          always_comb begin
            pmp_addr_rdata[i] = pmp_addr[i];
            if ((pmp_cfg[i].mode == PMP_MODE_OFF) || (pmp_cfg[i].mode == PMP_MODE_TOR)) begin
              pmp_addr_rdata[i][PMPGranularity-1:0] = '0;
            end
          end

        end else begin : g_pmp_g2
          // For G >= 2, bits are masked to one or zero depending on the mode
          always_comb begin
            // In NAPOT mode, bits [G-2:0] must read as one
            pmp_addr_rdata[i] = {pmp_addr[i], {PMPGranularity-1{1'b1}}};

            if ((pmp_cfg[i].mode == PMP_MODE_OFF) || (pmp_cfg[i].mode == PMP_MODE_TOR)) begin
              // In TOR or OFF mode, bits [G-1:0] must read as zero
              pmp_addr_rdata[i][PMPGranularity-1:0] = '0;
            end
          end
        end

      end else begin : g_other_regions
        // Non-implemented regions read as zero
        assign pmp_cfg_rdata[i]  = '0;
        assign pmp_addr_rdata[i] = '0;
      end
    end

    // Write data calculation
    for (genvar i = 0; i < PMPNumRegions; i++) begin : g_pmp_csrs
      // -------------------------
      // Instantiate cfg registers
      // -------------------------
      assign pmp_cfg_we[i] = csr_we_int & ~pmp_cfg_locked[i] &
                             (csr_addr == (CSR_OFF_PMP_CFG + (i[11:0] >> 2)));

      // Select the correct WDATA (each CSR contains 4 CFG fields, each with 2 RES bits)
      assign pmp_cfg_wdata[i].lock  = csr_wdata_int[(i%4)*PMP_CFG_W+7];
      // NA4 mode is not selectable when G > 0, mode is treated as OFF
      always_comb begin
        unique case (csr_wdata_int[(i%4)*PMP_CFG_W+3+:2])
          2'b00   : pmp_cfg_wdata[i].mode = PMP_MODE_OFF;
          2'b01   : pmp_cfg_wdata[i].mode = PMP_MODE_TOR;
          2'b10   : pmp_cfg_wdata[i].mode = (PMPGranularity == 0) ? PMP_MODE_NA4:
                                                                    PMP_MODE_OFF;
          2'b11   : pmp_cfg_wdata[i].mode = PMP_MODE_NAPOT;
          default : pmp_cfg_wdata[i].mode = PMP_MODE_OFF;
        endcase
      end
      assign pmp_cfg_wdata[i].exec  = csr_wdata_int[(i%4)*PMP_CFG_W+2];
      // When MSECCFG.MML is unset, W = 1, R = 0 is a reserved combination, so force W to 0 if R ==
      // 0. Otherwise allow all possible values to be written.
      assign pmp_cfg_wdata[i].write = pmp_mseccfg_q.mml ? csr_wdata_int[(i%4)*PMP_CFG_W+1] :
                                                          &csr_wdata_int[(i%4)*PMP_CFG_W+:2];
      assign pmp_cfg_wdata[i].read  = csr_wdata_int[(i%4)*PMP_CFG_W];

      ibex_csr #(
        .Width      ($bits(pmp_cfg_t)),
        .ShadowCopy (ShadowCSR),
        .ResetValue ('0)
      ) u_pmp_cfg_csr (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .wr_data_i  ({pmp_cfg_wdata[i]}),
        .wr_en_i    (pmp_cfg_we[i]),
        .rd_data_o  (pmp_cfg[i]),
        .rd_error_o (pmp_cfg_err[i])
      );

      // MSECCFG.RLB allows the lock bit to be bypassed (allowing cfg writes when MSECCFG.RLB is
      // set).
      assign pmp_cfg_locked[i] = pmp_cfg[i].lock & ~pmp_mseccfg_q.rlb;

      // --------------------------
      // Instantiate addr registers
      // --------------------------
      if (i < PMPNumRegions - 1) begin : g_lower
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg_locked[i] &
                                (~pmp_cfg_locked[i+1] | (pmp_cfg[i+1].mode != PMP_MODE_TOR)) &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end else begin : g_upper
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg_locked[i] &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end

      ibex_csr #(
        .Width      (PMPAddrWidth),
        .ShadowCopy (ShadowCSR),
        .ResetValue ('0)
      ) u_pmp_addr_csr (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .wr_data_i  (csr_wdata_int[31-:PMPAddrWidth]),
        .wr_en_i    (pmp_addr_we[i]),
        .rd_data_o  (pmp_addr[i]),
        .rd_error_o (pmp_addr_err[i])
      );

      assign csr_pmp_cfg_o[i]  = pmp_cfg[i];
      assign csr_pmp_addr_o[i] = {pmp_addr_rdata[i], 2'b00};
    end

    assign pmp_mseccfg_we = csr_we_int & (csr_addr == CSR_MSECCFG);

    // MSECCFG.MML/MSECCFG.MMWP cannot be unset once set
    assign pmp_mseccfg_d.mml  = pmp_mseccfg_q.mml  ? 1'b1 : csr_wdata_int[CSR_MSECCFG_MML_BIT];
    assign pmp_mseccfg_d.mmwp = pmp_mseccfg_q.mmwp ? 1'b1 : csr_wdata_int[CSR_MSECCFG_MMWP_BIT];

    // pmp_cfg_locked factors in MSECCFG.RLB so any_pmp_entry_locked will only be set if MSECCFG.RLB
    // is unset
    assign any_pmp_entry_locked = |pmp_cfg_locked;

    // When any PMP entry is locked (A PMP entry has the L bit set and MSECCFG.RLB is unset),
    // MSECCFG.RLB cannot be set again
    assign pmp_mseccfg_d.rlb = any_pmp_entry_locked ? 1'b0 : csr_wdata_int[CSR_MSECCFG_RLB_BIT];

    ibex_csr #(
      .Width      ($bits(pmp_mseccfg_t)),
      .ShadowCopy (ShadowCSR),
      .ResetValue ('0)
    ) u_pmp_mseccfg (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .wr_data_i  (pmp_mseccfg_d),
      .wr_en_i    (pmp_mseccfg_we),
      .rd_data_o  (pmp_mseccfg_q),
      .rd_error_o (pmp_mseccfg_err)
    );

    assign pmp_csr_err = (|pmp_cfg_err) | (|pmp_addr_err) | pmp_mseccfg_err;
    assign pmp_mseccfg = pmp_mseccfg_q;

  end else begin : g_no_pmp_tieoffs
    // Generate tieoffs when PMP is not configured
    for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_rdata
      assign pmp_addr_rdata[i] = '0;
      assign pmp_cfg_rdata[i]  = '0;
    end
    for (genvar i = 0; i < PMPNumRegions; i++) begin : g_outputs
      assign csr_pmp_cfg_o[i]  = pmp_cfg_t'(1'b0);
      assign csr_pmp_addr_o[i] = '0;
    end
    assign pmp_csr_err = 1'b0;
    assign pmp_mseccfg = '0;
  end

  assign csr_pmp_mseccfg_o = pmp_mseccfg;

  //////////////////////////
  //  Performance monitor //
  //////////////////////////

  // update enable signals
  always_comb begin : mcountinhibit_update
    if (mcountinhibit_we == 1'b1) begin
      // bit 1 must always be 0
      mcountinhibit_d = {csr_wdata_int[MHPMCounterNum+2:2], 1'b0, csr_wdata_int[0]};
    end else begin
      mcountinhibit_d = mcountinhibit_q;
    end
  end

  // event selection (hardwired) & control
  always_comb begin : gen_mhpmcounter_incr

    // Assign inactive counters (first to prevent latch inference)
    for (int unsigned i=0; i<32; i++) begin : gen_mhpmcounter_incr_inactive
      mhpmcounter_incr[i] = 1'b0;
    end

    // When adding or altering performance counter meanings and default
    // mappings please update dv/verilator/pcount/cpp/ibex_pcounts.cc
    // appropriately.
    //
    // active counters
    mhpmcounter_incr[0]  = 1'b1;                   // mcycle
    mhpmcounter_incr[1]  = 1'b0;                   // reserved
    mhpmcounter_incr[2]  = instr_ret_i;            // minstret
    mhpmcounter_incr[3]  = dside_wait_i;           // cycles waiting for data memory
    mhpmcounter_incr[4]  = iside_wait_i;           // cycles waiting for instr fetches
    mhpmcounter_incr[5]  = mem_load_i;             // num of loads
    mhpmcounter_incr[6]  = mem_store_i;            // num of stores
    mhpmcounter_incr[7]  = jump_i;                 // num of jumps (unconditional)
    mhpmcounter_incr[8]  = branch_i;               // num of branches (conditional)
    mhpmcounter_incr[9]  = branch_taken_i;         // num of taken branches (conditional)
    mhpmcounter_incr[10] = instr_ret_compressed_i; // num of compressed instr
    mhpmcounter_incr[11] = mul_wait_i;             // cycles waiting for multiply
    mhpmcounter_incr[12] = div_wait_i;             // cycles waiting for divide
  end

  // event selector (hardwired, 0 means no event)
  always_comb begin : gen_mhpmevent

    // activate all
    for (int i=0; i<32; i++) begin : gen_mhpmevent_active
      mhpmevent[i]    =   '0;
      mhpmevent[i][i] = 1'b1;
    end

    // deactivate
    mhpmevent[1] = '0; // not existing, reserved
    for (int unsigned i=3+MHPMCounterNum; i<32; i++) begin : gen_mhpmevent_inactive
      mhpmevent[i] = '0;
    end
  end

  // mcycle
  ibex_counter #(
    .CounterWidth(64)
  ) mcycle_counter_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .counter_inc_i(mhpmcounter_incr[0] & ~mcountinhibit[0]),
    .counterh_we_i(mhpmcounterh_we[0]),
    .counter_we_i(mhpmcounter_we[0]),
    .counter_val_i(csr_wdata_int),
    .counter_val_o(mhpmcounter[0])
  );

  // minstret
  ibex_counter #(
    .CounterWidth(64)
  ) minstret_counter_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .counter_inc_i(mhpmcounter_incr[2] & ~mcountinhibit[2]),
    .counterh_we_i(mhpmcounterh_we[2]),
    .counter_we_i(mhpmcounter_we[2]),
    .counter_val_i(csr_wdata_int),
    .counter_val_o(mhpmcounter[2])
  );

  // reserved:
  assign mhpmcounter[1]            = '0;
  assign unused_mhpmcounter_we_1   = mhpmcounter_we[1];
  assign unused_mhpmcounterh_we_1  = mhpmcounterh_we[1];
  assign unused_mhpmcounter_incr_1 = mhpmcounter_incr[1];

  for (genvar cnt=0; cnt < 29; cnt++) begin : gen_cntrs
    if (cnt < MHPMCounterNum) begin : gen_imp
      ibex_counter #(
        .CounterWidth(MHPMCounterWidth)
      ) mcounters_variable_i (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .counter_inc_i(mhpmcounter_incr[cnt+3] & ~mcountinhibit[cnt+3]),
        .counterh_we_i(mhpmcounterh_we[cnt+3]),
        .counter_we_i(mhpmcounter_we[cnt+3]),
        .counter_val_i(csr_wdata_int),
        .counter_val_o(mhpmcounter[cnt+3])
      );
    end else begin : gen_unimp
      assign mhpmcounter[cnt+3] = '0;
    end
  end

  if(MHPMCounterNum < 29) begin : g_mcountinhibit_reduced
    logic [29-MHPMCounterNum-1:0] unused_mhphcounter_we;
    logic [29-MHPMCounterNum-1:0] unused_mhphcounterh_we;
    logic [29-MHPMCounterNum-1:0] unused_mhphcounter_incr;

    assign mcountinhibit = {{29-MHPMCounterNum{1'b1}}, mcountinhibit_q};
    // Lint tieoffs for unused bits
    assign unused_mhphcounter_we   = mhpmcounter_we[31:MHPMCounterNum+3];
    assign unused_mhphcounterh_we  = mhpmcounterh_we[31:MHPMCounterNum+3];
    assign unused_mhphcounter_incr = mhpmcounter_incr[31:MHPMCounterNum+3];
  end else begin : g_mcountinhibit_full
    assign mcountinhibit = mcountinhibit_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mcountinhibit_q <= '0;
    end else begin
      mcountinhibit_q <= mcountinhibit_d;
    end
  end

  /////////////////////////////
  // Debug trigger registers //
  /////////////////////////////

  if (DbgTriggerEn) begin : gen_trigger_regs
    localparam int unsigned DbgHwNumLen = DbgHwBreakNum > 1 ? $clog2(DbgHwBreakNum) : 1;
    localparam int unsigned MaxTselect = DbgHwBreakNum - 1;

    // Register values
    logic [DbgHwNumLen-1:0]   tselect_d, tselect_q;
    logic                     tmatch_control_d;
    logic [DbgHwBreakNum-1:0] tmatch_control_q;
    logic [31:0]              tmatch_value_d;
    logic [31:0]              tmatch_value_q[DbgHwBreakNum];
    logic                     selected_tmatch_control;
    logic [31:0]              selected_tmatch_value;

    // Write enables
    logic                     tselect_we;
    logic [DbgHwBreakNum-1:0] tmatch_control_we;
    logic [DbgHwBreakNum-1:0] tmatch_value_we;
    // Trigger comparison result
    logic [DbgHwBreakNum-1:0] trigger_match;

    // Write select
    assign tselect_we = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TSELECT);
    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_tmatch_we
      assign tmatch_control_we[i] = (i[DbgHwNumLen-1:0] == tselect_q) & csr_we_int & debug_mode_i &
                                    (csr_addr_i == CSR_TDATA1);
      assign tmatch_value_we[i]   = (i[DbgHwNumLen-1:0] == tselect_q) & csr_we_int & debug_mode_i &
                                    (csr_addr_i == CSR_TDATA2);
    end

    // Debug interface tests the available number of triggers by writing and reading the trigger
    // select register. Only allow changes to the register if it is within the supported region.
    assign tselect_d = (csr_wdata_int < DbgHwBreakNum) ? csr_wdata_int[DbgHwNumLen-1:0] :
                                                         MaxTselect[DbgHwNumLen-1:0];

    // tmatch_control is enabled when the execute bit is set
    assign tmatch_control_d = csr_wdata_int[2];
    assign tmatch_value_d   = csr_wdata_int[31:0];

    // Registers
    ibex_csr #(
      .Width      (DbgHwNumLen),
      .ShadowCopy (1'b0),
      .ResetValue ('0)
    ) u_tselect_csr (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .wr_data_i  (tselect_d),
      .wr_en_i    (tselect_we),
      .rd_data_o  (tselect_q),
      .rd_error_o ()
    );

    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_tmatch_reg
      ibex_csr #(
        .Width      (1),
        .ShadowCopy (1'b0),
        .ResetValue ('0)
      ) u_tmatch_control_csr (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .wr_data_i  (tmatch_control_d),
        .wr_en_i    (tmatch_control_we[i]),
        .rd_data_o  (tmatch_control_q[i]),
        .rd_error_o ()
    );

      ibex_csr #(
        .Width      (32),
        .ShadowCopy (1'b0),
        .ResetValue ('0)
      ) u_tmatch_value_csr (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        .wr_data_i  (tmatch_value_d),
        .wr_en_i    (tmatch_value_we[i]),
        .rd_data_o  (tmatch_value_q[i]),
        .rd_error_o ()
      );
    end

    // Assign read data
    // TSELECT - number of supported triggers defined by parameter DbgHwBreakNum
    localparam int unsigned TSelectRdataPadlen = DbgHwNumLen >= 32 ? 0 : (32 - DbgHwNumLen);
    assign tselect_rdata = {{TSelectRdataPadlen{1'b0}}, tselect_q};

    if (DbgHwBreakNum > 1) begin : g_dbg_tmatch_multiple_select
      assign selected_tmatch_control = tmatch_control_q[tselect_q];
      assign selected_tmatch_value   = tmatch_value_q[tselect_q];
    end else begin : g_dbg_tmatch_single_select
      assign selected_tmatch_control = tmatch_control_q[0];
      assign selected_tmatch_value   = tmatch_value_q[0];
    end

    // TDATA0 - only support simple address matching
    assign tmatch_control_rdata = {4'h2,                    // type    : address/data match
                                   1'b1,                    // dmode   : access from D mode only
                                   6'h00,                   // maskmax : exact match only
                                   1'b0,                    // hit     : not supported
                                   1'b0,                    // select  : address match only
                                   1'b0,                    // timing  : match before execution
                                   2'b00,                   // sizelo  : match any access
                                   4'h1,                    // action  : enter debug mode
                                   1'b0,                    // chain   : not supported
                                   4'h0,                    // match   : simple match
                                   1'b1,                    // m       : match in m-mode
                                   1'b0,                    // 0       : zero
                                   1'b0,                    // s       : not supported
                                   1'b1,                    // u       : match in u-mode
                                   selected_tmatch_control, // execute : match instruction address
                                   1'b0,                    // store   : not supported
                                   1'b0};                   // load    : not supported

    // TDATA1 - address match value only
    assign tmatch_value_rdata = selected_tmatch_value;

    // Breakpoint matching
    // We match against the next address, as the breakpoint must be taken before execution
    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_trigger_match
      assign trigger_match[i] = tmatch_control_q[i] & (pc_if_i[31:0] == tmatch_value_q[i]);
    end
    assign trigger_match_o = |trigger_match;

  end else begin : gen_no_trigger_regs
    assign tselect_rdata        = 'b0;
    assign tmatch_control_rdata = 'b0;
    assign tmatch_value_rdata   = 'b0;
    assign trigger_match_o      = 'b0;
  end

  //////////////////////////
  // CPU control register //
  //////////////////////////

  // Cast register write data
  assign cpuctrl_wdata = cpu_ctrl_t'(csr_wdata_int[$bits(cpu_ctrl_t)-1:0]);

  // Generate fixed time execution bit
  if (DataIndTiming) begin : gen_dit
    assign cpuctrl_d.data_ind_timing = cpuctrl_wdata.data_ind_timing;

  end else begin : gen_no_dit
    // tieoff for the unused bit
    logic unused_dit;
    assign unused_dit = cpuctrl_wdata.data_ind_timing;

    // field will always read as zero if not configured
    assign cpuctrl_d.data_ind_timing = 1'b0;
  end

  assign data_ind_timing_o = cpuctrl_q.data_ind_timing;

  // Generate dummy instruction signals
  if (DummyInstructions) begin : gen_dummy
    assign cpuctrl_d.dummy_instr_en   = cpuctrl_wdata.dummy_instr_en;
    assign cpuctrl_d.dummy_instr_mask = cpuctrl_wdata.dummy_instr_mask;

    // Signal a write to the seed register
    assign dummy_instr_seed_en_o = csr_we_int && (csr_addr == CSR_SECURESEED);
    assign dummy_instr_seed_o    = csr_wdata_int;

  end else begin : gen_no_dummy
    // tieoff for the unused bit
    logic       unused_dummy_en;
    logic [2:0] unused_dummy_mask;
    assign unused_dummy_en   = cpuctrl_wdata.dummy_instr_en;
    assign unused_dummy_mask = cpuctrl_wdata.dummy_instr_mask;

    // field will always read as zero if not configured
    assign cpuctrl_d.dummy_instr_en   = 1'b0;
    assign cpuctrl_d.dummy_instr_mask = 3'b000;
    assign dummy_instr_seed_en_o      = 1'b0;
    assign dummy_instr_seed_o         = '0;
  end

  assign dummy_instr_en_o   = cpuctrl_q.dummy_instr_en;
  assign dummy_instr_mask_o = cpuctrl_q.dummy_instr_mask;

  // Generate icache enable bit
  if (ICache) begin : gen_icache_enable
    assign cpuctrl_d.icache_enable = cpuctrl_wdata.icache_enable;
  end else begin : gen_no_icache
    // tieoff for the unused icen bit
    logic unused_icen;
    assign unused_icen = cpuctrl_wdata.icache_enable;

    // icen field will always read as zero if ICache not configured
    assign cpuctrl_d.icache_enable = 1'b0;
  end

  assign icache_enable_o = cpuctrl_q.icache_enable;

  ibex_csr #(
    .Width      ($bits(cpu_ctrl_t)),
    .ShadowCopy (ShadowCSR),
    .ResetValue ('0)
  ) u_cpuctrl_csr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .wr_data_i  ({cpuctrl_d}),
    .wr_en_i    (cpuctrl_we),
    .rd_data_o  (cpuctrl_q),
    .rd_error_o (cpuctrl_err)
  );

  assign csr_shadow_err_o = mstatus_err | mtvec_err | pmp_csr_err | cpuctrl_err;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(IbexCsrOpEnRequiresAccess, csr_op_en_i |-> csr_access_i)

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control / status register primitive
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_csr #(
    parameter int unsigned    Width      = 32,
    parameter bit             ShadowCopy = 1'b0,
    parameter bit [Width-1:0] ResetValue = '0
 ) (
    input  logic             clk_i,
    input  logic             rst_ni,

    input  logic [Width-1:0] wr_data_i,
    input  logic             wr_en_i,
    output logic [Width-1:0] rd_data_o,

    output logic             rd_error_o
);

  logic [Width-1:0] rdata_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q <= ResetValue;
    end else if (wr_en_i) begin
      rdata_q <= wr_data_i;
    end
  end

  assign rd_data_o = rdata_q;

  if (ShadowCopy) begin : gen_shadow
    logic [Width-1:0] shadow_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        shadow_q <= ~ResetValue;
      end else if (wr_en_i) begin
        shadow_q <= ~wr_data_i;
      end
    end

    assign rd_error_o = rdata_q != ~shadow_q;

  end else begin : gen_no_shadow
    assign rd_error_o = 1'b0;
  end

  `ASSERT_KNOWN(IbexCSREnValid, wr_en_i)

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Instruction decoder
 *
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_decoder #(
    parameter bit RV32E               = 0,
    parameter ibex_pkg::rv32m_e RV32M = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone,
    parameter bit BranchTargetALU     = 0
) (
    input  logic                 clk_i,
    input  logic                 rst_ni,

    // to/from controller
    output logic                 illegal_insn_o,        // illegal instr encountered
    output logic                 ebrk_insn_o,           // trap instr encountered
    output logic                 mret_insn_o,           // return from exception instr
                                                        // encountered
    output logic                 dret_insn_o,           // return from debug instr encountered
    output logic                 ecall_insn_o,          // syscall instr encountered
    output logic                 wfi_insn_o,            // wait for interrupt instr encountered
    output logic                 jump_set_o,            // jump taken set signal
    input  logic                 branch_taken_i,        // registered branch decision
    output logic                 icache_inval_o,

    // from IF-ID pipeline register
    input  logic                 instr_first_cycle_i,   // instruction read is in its first cycle
    input  logic [31:0]          instr_rdata_i,         // instruction read from memory/cache
    input  logic [31:0]          instr_rdata_alu_i,     // instruction read from memory/cache
                                                        // replicated to ease fan-out)

    input  logic                 illegal_c_insn_i,      // compressed instruction decode failed

    // immediates
    output ibex_pkg::imm_a_sel_e  imm_a_mux_sel_o,       // immediate selection for operand a
    output ibex_pkg::imm_b_sel_e  imm_b_mux_sel_o,       // immediate selection for operand b
    output ibex_pkg::op_a_sel_e   bt_a_mux_sel_o,        // branch target selection operand a
    output ibex_pkg::imm_b_sel_e  bt_b_mux_sel_o,        // branch target selection operand b
    output logic [31:0]           imm_i_type_o,
    output logic [31:0]           imm_s_type_o,
    output logic [31:0]           imm_b_type_o,
    output logic [31:0]           imm_u_type_o,
    output logic [31:0]           imm_j_type_o,
    output logic [31:0]           zimm_rs1_type_o,

    // register file
    output ibex_pkg::rf_wd_sel_e rf_wdata_sel_o,   // RF write data selection
    output logic                 rf_we_o,          // write enable for regfile
    output logic [4:0]           rf_raddr_a_o,
    output logic [4:0]           rf_raddr_b_o,
    output logic [4:0]           rf_waddr_o,
    output logic                 rf_ren_a_o,          // Instruction reads from RF addr A
    output logic                 rf_ren_b_o,          // Instruction reads from RF addr B

    // ALU
    output ibex_pkg::alu_op_e    alu_operator_o,        // ALU operation selection
    output ibex_pkg::op_a_sel_e  alu_op_a_mux_sel_o,    // operand a selection: reg value, PC,
                                                        // immediate or zero
    output ibex_pkg::op_b_sel_e  alu_op_b_mux_sel_o,    // operand b selection: reg value or
                                                        // immediate
    output logic                 alu_multicycle_o,      // ternary bitmanip instruction

    // MULT & DIV
    output logic                 mult_en_o,             // perform integer multiplication
    output logic                 div_en_o,              // perform integer division or remainder
    output logic                 mult_sel_o,            // as above but static, for data muxes
    output logic                 div_sel_o,             // as above but static, for data muxes

    output ibex_pkg::md_op_e     multdiv_operator_o,
    output logic [1:0]           multdiv_signed_mode_o,

    // CSRs
    output logic                 csr_access_o,          // access to CSR
    output ibex_pkg::csr_op_e    csr_op_o,              // operation to perform on CSR

    // LSU
    output logic                 data_req_o,            // start transaction to data memory
    output logic                 data_we_o,             // write enable
    output logic [1:0]           data_type_o,           // size of transaction: byte, half
                                                        // word or word
    output logic                 data_sign_extension_o, // sign extension for data read from
                                                        // memory

    // jump/branches
    output logic                 jump_in_dec_o,         // jump is being calculated in ALU
    output logic                 branch_in_dec_o
);

  import ibex_pkg::*;

  logic        illegal_insn;
  logic        illegal_reg_rv32e;
  logic        csr_illegal;
  logic        rf_we;

  logic [31:0] instr;
  logic [31:0] instr_alu;
  logic [9:0]  unused_instr_alu;
  // Source/Destination register instruction index
  logic [4:0] instr_rs1;
  logic [4:0] instr_rs2;
  logic [4:0] instr_rs3;
  logic [4:0] instr_rd;

  logic        use_rs3_d;
  logic        use_rs3_q;

  csr_op_e     csr_op;

  opcode_e     opcode;
  opcode_e     opcode_alu;

  // To help timing the flops containing the current instruction are replicated to reduce fan-out.
  // instr_alu is used to determine the ALU control logic and associated operand/imm select signals
  // as the ALU is often on the more critical timing paths. instr is used for everything else.
  assign instr     = instr_rdata_i;
  assign instr_alu = instr_rdata_alu_i;

  //////////////////////////////////////
  // Register and immediate selection //
  //////////////////////////////////////

  // immediate extraction and sign extension
  assign imm_i_type_o = { {20{instr[31]}}, instr[31:20] };
  assign imm_s_type_o = { {20{instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_b_type_o = { {19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type_o = { instr[31:12], 12'b0 };
  assign imm_j_type_o = { {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulation (zero extended)
  assign zimm_rs1_type_o = { 27'b0, instr_rs1 }; // rs1

  if (RV32B != RV32BNone) begin : gen_rs3_flop
    // the use of rs3 is known one cycle ahead.
    always_ff  @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        use_rs3_q <= 1'b0;
      end else begin
        use_rs3_q <= use_rs3_d;
      end
    end
  end else begin : gen_no_rs3_flop
    logic unused_clk;
    logic unused_rst_n;

    // Clock and reset unused when there's no rs3 flop
    assign unused_clk = clk_i;
    assign unused_rst_n = rst_ni;

    // always zero
    assign use_rs3_q = use_rs3_d;
  end

  // source registers
  assign instr_rs1 = instr[19:15];
  assign instr_rs2 = instr[24:20];
  assign instr_rs3 = instr[31:27];
  assign rf_raddr_a_o = (use_rs3_q & ~instr_first_cycle_i) ? instr_rs3 : instr_rs1; // rs3 / rs1
  assign rf_raddr_b_o = instr_rs2; // rs2

  // destination register
  assign instr_rd = instr[11:7];
  assign rf_waddr_o   = instr_rd; // rd

  ////////////////////
  // Register check //
  ////////////////////
  if (RV32E) begin : gen_rv32e_reg_check_active
    assign illegal_reg_rv32e = ((rf_raddr_a_o[4] & (alu_op_a_mux_sel_o == OP_A_REG_A)) |
                                (rf_raddr_b_o[4] & (alu_op_b_mux_sel_o == OP_B_REG_B)) |
                                (rf_waddr_o[4]   & rf_we));
  end else begin : gen_rv32e_reg_check_inactive
    assign illegal_reg_rv32e = 1'b0;
  end

  ///////////////////////
  // CSR operand check //
  ///////////////////////
  always_comb begin : csr_operand_check
    csr_op_o = csr_op;

    // CSRRSI/CSRRCI must not write 0 to CSRs (uimm[4:0]=='0)
    // CSRRS/CSRRC must not write from x0 to CSRs (rs1=='0)
    if ((csr_op == CSR_OP_SET || csr_op == CSR_OP_CLEAR) &&
        instr_rs1 == '0) begin
      csr_op_o = CSR_OP_READ;
    end
  end

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    jump_in_dec_o         = 1'b0;
    jump_set_o            = 1'b0;
    branch_in_dec_o       = 1'b0;
    icache_inval_o        = 1'b0;

    multdiv_operator_o    = MD_OP_MULL;
    multdiv_signed_mode_o = 2'b00;

    rf_wdata_sel_o        = RF_WD_EX;
    rf_we                 = 1'b0;
    rf_ren_a_o            = 1'b0;
    rf_ren_b_o            = 1'b0;

    csr_access_o          = 1'b0;
    csr_illegal           = 1'b0;
    csr_op                = CSR_OP_READ;

    data_we_o             = 1'b0;
    data_type_o           = 2'b00;
    data_sign_extension_o = 1'b0;
    data_req_o            = 1'b0;

    illegal_insn          = 1'b0;
    ebrk_insn_o           = 1'b0;
    mret_insn_o           = 1'b0;
    dret_insn_o           = 1'b0;
    ecall_insn_o          = 1'b0;
    wfi_insn_o            = 1'b0;

    opcode                = opcode_e'(instr[6:0]);

    unique case (opcode)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin   // Jump and Link
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
      end

      OPCODE_JALR: begin  // Jump and Link Register
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
        if (instr[14:12] != 3'b0) begin
          illegal_insn = 1'b1;
        end

        rf_ren_a_o = 1'b1;
      end

      OPCODE_BRANCH: begin // Branch
        branch_in_dec_o       = 1'b1;
        // Check branch condition selection
        unique case (instr[14:12])
          3'b000,
          3'b001,
          3'b100,
          3'b101,
          3'b110,
          3'b111:  illegal_insn = 1'b0;
          default: illegal_insn = 1'b1;
        endcase

        rf_ren_a_o = 1'b1;
        rf_ren_b_o = 1'b1;
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        rf_ren_a_o         = 1'b1;
        rf_ren_b_o         = 1'b1;
        data_req_o         = 1'b1;
        data_we_o          = 1'b1;

        if (instr[14]) begin
          illegal_insn = 1'b1;
        end

        // store size
        unique case (instr[13:12])
          2'b00:   data_type_o  = 2'b10; // sb
          2'b01:   data_type_o  = 2'b01; // sh
          2'b10:   data_type_o  = 2'b00; // sw
          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_LOAD: begin
        rf_ren_a_o          = 1'b1;
        data_req_o          = 1'b1;
        data_type_o         = 2'b00;

        // sign/zero extension
        data_sign_extension_o = ~instr[14];

        // load size
        unique case (instr[13:12])
          2'b00: data_type_o = 2'b10; // lb(u)
          2'b01: data_type_o = 2'b01; // lh(u)
          2'b10: begin
            data_type_o = 2'b00;      // lw
            if (instr[14]) begin
              illegal_insn = 1'b1;    // lwu does not exist
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        rf_we            = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        rf_we            = 1'b1;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        rf_ren_a_o       = 1'b1;
        rf_we            = 1'b1;

        unique case (instr[14:12])
          3'b000,
          3'b010,
          3'b011,
          3'b100,
          3'b110,
          3'b111: illegal_insn = 1'b0;

          3'b001: begin
            unique case (instr[31:27])
              5'b0_0000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;        // slli
              5'b0_0100,                                                              // sloi
              5'b0_1001,                                                              // sbclri
              5'b0_0101,                                                              // sbseti
              5'b0_1101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;           // sbinvi
              5'b0_0001: if (instr[26] == 1'b0) begin
                illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1;                    // shfl
              end else begin
                illegal_insn = 1'b1;
              end
              5'b0_1100: begin
                unique case(instr[26:20])
                  7'b000_0000,                                                         // clz
                  7'b000_0001,                                                         // ctz
                  7'b000_0010,                                                         // pcnt
                  7'b000_0100,                                                         // sext.b
                  7'b000_0101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;      // sext.h
                  7'b001_0000,                                                         // crc32.b
                  7'b001_0001,                                                         // crc32.h
                  7'b001_0010,                                                         // crc32.w
                  7'b001_1000,                                                         // crc32c.b
                  7'b001_1001,                                                         // crc32c.h
                  7'b001_1010: illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1;      // crc32c.w

                  default: illegal_insn = 1'b1;
                endcase
              end
              default : illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            if (instr[26]) begin
              illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;                       // fsri
            end else begin
              unique case (instr[31:27])
                5'b0_0000,                                                             // srli
                5'b0_1000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;       // srai

                5'b0_0100,                                                             // sroi
                5'b0_1100,                                                             // rori
                5'b0_1001: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;          // sbexti

                5'b0_1101: begin
                  if ((RV32B == RV32BFull)) begin
                    illegal_insn = 1'b0;                                               // grevi
                  end else begin
                    unique case (instr[24:20])
                      5'b11111,                                                        // rev
                      5'b11000: illegal_insn = (RV32B == RV32BBalanced) ? 1'b0 : 1'b1; // rev8

                      default: illegal_insn = 1'b1;
                    endcase
                  end
                end
                5'b0_0101: begin
                  if ((RV32B == RV32BFull)) begin
                    illegal_insn = 1'b0;                                              // gorci
                  end else if (instr[24:20] == 5'b00111) begin
                    illegal_insn = (RV32B == RV32BBalanced) ? 1'b0 : 1'b1;            // orc.b
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end
                5'b0_0001: begin
                  if (instr[26] == 1'b0) begin
                    illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1;                // unshfl
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end

                default: illegal_insn = 1'b1;
              endcase
            end
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        rf_ren_a_o      = 1'b1;
        rf_ren_b_o      = 1'b1;
        rf_we           = 1'b1;
        if ({instr[26], instr[13:12]} == {1'b1, 2'b01}) begin
          illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // cmix / cmov / fsl / fsr
        end else begin
          unique case ({instr[31:25], instr[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000},
            {7'b010_0000, 3'b000},
            {7'b000_0000, 3'b010},
            {7'b000_0000, 3'b011},
            {7'b000_0000, 3'b100},
            {7'b000_0000, 3'b110},
            {7'b000_0000, 3'b111},
            {7'b000_0000, 3'b001},
            {7'b000_0000, 3'b101},
            {7'b010_0000, 3'b101}: illegal_insn = 1'b0;

            // RV32B zbb
            {7'b010_0000, 3'b111}, // andn
            {7'b010_0000, 3'b110}, // orn
            {7'b010_0000, 3'b100}, // xnor
            {7'b001_0000, 3'b001}, // slo
            {7'b001_0000, 3'b101}, // sro
            {7'b011_0000, 3'b001}, // rol
            {7'b011_0000, 3'b101}, // ror
            {7'b000_0101, 3'b100}, // min
            {7'b000_0101, 3'b101}, // max
            {7'b000_0101, 3'b110}, // minu
            {7'b000_0101, 3'b111}, // maxu
            {7'b000_0100, 3'b100}, // pack
            {7'b010_0100, 3'b100}, // packu
            {7'b000_0100, 3'b111}, // packh
            // RV32B zbs
            {7'b010_0100, 3'b001}, // sbclr
            {7'b001_0100, 3'b001}, // sbset
            {7'b011_0100, 3'b001}, // sbinv
            {7'b010_0100, 3'b101}, // sbext
            // RV32B zbf
            {7'b010_0100, 3'b111}: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // bfp
            // RV32B zbe
            {7'b010_0100, 3'b110}, // bdep
            {7'b000_0100, 3'b110}, // bext
            // RV32B zbp
            {7'b011_0100, 3'b101}, // grev
            {7'b001_0100, 3'b101}, // gorc
            {7'b000_0100, 3'b001}, // shfl
            {7'b000_0100, 3'b101}, // unshfl
            // RV32B zbc
            {7'b000_0101, 3'b001}, // clmul
            {7'b000_0101, 3'b010}, // clmulr
            {7'b000_0101, 3'b011}: illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1; // clmulh

            // RV32M instructions
            {7'b000_0001, 3'b000}: begin // mul
              multdiv_operator_o    = MD_OP_MULL;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b01;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b100}: begin // div
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b101}: begin // divu
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b110}: begin // rem
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b111}: begin // remu
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            rf_we           = 1'b0;
          end
          3'b001: begin
            // FENCE.I is implemented as a jump to the next PC, this gives the required flushing
            // behaviour (iside prefetch buffer flushed and response to any outstanding iside
            // requests will be ignored).
            // If present, the ICache will also be flushed.
            jump_in_dec_o   = 1'b1;

            rf_we           = 1'b0;

            if (instr_first_cycle_i) begin
              jump_set_o       = 1'b1;
              icache_inval_o   = 1'b1;
            end
          end
          default: begin
            illegal_insn       = 1'b1;
          end
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          unique case (instr[31:20])
            12'h000:  // ECALL
              // environment (system) call
              ecall_insn_o = 1'b1;

            12'h001:  // ebreak
              // debugger trap
              ebrk_insn_o = 1'b1;

            12'h302:  // mret
              mret_insn_o = 1'b1;

            12'h7b2:  // dret
              dret_insn_o = 1'b1;

            12'h105:  // wfi
              wfi_insn_o = 1'b1;

            default:
              illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (instr_rs1 != 5'b0 || instr_rd != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          // instruction to read/modify CSR
          csr_access_o     = 1'b1;
          rf_wdata_sel_o   = RF_WD_CSR;
          rf_we            = 1'b1;

          if (~instr[14]) begin
            rf_ren_a_o         = 1'b1;
          end

          unique case (instr[13:12])
            2'b01:   csr_op = CSR_OP_WRITE;
            2'b10:   csr_op = CSR_OP_SET;
            2'b11:   csr_op = CSR_OP_CLEAR;
            default: csr_illegal = 1'b1;
          endcase

          illegal_insn = csr_illegal;
        end

      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase

    // make sure illegal compressed instructions cause illegal instruction exceptions
    if (illegal_c_insn_i) begin
      illegal_insn = 1'b1;
    end

    // make sure illegal instructions detected in the decoder do not propagate from decoder
    // into register file, LSU, EX, WB, CSRs, PC
    // NOTE: instructions can also be detected to be illegal inside the CSRs (upon accesses with
    // insufficient privileges), or when accessing non-available registers in RV32E,
    // these cases are not handled here
    if (illegal_insn) begin
      rf_we           = 1'b0;
      data_req_o      = 1'b0;
      data_we_o       = 1'b0;
      jump_in_dec_o   = 1'b0;
      jump_set_o      = 1'b0;
      branch_in_dec_o = 1'b0;
      csr_access_o    = 1'b0;
    end
  end

  /////////////////////////////
  // Decoder for ALU control //
  /////////////////////////////

  always_comb begin
    alu_operator_o     = ALU_SLTU;
    alu_op_a_mux_sel_o = OP_A_IMM;
    alu_op_b_mux_sel_o = OP_B_IMM;

    imm_a_mux_sel_o    = IMM_A_ZERO;
    imm_b_mux_sel_o    = IMM_B_I;

    bt_a_mux_sel_o     = OP_A_CURRPC;
    bt_b_mux_sel_o     = IMM_B_I;


    opcode_alu         = opcode_e'(instr_alu[6:0]);

    use_rs3_d          = 1'b0;
    alu_multicycle_o   = 1'b0;
    mult_sel_o         = 1'b0;
    div_sel_o          = 1'b0;

    unique case (opcode_alu)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin // Jump and Link
        if (BranchTargetALU) begin
          bt_a_mux_sel_o = OP_A_CURRPC;
          bt_b_mux_sel_o = IMM_B_J;
        end

        // Jumps take two cycles without the BTALU
        if (instr_first_cycle_i && !BranchTargetALU) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_J;
          alu_operator_o      = ALU_ADD;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        end
      end

      OPCODE_JALR: begin // Jump and Link Register
        if (BranchTargetALU) begin
          bt_a_mux_sel_o = OP_A_REG_A;
          bt_b_mux_sel_o = IMM_B_I;
        end

        // Jumps take two cycles without the BTALU
        if (instr_first_cycle_i && !BranchTargetALU) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_I;
          alu_operator_o      = ALU_ADD;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        end
      end

      OPCODE_BRANCH: begin // Branch
        // Check branch condition selection
        unique case (instr_alu[14:12])
          3'b000:  alu_operator_o = ALU_EQ;
          3'b001:  alu_operator_o = ALU_NE;
          3'b100:  alu_operator_o = ALU_LT;
          3'b101:  alu_operator_o = ALU_GE;
          3'b110:  alu_operator_o = ALU_LTU;
          3'b111:  alu_operator_o = ALU_GEU;
          default: ;
        endcase

        if (BranchTargetALU) begin
          bt_a_mux_sel_o = OP_A_CURRPC;
          // Not-taken branch will jump to next instruction (used in secure mode)
          bt_b_mux_sel_o = branch_taken_i ? IMM_B_B : IMM_B_INCR_PC;
        end

        // Without branch target ALU, a branch is a two-stage operation using the Main ALU in both
        // stages
        if (instr_first_cycle_i) begin
          // First evaluate the branch condition
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_REG_B;
        end else if (!BranchTargetALU) begin
          // Then calculate jump target
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          // Not-taken branch will jump to next instruction (used in secure mode)
          imm_b_mux_sel_o     = branch_taken_i ? IMM_B_B : IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        end
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;
        alu_operator_o     = ALU_ADD;

        if (!instr_alu[14]) begin
          // offset from immediate
          imm_b_mux_sel_o     = IMM_B_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;
        end
      end

      OPCODE_LOAD: begin
        alu_op_a_mux_sel_o  = OP_A_REG_A;

        // offset from immediate
        alu_operator_o      = ALU_ADD;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMM_A_ZERO;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;

        unique case (instr_alu[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLT;  // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            if (RV32B != RV32BNone) begin
              unique case (instr_alu[31:27])
                5'b0_0000: alu_operator_o = ALU_SLL;    // Shift Left Logical by Immediate
                5'b0_0100: alu_operator_o = ALU_SLO;    // Shift Left Ones by Immediate
                5'b0_1001: alu_operator_o = ALU_SBCLR;  // Clear bit specified by immediate
                5'b0_0101: alu_operator_o = ALU_SBSET;  // Set bit specified by immediate
                5'b0_1101: alu_operator_o = ALU_SBINV;  // Invert bit specified by immediate.
                // Shuffle with Immediate Control Value
                5'b0_0001: if (instr_alu[26] == 0) alu_operator_o = ALU_SHFL;
                5'b0_1100: begin
                  unique case (instr_alu[26:20])
                    7'b000_0000: alu_operator_o = ALU_CLZ;   // clz
                    7'b000_0001: alu_operator_o = ALU_CTZ;   // ctz
                    7'b000_0010: alu_operator_o = ALU_PCNT;  // pcnt
                    7'b000_0100: alu_operator_o = ALU_SEXTB; // sext.b
                    7'b000_0101: alu_operator_o = ALU_SEXTH; // sext.h
                    7'b001_0000: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_B;  // crc32.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0001: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_H;  // crc32.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0010: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_W;  // crc32.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1000: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_B; // crc32c.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1001: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_H; // crc32c.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1010: begin
                      if (RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_W; // crc32c.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    default: ;
                  endcase
                end

                default: ;
              endcase
            end else begin
              alu_operator_o = ALU_SLL; // Shift Left Logical by Immediate
            end
          end

          3'b101: begin
            if (RV32B != RV32BNone) begin
              if (instr_alu[26] == 1'b1) begin
                alu_operator_o = ALU_FSR;
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end else begin
                unique case (instr_alu[31:27])
                  5'b0_0000: alu_operator_o = ALU_SRL;   // Shift Right Logical by Immediate
                  5'b0_1000: alu_operator_o = ALU_SRA;   // Shift Right Arithmetically by Immediate
                  5'b0_0100: alu_operator_o = ALU_SRO;   // Shift Right Ones by Immediate
                  5'b0_1001: alu_operator_o = ALU_SBEXT; // Extract bit specified by immediate.
                  5'b0_1100: begin
                    alu_operator_o = ALU_ROR;            // Rotate Right by Immediate
                    alu_multicycle_o = 1'b1;
                  end
                  5'b0_1101: alu_operator_o = ALU_GREV;  // General Reverse with Imm Control Val
                  5'b0_0101: alu_operator_o = ALU_GORC;  // General Or-combine with Imm Control Val
                  // Unshuffle with Immediate Control Value
                  5'b0_0001: begin
                    if (RV32B == RV32BFull) begin
                      if (instr_alu[26] == 1'b0) alu_operator_o = ALU_UNSHFL;
                    end
                  end
                  default: ;
                endcase
              end

            end else begin
              if (instr_alu[31:27] == 5'b0_0000) begin
                alu_operator_o = ALU_SRL;               // Shift Right Logical by Immediate
              end else if (instr_alu[31:27] == 5'b0_1000) begin
                alu_operator_o = ALU_SRA;               // Shift Right Arithmetically by Immediate
              end
            end
          end

          default: ;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;

        if (instr_alu[26]) begin
          if (RV32B != RV32BNone) begin
            unique case ({instr_alu[26:25], instr_alu[14:12]})
              {2'b11, 3'b001}: begin
                alu_operator_o   = ALU_CMIX; // cmix
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b11, 3'b101}: begin
                alu_operator_o   = ALU_CMOV; // cmov
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b001}: begin
                alu_operator_o   = ALU_FSL;  // fsl
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b101}: begin
                alu_operator_o   = ALU_FSR;  // fsr
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              default: ;
            endcase
          end
        end else begin
          unique case ({instr_alu[31:25], instr_alu[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {7'b010_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {7'b000_0000, 3'b010}: alu_operator_o = ALU_SLT;   // Set Lower Than
            {7'b000_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {7'b000_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {7'b000_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {7'b000_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {7'b000_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {7'b000_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {7'b010_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // RV32B ALU Operations
            {7'b001_0000, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_SLO;   // slo
            {7'b001_0000, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_SRO;   // sro
            {7'b011_0000, 3'b001}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROL;   // rol
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b011_0000, 3'b101}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROR;   // ror
                alu_multicycle_o = 1'b1;
              end
            end

            {7'b000_0101, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_MIN;    // min
            {7'b000_0101, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAX;    // max
            {7'b000_0101, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_MINU;   // minu
            {7'b000_0101, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAXU;   // maxu

            {7'b000_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACK;   // pack
            {7'b010_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKU;  // packu
            {7'b000_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKH;  // packh

            {7'b010_0000, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_XNOR;   // xnor
            {7'b010_0000, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_ORN;    // orn
            {7'b010_0000, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_ANDN;   // andn

            // RV32B zbs
            {7'b010_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_SBCLR;  // sbclr
            {7'b001_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_SBSET;  // sbset
            {7'b011_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_SBINV;  // sbinv
            {7'b010_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_SBEXT;  // sbext

            // RV32B zbf
            {7'b010_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_BFP;    // bfp

            // RV32B zbp
            {7'b011_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GREV;   // grev
            {7'b001_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GORC;   // grev
            {7'b000_0100, 3'b001}: if (RV32B == RV32BFull) alu_operator_o = ALU_SHFL;   // shfl
            {7'b000_0100, 3'b101}: if (RV32B == RV32BFull) alu_operator_o = ALU_UNSHFL; // unshfl

            // RV32B zbc
            {7'b000_0101, 3'b001}: if (RV32B == RV32BFull) alu_operator_o = ALU_CLMUL;  // clmul
            {7'b000_0101, 3'b010}: if (RV32B == RV32BFull) alu_operator_o = ALU_CLMULR; // clmulr
            {7'b000_0101, 3'b011}: if (RV32B == RV32BFull) alu_operator_o = ALU_CLMULH; // clmulh

            // RV32B zbe
            {7'b010_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BDEP;   // bdep
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b000_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BEXT;   // bext
                alu_multicycle_o = 1'b1;
              end
            end

            // RV32M instructions, all use the same ALU operation
            {7'b000_0001, 3'b000}: begin // mul
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b100}: begin // div
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b101}: begin // divu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b110}: begin // rem
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b111}: begin // remu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end

            default: ;
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr_alu[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            alu_operator_o     = ALU_ADD; // nop
            alu_op_a_mux_sel_o = OP_A_REG_A;
            alu_op_b_mux_sel_o = OP_B_IMM;
          end
          3'b001: begin
            // FENCE.I will flush the IF stage, prefetch buffer and ICache if present.
            if (BranchTargetALU) begin
              bt_a_mux_sel_o     = OP_A_CURRPC;
              bt_b_mux_sel_o     = IMM_B_INCR_PC;
            end else begin
              alu_op_a_mux_sel_o = OP_A_CURRPC;
              alu_op_b_mux_sel_o = OP_B_IMM;
              imm_b_mux_sel_o    = IMM_B_INCR_PC;
              alu_operator_o     = ALU_ADD;
            end
          end
          default: ;
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr_alu[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          alu_op_a_mux_sel_o = OP_A_REG_A;
          alu_op_b_mux_sel_o = OP_B_IMM;
        end else begin
          // instruction to read/modify CSR
          alu_op_b_mux_sel_o = OP_B_IMM;
          imm_a_mux_sel_o    = IMM_A_Z;
          imm_b_mux_sel_o    = IMM_B_I;  // CSR address is encoded in I imm

          if (instr_alu[14]) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            alu_op_a_mux_sel_o = OP_A_REG_A;
          end
        end

      end
      default: ;
    endcase
  end

  // do not enable multdiv in case of illegal instruction exceptions
  assign mult_en_o = illegal_insn ? 1'b0 : mult_sel_o;
  assign div_en_o  = illegal_insn ? 1'b0 : div_sel_o;

  // make sure instructions accessing non-available registers in RV32E cause illegal
  // instruction exceptions
  assign illegal_insn_o = illegal_insn | illegal_reg_rv32e;

  // do not propgate regfile write enable if non-available registers are accessed in RV32E
  assign rf_we_o = rf_we & ~illegal_reg_rv32e;

  // Not all bits are used
  assign unused_instr_alu = {instr_alu[19:15],instr_alu[11:7]};

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexRegImmAluOpKnown, (opcode == OPCODE_OP_IMM) |->
      !$isunknown(instr[14:12]))
endmodule // controller
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Dummy instruction module
 *
 * Provides pseudo-randomly inserted fake instructions for secure code obfuscation
 */

module ibex_dummy_instr import ibex_pkg::*; #(
    parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault
) (
    // Clock and reset
    input  logic        clk_i,
    input  logic        rst_ni,

    // Interface to CSRs
    input  logic        dummy_instr_en_i,
    input  logic [2:0]  dummy_instr_mask_i,
    input  logic        dummy_instr_seed_en_i,
    input  logic [31:0] dummy_instr_seed_i,

    // Interface to IF stage
    input  logic        fetch_valid_i,
    input  logic        id_in_ready_i,
    output logic        insert_dummy_instr_o,
    output logic [31:0] dummy_instr_data_o
);

  localparam int unsigned TIMEOUT_CNT_W = 5;
  localparam int unsigned OP_W          = 5;

  typedef enum logic [1:0] {
    DUMMY_ADD = 2'b00,
    DUMMY_MUL = 2'b01,
    DUMMY_DIV = 2'b10,
    DUMMY_AND = 2'b11
  } dummy_instr_e;

  typedef struct packed {
    dummy_instr_e             instr_type;
    logic [OP_W-1:0]          op_b;
    logic [OP_W-1:0]          op_a;
    logic [TIMEOUT_CNT_W-1:0] cnt;
  } lfsr_data_t;
  localparam int unsigned LFSR_OUT_W = $bits(lfsr_data_t);

  lfsr_data_t               lfsr_data;
  logic [TIMEOUT_CNT_W-1:0] dummy_cnt_incr, dummy_cnt_threshold;
  logic [TIMEOUT_CNT_W-1:0] dummy_cnt_d, dummy_cnt_q;
  logic                     dummy_cnt_en;
  logic                     lfsr_en;
  logic [LFSR_OUT_W-1:0]    lfsr_state;
  logic                     insert_dummy_instr;
  logic [6:0]               dummy_set;
  logic [2:0]               dummy_opcode;
  logic [31:0]              dummy_instr;
  logic [31:0]              dummy_instr_seed_q, dummy_instr_seed_d;

  // Shift the LFSR every time we insert an instruction
  assign lfsr_en = insert_dummy_instr & id_in_ready_i;

  assign dummy_instr_seed_d = dummy_instr_seed_q ^ dummy_instr_seed_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dummy_instr_seed_q <= '0;
    end else if (dummy_instr_seed_en_i) begin
      dummy_instr_seed_q <= dummy_instr_seed_d;
    end
  end

  prim_lfsr #(
      .LfsrDw      ( LfsrWidth       ),
      .StateOutDw  ( LFSR_OUT_W      ),
      .DefaultSeed ( RndCnstLfsrSeed ),
      .StatePermEn ( 1'b1            ),
      .StatePerm   ( RndCnstLfsrPerm )
  ) lfsr_i (
      .clk_i     ( clk_i                 ),
      .rst_ni    ( rst_ni                ),
      .seed_en_i ( dummy_instr_seed_en_i ),
      .seed_i    ( dummy_instr_seed_d    ),
      .lfsr_en_i ( lfsr_en               ),
      .entropy_i ( '0                    ),
      .state_o   ( lfsr_state            )
  );

  // Extract fields from LFSR
  assign lfsr_data = lfsr_data_t'(lfsr_state);

  // Set count threshold for inserting a new instruction. This is the pseudo-random value from the
  // LFSR with a mask applied (based on CSR config data) to shorten the period if required.
  assign dummy_cnt_threshold = lfsr_data.cnt & {dummy_instr_mask_i,{TIMEOUT_CNT_W-3{1'b1}}};
  assign dummy_cnt_incr      = dummy_cnt_q + {{TIMEOUT_CNT_W-1{1'b0}},1'b1};
  // Clear the counter everytime a new instruction is inserted
  assign dummy_cnt_d         = insert_dummy_instr ? '0 : dummy_cnt_incr;
  // Increment the counter for each executed instruction while dummy instuctions are
  // enabled.
  assign dummy_cnt_en        = dummy_instr_en_i & id_in_ready_i &
                               (fetch_valid_i | insert_dummy_instr);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dummy_cnt_q <= '0;
    end else if (dummy_cnt_en) begin
      dummy_cnt_q <= dummy_cnt_d;
    end
  end

  // Insert a dummy instruction each time the counter hits the threshold
  assign insert_dummy_instr = dummy_instr_en_i & (dummy_cnt_q == dummy_cnt_threshold);

  // Encode instruction
  always_comb begin
    unique case (lfsr_data.instr_type)
      DUMMY_ADD : begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b000;
      end
      DUMMY_MUL : begin
        dummy_set    = 7'b0000001;
        dummy_opcode = 3'b000;
      end
      DUMMY_DIV : begin
        dummy_set    = 7'b0000001;
        dummy_opcode = 3'b100;
      end
      DUMMY_AND : begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b111;
      end
      default : begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b000;
      end
    endcase
  end

  //                    SET       RS2            RS1            OP           RD
  assign dummy_instr = {dummy_set,lfsr_data.op_b,lfsr_data.op_a,dummy_opcode,5'h00,7'h33};

  // Assign outputs
  assign insert_dummy_instr_o = insert_dummy_instr;
  assign dummy_instr_data_o   = dummy_instr;

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Execution stage
 *
 * Execution block: Hosts ALU and MUL/DIV unit
 */
module ibex_ex_block #(
    parameter ibex_pkg::rv32m_e RV32M           = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e RV32B           = ibex_pkg::RV32BNone,
    parameter bit               BranchTargetALU = 0
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    // ALU
    input  ibex_pkg::alu_op_e     alu_operator_i,
    input  logic [31:0]           alu_operand_a_i,
    input  logic [31:0]           alu_operand_b_i,
    input  logic                  alu_instr_first_cycle_i,

    // Branch Target ALU
    // All of these signals are unusued when BranchTargetALU == 0
    input  logic [31:0]           bt_a_operand_i,
    input  logic [31:0]           bt_b_operand_i,

    // Multiplier/Divider
    input  ibex_pkg::md_op_e      multdiv_operator_i,
    input  logic                  mult_en_i,             // dynamic enable signal, for FSM control
    input  logic                  div_en_i,              // dynamic enable signal, for FSM control
    input  logic                  mult_sel_i,            // static decoder output, for data muxes
    input  logic                  div_sel_i,             // static decoder output, for data muxes
    input  logic  [1:0]           multdiv_signed_mode_i,
    input  logic [31:0]           multdiv_operand_a_i,
    input  logic [31:0]           multdiv_operand_b_i,
    input  logic                  multdiv_ready_id_i,
    input  logic                  data_ind_timing_i,

    // intermediate val reg
    output logic [1:0]            imd_val_we_o,
    output logic [33:0]           imd_val_d_o[2],
    input  logic [33:0]           imd_val_q_i[2],

    // Outputs
    output logic [31:0]           alu_adder_result_ex_o, // to LSU
    output logic [31:0]           result_ex_o,
    output logic [31:0]           branch_target_o,       // to IF
    output logic                  branch_decision_o,     // to ID

    output logic                  ex_valid_o             // EX has valid output
);

  import ibex_pkg::*;

  logic [31:0] alu_result, multdiv_result;

  logic [32:0] multdiv_alu_operand_b, multdiv_alu_operand_a;
  logic [33:0] alu_adder_result_ext;
  logic        alu_cmp_result, alu_is_equal_result;
  logic        multdiv_valid;
  logic        multdiv_sel;
  logic [31:0] alu_imd_val_q[2];
  logic [31:0] alu_imd_val_d[2];
  logic [ 1:0] alu_imd_val_we;
  logic [33:0] multdiv_imd_val_d[2];
  logic [ 1:0] multdiv_imd_val_we;

  /*
    The multdiv_i output is never selected if RV32M=RV32MNone
    At synthesis time, all the combinational and sequential logic
    from the multdiv_i module are eliminated
  */
  if (RV32M != RV32MNone) begin : gen_multdiv_m
    assign multdiv_sel = mult_sel_i | div_sel_i;
  end else begin : gen_multdiv_no_m
    assign multdiv_sel = 1'b0;
  end

  // Intermediate Value Register Mux
  assign imd_val_d_o[0] = multdiv_sel ? multdiv_imd_val_d[0] : {2'b0, alu_imd_val_d[0]};
  assign imd_val_d_o[1] = multdiv_sel ? multdiv_imd_val_d[1] : {2'b0, alu_imd_val_d[1]};
  assign imd_val_we_o   = multdiv_sel ? multdiv_imd_val_we : alu_imd_val_we;

  assign alu_imd_val_q = '{imd_val_q_i[0][31:0], imd_val_q_i[1][31:0]};

  assign result_ex_o  = multdiv_sel ? multdiv_result : alu_result;

  // branch handling
  assign branch_decision_o  = alu_cmp_result;

  if (BranchTargetALU) begin : g_branch_target_alu
    logic [32:0] bt_alu_result;
    logic        unused_bt_carry;

    assign bt_alu_result   = bt_a_operand_i + bt_b_operand_i;

    assign unused_bt_carry = bt_alu_result[32];
    assign branch_target_o = bt_alu_result[31:0];
  end else begin : g_no_branch_target_alu
    // Unused bt_operand signals cause lint errors, this avoids them
    logic [31:0] unused_bt_a_operand, unused_bt_b_operand;

    assign unused_bt_a_operand = bt_a_operand_i;
    assign unused_bt_b_operand = bt_b_operand_i;

    assign branch_target_o = alu_adder_result_ex_o;
  end

  /////////
  // ALU //
  /////////

  ibex_alu #(
    .RV32B(RV32B)
  ) alu_i                  (
      .operator_i          ( alu_operator_i          ),
      .operand_a_i         ( alu_operand_a_i         ),
      .operand_b_i         ( alu_operand_b_i         ),
      .instr_first_cycle_i ( alu_instr_first_cycle_i ),
      .imd_val_q_i         ( alu_imd_val_q           ),
      .imd_val_we_o        ( alu_imd_val_we          ),
      .imd_val_d_o         ( alu_imd_val_d           ),
      .multdiv_operand_a_i ( multdiv_alu_operand_a   ),
      .multdiv_operand_b_i ( multdiv_alu_operand_b   ),
      .multdiv_sel_i       ( multdiv_sel             ),
      .adder_result_o      ( alu_adder_result_ex_o   ),
      .adder_result_ext_o  ( alu_adder_result_ext    ),
      .result_o            ( alu_result              ),
      .comparison_result_o ( alu_cmp_result          ),
      .is_equal_result_o   ( alu_is_equal_result     )
  );

  ////////////////
  // Multiplier //
  ////////////////

  if (RV32M == RV32MSlow) begin : gen_multdiv_slow
    ibex_multdiv_slow multdiv_i (
        .clk_i              ( clk_i                 ),
        .rst_ni             ( rst_ni                ),
        .mult_en_i          ( mult_en_i             ),
        .div_en_i           ( div_en_i              ),
        .mult_sel_i         ( mult_sel_i            ),
        .div_sel_i          ( div_sel_i             ),
        .operator_i         ( multdiv_operator_i    ),
        .signed_mode_i      ( multdiv_signed_mode_i ),
        .op_a_i             ( multdiv_operand_a_i   ),
        .op_b_i             ( multdiv_operand_b_i   ),
        .alu_adder_ext_i    ( alu_adder_result_ext  ),
        .alu_adder_i        ( alu_adder_result_ex_o ),
        .equal_to_zero_i    ( alu_is_equal_result   ),
        .data_ind_timing_i  ( data_ind_timing_i     ),
        .valid_o            ( multdiv_valid         ),
        .alu_operand_a_o    ( multdiv_alu_operand_a ),
        .alu_operand_b_o    ( multdiv_alu_operand_b ),
        .imd_val_q_i        ( imd_val_q_i           ),
        .imd_val_d_o        ( multdiv_imd_val_d     ),
        .imd_val_we_o       ( multdiv_imd_val_we    ),
        .multdiv_ready_id_i ( multdiv_ready_id_i    ),
        .multdiv_result_o   ( multdiv_result        )
    );
  end else if (RV32M == RV32MFast || RV32M == RV32MSingleCycle) begin : gen_multdiv_fast
    ibex_multdiv_fast #     (
        .RV32M ( RV32M )
    ) multdiv_i             (
        .clk_i              ( clk_i                 ),
        .rst_ni             ( rst_ni                ),
        .mult_en_i          ( mult_en_i             ),
        .div_en_i           ( div_en_i              ),
        .mult_sel_i         ( mult_sel_i            ),
        .div_sel_i          ( div_sel_i             ),
        .operator_i         ( multdiv_operator_i    ),
        .signed_mode_i      ( multdiv_signed_mode_i ),
        .op_a_i             ( multdiv_operand_a_i   ),
        .op_b_i             ( multdiv_operand_b_i   ),
        .alu_operand_a_o    ( multdiv_alu_operand_a ),
        .alu_operand_b_o    ( multdiv_alu_operand_b ),
        .alu_adder_ext_i    ( alu_adder_result_ext  ),
        .alu_adder_i        ( alu_adder_result_ex_o ),
        .equal_to_zero_i    ( alu_is_equal_result   ),
        .data_ind_timing_i  ( data_ind_timing_i     ),
        .imd_val_q_i        ( imd_val_q_i           ),
        .imd_val_d_o        ( multdiv_imd_val_d     ),
        .imd_val_we_o       ( multdiv_imd_val_we    ),
        .multdiv_ready_id_i ( multdiv_ready_id_i    ),
        .valid_o            ( multdiv_valid         ),
        .multdiv_result_o   ( multdiv_result        )
    );
  end

  // Multiplier/divider may require multiple cycles. The ALU output is valid in the same cycle
  // unless the intermediate result register is being written (which indicates this isn't the
  // final cycle of ALU operation).
  assign ex_valid_o = multdiv_sel ? multdiv_valid : ~(|alu_imd_val_we);

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch Fifo for 32 bit memory interface
 *
 * input port: send address and data to the FIFO
 * clear_i clears the FIFO for the following cycle, including any new request
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_fetch_fifo #(
  parameter int unsigned NUM_REQS = 2,
  parameter bit          ResetAll = 1'b0
) (
    input  logic                clk_i,
    input  logic                rst_ni,

    // control signals
    input  logic                clear_i,   // clears the contents of the FIFO
    output logic [NUM_REQS-1:0] busy_o,

    // input port
    input  logic                in_valid_i,
    input  logic [31:0]         in_addr_i,
    input  logic [31:0]         in_rdata_i,
    input  logic                in_err_i,

    // output port
    output logic                out_valid_o,
    input  logic                out_ready_i,
    output logic [31:0]         out_addr_o,
    output logic [31:0]         out_addr_next_o,
    output logic [31:0]         out_rdata_o,
    output logic                out_err_o,
    output logic                out_err_plus2_o
);

  localparam int unsigned DEPTH = NUM_REQS+1;

  // index 0 is used for output
  logic [DEPTH-1:0] [31:0]  rdata_d,   rdata_q;
  logic [DEPTH-1:0]         err_d,     err_q;
  logic [DEPTH-1:0]         valid_d,   valid_q;
  logic [DEPTH-1:0]         lowest_free_entry;
  logic [DEPTH-1:0]         valid_pushed, valid_popped;
  logic [DEPTH-1:0]         entry_en;

  logic                     pop_fifo;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     err,   err_unaligned, err_plus2;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;

  logic                     addr_incr_two;
  logic [31:1]              instr_addr_next;
  logic [31:1]              instr_addr_d, instr_addr_q;
  logic                     instr_addr_en;
  logic                     unused_addr_in;

  /////////////////
  // Output port //
  /////////////////

  assign rdata = valid_q[0] ? rdata_q[0] : in_rdata_i;
  assign err   = valid_q[0] ? err_q[0]   : in_err_i;
  assign valid = valid_q[0] | in_valid_i;

  // The FIFO contains word aligned memory fetches, but the instructions contained in each entry
  // might be half-word aligned (due to compressed instructions)
  // e.g.
  //              | 31               16 | 15               0 |
  // FIFO entry 0 | Instr 1 [15:0]      | Instr 0 [15:0]     |
  // FIFO entry 1 | Instr 2 [15:0]      | Instr 1 [31:16]    |
  //
  // The FIFO also has a direct bypass path, so a complete instruction might be made up of data
  // from the FIFO and new incoming data.
  //

  // Construct the output data for an unaligned instruction
  assign rdata_unaligned = valid_q[1] ? {rdata_q[1][15:0], rdata[31:16]} :
                                        {in_rdata_i[15:0], rdata[31:16]};

  // If entry[1] is valid, an error can come from entry[0] or entry[1], unless the
  // instruction in entry[0] is compressed (entry[1] is a new instruction)
  // If entry[1] is not valid, and entry[0] is, an error can come from entry[0] or the incoming
  // data, unless the instruction in entry[0] is compressed
  // If entry[0] is not valid, the error must come from the incoming data
  assign err_unaligned   = valid_q[1] ? ((err_q[1] & ~unaligned_is_compressed) | err_q[0]) :
                                        ((valid_q[0] & err_q[0]) |
                                         (in_err_i & (~valid_q[0] | ~unaligned_is_compressed)));

  // Record when an error is caused by the second half of an unaligned 32bit instruction.
  // Only needs to be correct when unaligned and if err_unaligned is set
  assign err_plus2       = valid_q[1] ? (err_q[1] & ~err_q[0]) :
                                        (in_err_i & valid_q[0] & ~err_q[0]);

  // An uncompressed unaligned instruction is only valid if both parts are available
  assign valid_unaligned = valid_q[1] ? 1'b1 :
                                        (valid_q[0] & in_valid_i);

  // If there is an error, rdata is unknown
  assign unaligned_is_compressed = (rdata[17:16] != 2'b11) & ~err;
  assign aligned_is_compressed   = (rdata[ 1: 0] != 2'b11) & ~err;

  ////////////////////////////////////////
  // Instruction aligner (if unaligned) //
  ////////////////////////////////////////

  always_comb begin
    if (out_addr_o[1]) begin
      // unaligned case
      out_rdata_o     = rdata_unaligned;
      out_err_o       = err_unaligned;
      out_err_plus2_o = err_plus2;

      if (unaligned_is_compressed) begin
        out_valid_o = valid;
      end else begin
        out_valid_o = valid_unaligned;
      end
    end else begin
      // aligned case
      out_rdata_o     = rdata;
      out_err_o       = err;
      out_err_plus2_o = 1'b0;
      out_valid_o     = valid;
    end
  end

  /////////////////////////
  // Instruction address //
  /////////////////////////

  // Update the address on branches and every time an instruction is driven
  assign instr_addr_en = clear_i | (out_ready_i & out_valid_o);

  // Increment the address by two every time a compressed instruction is popped
  assign addr_incr_two = instr_addr_q[1] ? unaligned_is_compressed :
                                           aligned_is_compressed;

  assign instr_addr_next = (instr_addr_q[31:1] +
                            // Increment address by 4 or 2
                            {29'd0,~addr_incr_two,addr_incr_two});

  assign instr_addr_d = clear_i ? in_addr_i[31:1] :
                                  instr_addr_next;

  if (ResetAll) begin : g_instr_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_addr_q <= '0;
      end else if (instr_addr_en) begin
        instr_addr_q <= instr_addr_d;
      end
    end
  end else begin : g_instr_addr_nr
    always_ff @(posedge clk_i) begin
      if (instr_addr_en) begin
        instr_addr_q <= instr_addr_d;
      end
    end
  end

  // Output both PC of current instruction and instruction following. PC of instruction following is
  // required for the branch predictor. It's used to fetch the instruction following a branch that
  // was not-taken but (mis)predicted taken.
  assign out_addr_next_o = {instr_addr_next, 1'b0};
  assign out_addr_o      = {instr_addr_q, 1'b0};

  // The LSB of the address is unused, since all addresses are halfword aligned
  assign unused_addr_in = in_addr_i[0];

  /////////////////
  // FIFO status //
  /////////////////

  // Indicate the fill level of fifo-entries. This is used to determine when a new request can be
  // made on the bus. The prefetch buffer only needs to know about the upper entries which overlap
  // with NUM_REQS.
  assign busy_o = valid_q[DEPTH-1:DEPTH-NUM_REQS];

  /////////////////////
  // FIFO management //
  /////////////////////

  // Since an entry can contain unaligned instructions, popping an entry can leave the entry valid
  assign pop_fifo = out_ready_i & out_valid_o & (~aligned_is_compressed | out_addr_o[1]);

  for (genvar i = 0; i < (DEPTH - 1); i++) begin : g_fifo_next
    // Calculate lowest free entry (write pointer)
    if (i == 0) begin : g_ent0
      assign lowest_free_entry[i] = ~valid_q[i];
    end else begin : g_ent_others
      assign lowest_free_entry[i] = ~valid_q[i] & valid_q[i-1];
    end

    // An entry is set when an incoming request chooses the lowest available entry
    assign valid_pushed[i] = (in_valid_i & lowest_free_entry[i]) |
                             valid_q[i];
    // Popping the FIFO shifts all entries down
    assign valid_popped[i] = pop_fifo ? valid_pushed[i+1] : valid_pushed[i];
    // All entries are wiped out on a clear
    assign valid_d[i] = valid_popped[i] & ~clear_i;

    // data flops are enabled if there is new data to shift into it, or
    assign entry_en[i] = (valid_pushed[i+1] & pop_fifo) |
                         // a new request is incoming and this is the lowest free entry
                         (in_valid_i & lowest_free_entry[i] & ~pop_fifo);

    // take the next entry or the incoming data
    assign rdata_d[i]  = valid_q[i+1] ? rdata_q[i+1] : in_rdata_i;
    assign err_d  [i]  = valid_q[i+1] ? err_q  [i+1] : in_err_i;
  end
  // The top entry is similar but with simpler muxing
  assign lowest_free_entry[DEPTH-1] = ~valid_q[DEPTH-1] & valid_q[DEPTH-2];
  assign valid_pushed     [DEPTH-1] = valid_q[DEPTH-1] | (in_valid_i & lowest_free_entry[DEPTH-1]);
  assign valid_popped     [DEPTH-1] = pop_fifo ? 1'b0 : valid_pushed[DEPTH-1];
  assign valid_d [DEPTH-1]          = valid_popped[DEPTH-1] & ~clear_i;
  assign entry_en[DEPTH-1]          = in_valid_i & lowest_free_entry[DEPTH-1];
  assign rdata_d [DEPTH-1]          = in_rdata_i;
  assign err_d   [DEPTH-1]          = in_err_i;

  ////////////////////
  // FIFO registers //
  ////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= '0;
    end else begin
      valid_q <= valid_d;
    end
  end

  for (genvar i = 0; i < DEPTH; i++) begin : g_fifo_regs
    if (ResetAll) begin : g_rdata_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rdata_q[i] <= '0;
          err_q[i]   <= '0;
        end else if (entry_en[i]) begin
          rdata_q[i] <= rdata_d[i];
          err_q[i]   <= err_d[i];
        end
      end
    end else begin : g_rdata_nr
      always_ff @(posedge clk_i) begin
        if (entry_en[i]) begin
          rdata_q[i] <= rdata_d[i];
          err_q[i]   <= err_d[i];
        end
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Must not push and pop simultaneously when FIFO full.
  `ASSERT(IbexFetchFifoPushPopFull,
      (in_valid_i && pop_fifo) |-> (!valid_q[DEPTH-1] || clear_i))

  // Must not push to FIFO when full.
  `ASSERT(IbexFetchFifoPushFull,
      (in_valid_i) |-> (!valid_q[DEPTH-1] || clear_i))

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Instruction cache
 *
 * Provides an instruction cache along with cache management, instruction buffering and prefetching
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_icache import ibex_pkg::*; #(
  parameter bit          BranchPredictor = 1'b0,
  parameter bit          ICacheECC       = 1'b0,
  parameter bit          ResetAll        = 1'b0,
  parameter int unsigned BusSizeECC      = BUS_SIZE,
  parameter int unsigned TagSizeECC      = IC_TAG_SIZE,
  parameter int unsigned LineSizeECC     = IC_LINE_SIZE,
  // Only cache branch targets
  parameter bit          BranchCache     = 1'b0
) (
    // Clock and reset
    input  logic                           clk_i,
    input  logic                           rst_ni,

    // Signal that the core would like instructions
    input  logic                           req_i,

    // Set the cache's address counter
    input  logic                           branch_i,
    input  logic                           branch_spec_i,
    input  logic                           predicted_branch_i,
    input  logic                           branch_mispredict_i,
    input  logic [31:0]                    addr_i,

    // IF stage interface: Pass fetched instructions to the core
    input  logic                           ready_i,
    output logic                           valid_o,
    output logic [31:0]                    rdata_o,
    output logic [31:0]                    addr_o,
    output logic                           err_o,
    output logic                           err_plus2_o,

    // Instruction memory / interconnect interface: Fetch instruction data from memory
    output logic                           instr_req_o,
    input  logic                           instr_gnt_i,
    output logic [31:0]                    instr_addr_o,
    input  logic [BUS_SIZE-1:0]            instr_rdata_i,
    input  logic                           instr_err_i,
    input  logic                           instr_pmp_err_i,
    input  logic                           instr_rvalid_i,

    // RAM IO
    output logic [IC_NUM_WAYS-1:0]         ic_tag_req_o,
    output logic                           ic_tag_write_o,
    output logic [IC_INDEX_W-1:0]          ic_tag_addr_o,
    output logic [TagSizeECC-1:0]          ic_tag_wdata_o,
    input  logic [TagSizeECC-1:0]          ic_tag_rdata_i [IC_NUM_WAYS],
    output logic [IC_NUM_WAYS-1:0]         ic_data_req_o,
    output logic                           ic_data_write_o,
    output logic [IC_INDEX_W-1:0]          ic_data_addr_o,
    output logic [LineSizeECC-1:0]         ic_data_wdata_o,
    input  logic [LineSizeECC-1:0]         ic_data_rdata_i [IC_NUM_WAYS],

    // Cache status
    input  logic                           icache_enable_i,
    input  logic                           icache_inval_i,
    output logic                           busy_o
);

  // Number of fill buffers (must be >= 2)
  localparam int unsigned NUM_FB        = 4;
  // Request throttling threshold
  localparam int unsigned FB_THRESHOLD  = NUM_FB - 2;

  // Prefetch signals
  logic [ADDR_W-1:0]                      lookup_addr_aligned;
  logic [ADDR_W-1:0]                      branch_mispredict_addr;
  logic [ADDR_W-1:0]                      prefetch_addr_d, prefetch_addr_q;
  logic                                   prefetch_addr_en;
  logic                                   branch_or_mispredict;
  // Cache pipelipe IC0 signals
  logic                                   branch_suppress;
  logic                                   lookup_throttle;
  logic                                   lookup_req_ic0;
  logic [ADDR_W-1:0]                      lookup_addr_ic0;
  logic [IC_INDEX_W-1:0]                  lookup_index_ic0;
  logic                                   fill_req_ic0;
  logic [IC_INDEX_W-1:0]                  fill_index_ic0;
  logic [IC_TAG_SIZE-1:0]                 fill_tag_ic0;
  logic [IC_LINE_SIZE-1:0]                fill_wdata_ic0;
  logic                                   lookup_grant_ic0;
  logic                                   lookup_actual_ic0;
  logic                                   fill_grant_ic0;
  logic                                   tag_req_ic0;
  logic [IC_INDEX_W-1:0]                  tag_index_ic0;
  logic [IC_NUM_WAYS-1:0]                 tag_banks_ic0;
  logic                                   tag_write_ic0;
  logic [TagSizeECC-1:0]                  tag_wdata_ic0;
  logic                                   data_req_ic0;
  logic [IC_INDEX_W-1:0]                  data_index_ic0;
  logic [IC_NUM_WAYS-1:0]                 data_banks_ic0;
  logic                                   data_write_ic0;
  logic [LineSizeECC-1:0]                 data_wdata_ic0;
  // Cache pipelipe IC1 signals
  logic [TagSizeECC-1:0]                  tag_rdata_ic1  [IC_NUM_WAYS];
  logic [LineSizeECC-1:0]                 data_rdata_ic1 [IC_NUM_WAYS];
  logic [LineSizeECC-1:0]                 hit_data_ecc_ic1;
  logic [IC_LINE_SIZE-1:0]                hit_data_ic1;
  logic                                   lookup_valid_ic1;
  logic [ADDR_W-1:IC_INDEX_HI+1]          lookup_addr_ic1;
  logic [IC_NUM_WAYS-1:0]                 tag_match_ic1;
  logic                                   tag_hit_ic1;
  logic [IC_NUM_WAYS-1:0]                 tag_invalid_ic1;
  logic [IC_NUM_WAYS-1:0]                 lowest_invalid_way_ic1;
  logic [IC_NUM_WAYS-1:0]                 round_robin_way_ic1, round_robin_way_q;
  logic [IC_NUM_WAYS-1:0]                 sel_way_ic1;
  logic                                   ecc_err_ic1;
  logic                                   ecc_write_req;
  logic [IC_NUM_WAYS-1:0]                 ecc_write_ways;
  logic [IC_INDEX_W-1:0]                  ecc_write_index;
  // Fill buffer signals
  logic                                   gnt_or_pmp_err, gnt_not_pmp_err;
  logic [$clog2(NUM_FB)-1:0]              fb_fill_level;
  logic                                   fill_cache_new;
  logic                                   fill_new_alloc;
  logic                                   fill_spec_req, fill_spec_done, fill_spec_hold;
  logic [NUM_FB-1:0][NUM_FB-1:0]          fill_older_d, fill_older_q;
  logic [NUM_FB-1:0]                      fill_alloc_sel, fill_alloc;
  logic [NUM_FB-1:0]                      fill_busy_d, fill_busy_q;
  logic [NUM_FB-1:0]                      fill_done;
  logic [NUM_FB-1:0]                      fill_in_ic1;
  logic [NUM_FB-1:0]                      fill_stale_d, fill_stale_q;
  logic [NUM_FB-1:0]                      fill_cache_d, fill_cache_q;
  logic [NUM_FB-1:0]                      fill_hit_ic1, fill_hit_d, fill_hit_q;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_ext_cnt_d, fill_ext_cnt_q;
  logic [NUM_FB-1:0]                      fill_ext_hold_d, fill_ext_hold_q;
  logic [NUM_FB-1:0]                      fill_ext_done_d, fill_ext_done_q;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_rvd_cnt_d, fill_rvd_cnt_q;
  logic [NUM_FB-1:0]                      fill_rvd_done;
  logic [NUM_FB-1:0]                      fill_ram_done_d, fill_ram_done_q;
  logic [NUM_FB-1:0]                      fill_out_grant;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_out_cnt_d, fill_out_cnt_q;
  logic [NUM_FB-1:0]                      fill_out_done;
  logic [NUM_FB-1:0]                      fill_ext_req, fill_rvd_exp, fill_ram_req, fill_out_req;
  logic [NUM_FB-1:0]                      fill_data_sel, fill_data_reg;
  logic [NUM_FB-1:0]                      fill_data_hit, fill_data_rvd;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W-1:0] fill_ext_off, fill_rvd_off;
  logic [NUM_FB-1:0][IC_LINE_BEATS_W:0]   fill_ext_beat, fill_rvd_beat;
  logic [NUM_FB-1:0]                      fill_ext_arb, fill_ram_arb, fill_out_arb;
  logic [NUM_FB-1:0]                      fill_rvd_arb;
  logic [NUM_FB-1:0]                      fill_entry_en;
  logic [NUM_FB-1:0]                      fill_addr_en;
  logic [NUM_FB-1:0]                      fill_way_en;
  logic [NUM_FB-1:0][IC_LINE_BEATS-1:0]   fill_data_en;
  logic [NUM_FB-1:0][IC_LINE_BEATS-1:0]   fill_err_d, fill_err_q;
  logic [ADDR_W-1:0]                      fill_addr_q [NUM_FB];
  logic [IC_NUM_WAYS-1:0]                 fill_way_q  [NUM_FB];
  logic [IC_LINE_SIZE-1:0]                fill_data_d [NUM_FB];
  logic [IC_LINE_SIZE-1:0]                fill_data_q [NUM_FB];
  logic [ADDR_W-1:BUS_W]                  fill_ext_req_addr;
  logic [ADDR_W-1:0]                      fill_ram_req_addr;
  logic [IC_NUM_WAYS-1:0]                 fill_ram_req_way;
  logic [IC_LINE_SIZE-1:0]                fill_ram_req_data;
  logic [IC_LINE_SIZE-1:0]                fill_out_data;
  logic [IC_LINE_BEATS-1:0]               fill_out_err;
  // External req signals
  logic                                   instr_req;
  logic [ADDR_W-1:BUS_W]                  instr_addr;
  // Data output signals
  logic                                   skid_complete_instr;
  logic                                   skid_ready;
  logic                                   output_compressed;
  logic                                   skid_valid_d, skid_valid_q, skid_en;
  logic [15:0]                            skid_data_d, skid_data_q;
  logic                                   skid_err_q;
  logic                                   output_valid;
  logic                                   addr_incr_two;
  logic                                   output_addr_en;
  logic [ADDR_W-1:1]                      output_addr_incr;
  logic [ADDR_W-1:1]                      output_addr_d, output_addr_q;
  logic [15:0]                            output_data_lo, output_data_hi;
  logic                                   data_valid, output_ready;
  logic [IC_LINE_SIZE-1:0]                line_data;
  logic [IC_LINE_BEATS-1:0]               line_err;
  logic [31:0]                            line_data_muxed;
  logic                                   line_err_muxed;
  logic [31:0]                            output_data;
  logic                                   output_err;
  // Invalidations
  logic                                   start_inval, inval_done;
  logic                                   reset_inval_q;
  logic                                   inval_prog_d, inval_prog_q;
  logic [IC_INDEX_W-1:0]                  inval_index_d, inval_index_q;

  //////////////////////////
  // Instruction prefetch //
  //////////////////////////

  if (BranchPredictor) begin : g_branch_predictor
    // Where the branch predictor is present record what address followed a predicted branch.  If
    // that branch is predicted taken but mispredicted (so not-taken) this is used to resume on
    // the not-taken code path.
    logic [31:0] branch_mispredict_addr_q;
    logic        branch_mispredict_addr_en;

    assign branch_mispredict_addr_en = branch_i & predicted_branch_i;

    if (ResetAll) begin : g_branch_misp_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          branch_mispredict_addr_q <= '0;
        end else if (branch_mispredict_addr_en) begin
          branch_mispredict_addr_q <= {output_addr_incr, 1'b0};
        end
      end
    end else begin : g_branch_misp_nr
      always_ff @(posedge clk_i) begin
        if (branch_mispredict_addr_en) begin
          branch_mispredict_addr_q <= {output_addr_incr, 1'b0};
        end
      end
    end

    assign branch_mispredict_addr = branch_mispredict_addr_q;

  end else begin : g_no_branch_predictor
    logic        unused_predicted_branch;

    assign unused_predicted_branch   = predicted_branch_i;

    assign branch_mispredict_addr = '0;
  end

  assign branch_or_mispredict = branch_i | branch_mispredict_i;

  assign lookup_addr_aligned = {lookup_addr_ic0[ADDR_W-1:IC_LINE_W], {IC_LINE_W{1'b0}}};

  // The prefetch address increments by one cache line for each granted request.
  // This address is also updated if there is a branch that is not granted, since the target
  // address (addr_i) is only valid for one cycle while branch_i is high.

  // The captured branch target address is not forced to be aligned since the offset in the cache
  // line must also be recorded for later use by the fill buffers.
  assign prefetch_addr_d     =
      lookup_grant_ic0 ? (lookup_addr_aligned +
                          {{ADDR_W-IC_LINE_W-1{1'b0}}, 1'b1, {IC_LINE_W{1'b0}}}) :
      branch_i         ? addr_i :
                         branch_mispredict_addr;

  assign prefetch_addr_en    = branch_or_mispredict | lookup_grant_ic0;

  if (ResetAll) begin : g_prefetch_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prefetch_addr_q <= '0;
      end else if (prefetch_addr_en) begin
        prefetch_addr_q <= prefetch_addr_d;
      end
    end
  end else begin : g_prefetch_addr_nr
    always_ff @(posedge clk_i) begin
      if (prefetch_addr_en) begin
        prefetch_addr_q <= prefetch_addr_d;
      end
    end
  end

  ////////////////////////
  // Pipeline stage IC0 //
  ////////////////////////

  // Cache lookup
  assign lookup_throttle  = (fb_fill_level > FB_THRESHOLD[$clog2(NUM_FB)-1:0]);

  assign lookup_req_ic0   = req_i & ~&fill_busy_q & (branch_or_mispredict | ~lookup_throttle) &
                            ~ecc_write_req;
  assign lookup_addr_ic0  = branch_spec_i       ? addr_i :
                            branch_mispredict_i ? branch_mispredict_addr :
                                                  prefetch_addr_q;
  assign lookup_index_ic0 = lookup_addr_ic0[IC_INDEX_HI:IC_LINE_W];

  // Cache write
  assign fill_req_ic0   = (|fill_ram_req);
  assign fill_index_ic0 = fill_ram_req_addr[IC_INDEX_HI:IC_LINE_W];
  assign fill_tag_ic0   = {(~inval_prog_q & ~ecc_write_req),
                           fill_ram_req_addr[ADDR_W-1:IC_INDEX_HI+1]};
  assign fill_wdata_ic0 = fill_ram_req_data;

  // Suppress a new lookup on a not-taken branch (as the address will be incorrect)
  assign branch_suppress   = branch_spec_i & ~branch_i;

  // Arbitrated signals - lookups have highest priority
  assign lookup_grant_ic0  = lookup_req_ic0 & ~branch_suppress;
  assign fill_grant_ic0    = fill_req_ic0 & (~lookup_req_ic0 | branch_suppress) & ~inval_prog_q &
                             ~ecc_write_req;
  // Qualified lookup grant to mask ram signals in IC1 if access was not made
  assign lookup_actual_ic0 = lookup_grant_ic0 & icache_enable_i & ~inval_prog_q & ~start_inval;

  // Tagram
  assign tag_req_ic0   = lookup_req_ic0 | fill_req_ic0 | inval_prog_q | ecc_write_req;
  assign tag_index_ic0 = inval_prog_q   ? inval_index_q :
                         ecc_write_req  ? ecc_write_index :
                         fill_grant_ic0 ? fill_index_ic0 :
                                          lookup_index_ic0;
  assign tag_banks_ic0 = ecc_write_req  ? ecc_write_ways :
                         fill_grant_ic0 ? fill_ram_req_way :
                                          {IC_NUM_WAYS{1'b1}};
  assign tag_write_ic0 = fill_grant_ic0 | inval_prog_q | ecc_write_req;

  // Dataram
  assign data_req_ic0   = lookup_req_ic0 | fill_req_ic0;
  assign data_index_ic0 = tag_index_ic0;
  assign data_banks_ic0 = tag_banks_ic0;
  assign data_write_ic0 = tag_write_ic0;

  // Append ECC checkbits to write data if required
  if (ICacheECC) begin : gen_ecc_wdata

    // Tagram ECC
    // Reuse the same ecc encoding module for larger cache sizes by padding with zeros
    logic [21:0]             tag_ecc_input_padded;
    logic [27:0]             tag_ecc_output_padded;
    logic [22-IC_TAG_SIZE:0] tag_ecc_output_unused;

    assign tag_ecc_input_padded  = {{22-IC_TAG_SIZE{1'b0}},fill_tag_ic0};
    assign tag_ecc_output_unused = tag_ecc_output_padded[21:IC_TAG_SIZE-1];

    prim_secded_28_22_enc tag_ecc_enc (
      .data_i (tag_ecc_input_padded),
      .data_o (tag_ecc_output_padded)
    );

    assign tag_wdata_ic0 = {tag_ecc_output_padded[27:22],tag_ecc_output_padded[IC_TAG_SIZE-1:0]};

    // Dataram ECC
    for (genvar bank = 0; bank < IC_LINE_BEATS; bank++) begin : gen_ecc_banks
      prim_secded_39_32_enc data_ecc_enc (
        .data_i (fill_wdata_ic0[bank*BUS_SIZE+:BUS_SIZE]),
        .data_o (data_wdata_ic0[bank*BusSizeECC+:BusSizeECC])
      );
    end

  end else begin : gen_noecc_wdata
    assign tag_wdata_ic0  = fill_tag_ic0;
    assign data_wdata_ic0 = fill_wdata_ic0;
  end

  ////////////////
  // IC0 -> IC1 //
  ////////////////

  // Tag RAMs outputs
  assign ic_tag_req_o    = {IC_NUM_WAYS{tag_req_ic0}} & tag_banks_ic0;
  assign ic_tag_write_o  = tag_write_ic0;
  assign ic_tag_addr_o   = tag_index_ic0;
  assign ic_tag_wdata_o  = tag_wdata_ic0;

  // Tag RAMs inputs
  assign tag_rdata_ic1   = ic_tag_rdata_i;

  // Data RAMs outputs
  assign ic_data_req_o   = {IC_NUM_WAYS{data_req_ic0}} & data_banks_ic0;
  assign ic_data_write_o = data_write_ic0;
  assign ic_data_addr_o  = data_index_ic0;
  assign ic_data_wdata_o = data_wdata_ic0;

  // Data RAMs inputs
  assign data_rdata_ic1  = ic_data_rdata_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lookup_valid_ic1 <= 1'b0;
    end else begin
      lookup_valid_ic1 <= lookup_actual_ic0;
    end
  end

  if (ResetAll) begin : g_lookup_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        lookup_addr_ic1 <= '0;
        fill_in_ic1     <= '0;
      end else if (lookup_grant_ic0) begin
        lookup_addr_ic1 <= lookup_addr_ic0[ADDR_W-1:IC_INDEX_HI+1];
        fill_in_ic1     <= fill_alloc_sel;
      end
    end
  end else begin : g_lookup_addr_nr
    always_ff @(posedge clk_i) begin
      if (lookup_grant_ic0) begin
        lookup_addr_ic1 <= lookup_addr_ic0[ADDR_W-1:IC_INDEX_HI+1];
        fill_in_ic1     <= fill_alloc_sel;
      end
    end
  end

  ////////////////////////
  // Pipeline stage IC1 //
  ////////////////////////

  // Tag matching
  for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_tag_match
    assign tag_match_ic1[way]   = (tag_rdata_ic1[way][IC_TAG_SIZE-1:0] ==
                                   {1'b1,lookup_addr_ic1[ADDR_W-1:IC_INDEX_HI+1]});
    assign tag_invalid_ic1[way] = ~tag_rdata_ic1[way][IC_TAG_SIZE-1];
  end

  assign tag_hit_ic1 = |tag_match_ic1;

  // Hit data mux
  always_comb begin
    hit_data_ecc_ic1 = 'b0;
    for (int way = 0; way < IC_NUM_WAYS; way++) begin
      if (tag_match_ic1[way]) begin
        hit_data_ecc_ic1 |= data_rdata_ic1[way];
      end
    end
  end

  // Way selection for allocations to the cache (onehot signals)
  // 1 first invalid way
  // 2 global round-robin (pseudorandom) way
  assign lowest_invalid_way_ic1[0] = tag_invalid_ic1[0];
  assign round_robin_way_ic1[0]    = round_robin_way_q[IC_NUM_WAYS-1];
  for (genvar way = 1; way < IC_NUM_WAYS; way++) begin : gen_lowest_way
    assign lowest_invalid_way_ic1[way] = tag_invalid_ic1[way] & ~|tag_invalid_ic1[way-1:0];
    assign round_robin_way_ic1[way]    = round_robin_way_q[way-1];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round_robin_way_q <= {{IC_NUM_WAYS-1{1'b0}}, 1'b1};
    end else if (lookup_valid_ic1) begin
      round_robin_way_q <= round_robin_way_ic1;
    end
  end

  assign sel_way_ic1 = |tag_invalid_ic1 ? lowest_invalid_way_ic1 :
                                          round_robin_way_q;

  // ECC checking logic
  if (ICacheECC) begin : gen_data_ecc_checking
    logic [IC_NUM_WAYS-1:0]     tag_err_ic1;
    logic [IC_LINE_BEATS*2-1:0] data_err_ic1;
    logic                       ecc_correction_write_d, ecc_correction_write_q;
    logic [IC_NUM_WAYS-1:0]     ecc_correction_ways_d, ecc_correction_ways_q;
    logic [IC_INDEX_W-1:0]      lookup_index_ic1, ecc_correction_index_q;

    // Tag ECC checking
    for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_tag_ecc
      logic [1:0]  tag_err_bank_ic1;
      logic [27:0] tag_rdata_padded_ic1;

      // Expand the tag rdata with extra padding if the tag size is less than the maximum
      assign tag_rdata_padded_ic1 = {tag_rdata_ic1[way][TagSizeECC-1-:6],
                                     {22-IC_TAG_SIZE{1'b0}},
                                     tag_rdata_ic1[way][IC_TAG_SIZE-1:0]};

      prim_secded_28_22_dec data_ecc_dec (
        .data_i     (tag_rdata_padded_ic1),
        .data_o     (),
        .syndrome_o (),
        .err_o      (tag_err_bank_ic1)
      );
      assign tag_err_ic1[way] = |tag_err_bank_ic1;
    end

    // Data ECC checking
    // Note - could generate for all ways and mux after
    for (genvar bank = 0; bank < IC_LINE_BEATS; bank++) begin : gen_ecc_banks
      prim_secded_39_32_dec data_ecc_dec (
        .data_i     (hit_data_ecc_ic1[bank*BusSizeECC+:BusSizeECC]),
        .data_o     (),
        .syndrome_o (),
        .err_o      (data_err_ic1[bank*2+:2])
      );

      assign hit_data_ic1[bank*BUS_SIZE+:BUS_SIZE] =
          hit_data_ecc_ic1[bank*BusSizeECC+:BUS_SIZE];

    end

    assign ecc_err_ic1 = lookup_valid_ic1 & ((|data_err_ic1) | (|tag_err_ic1));

    // Error correction
    // All ways will be invalidated on a tag error to prevent X-propagation from data_err_ic1 on
    // spurious hits. Also prevents the same line being allocated twice when there was a true
    // hit and a spurious hit.
    assign ecc_correction_ways_d  = {IC_NUM_WAYS{|tag_err_ic1}} |
                                    (tag_match_ic1 & {IC_NUM_WAYS{|data_err_ic1}});
    assign ecc_correction_write_d = ecc_err_ic1;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        ecc_correction_write_q <= 1'b0;
      end else begin
        ecc_correction_write_q <= ecc_correction_write_d;
      end
    end

    // The index is required in IC1 only when ECC is configured so is registered here
    if (ResetAll) begin : g_lookup_ind_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          lookup_index_ic1 <= '0;
        end else if (lookup_grant_ic0) begin
          lookup_index_ic1 <= lookup_addr_ic0[IC_INDEX_HI-:IC_INDEX_W];
        end
      end
    end else begin : g_lookup_ind_nr
      always_ff @(posedge clk_i) begin
        if (lookup_grant_ic0) begin
          lookup_index_ic1 <= lookup_addr_ic0[IC_INDEX_HI-:IC_INDEX_W];
        end
      end
    end

    // Store the ways with errors to be invalidated
    if (ResetAll) begin : g_ecc_correction_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          ecc_correction_ways_q  <= '0;
          ecc_correction_index_q <= '0;
        end else if (ecc_err_ic1) begin
          ecc_correction_ways_q  <= ecc_correction_ways_d;
          ecc_correction_index_q <= lookup_index_ic1;
        end
      end
    end else begin : g_ecc_correction_nr
      always_ff @(posedge clk_i) begin
        if (ecc_err_ic1) begin
          ecc_correction_ways_q  <= ecc_correction_ways_d;
          ecc_correction_index_q <= lookup_index_ic1;
        end
      end
    end

    assign ecc_write_req   = ecc_correction_write_q;
    assign ecc_write_ways  = ecc_correction_ways_q;
    assign ecc_write_index = ecc_correction_index_q;

  end else begin : gen_no_data_ecc
    assign ecc_err_ic1     = 1'b0;
    assign ecc_write_req   = 1'b0;
    assign ecc_write_ways  = '0;
    assign ecc_write_index = '0;
    assign hit_data_ic1    = hit_data_ecc_ic1;
  end

  ///////////////////////////////
  // Cache allocation decision //
  ///////////////////////////////

  if (BranchCache) begin : gen_caching_logic

    // Cache branch target + a number of subsequent lines
    localparam int unsigned CACHE_AHEAD = 2;
    localparam int unsigned CACHE_CNT_W = (CACHE_AHEAD == 1) ? 1 : $clog2(CACHE_AHEAD) + 1;
    logic                   cache_cnt_dec;
    logic [CACHE_CNT_W-1:0] cache_cnt_d, cache_cnt_q;

    assign cache_cnt_dec = lookup_grant_ic0 & (|cache_cnt_q);
    assign cache_cnt_d   = branch_i ? CACHE_AHEAD[CACHE_CNT_W-1:0] :
                                      (cache_cnt_q - {{CACHE_CNT_W-1{1'b0}},cache_cnt_dec});

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cache_cnt_q <= '0;
      end else begin
        cache_cnt_q <= cache_cnt_d;
      end
    end

    assign fill_cache_new = (branch_i | (|cache_cnt_q)) & icache_enable_i &
                            ~icache_inval_i & ~inval_prog_q;

  end else begin : gen_cache_all

    // Cache all missing fetches
    assign fill_cache_new = icache_enable_i & ~start_inval & ~inval_prog_q;
  end

  //////////////////////////
  // Fill buffer tracking //
  //////////////////////////

  always_comb begin
    fb_fill_level = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_busy_q[i] & ~fill_stale_q[i]) begin
        fb_fill_level += {{$clog2(NUM_FB)-1{1'b0}},1'b1};
      end
    end
  end

  // PMP errors might not / don't need to be granted (since the external request is masked)
  assign gnt_or_pmp_err  = instr_gnt_i | instr_pmp_err_i;
  assign gnt_not_pmp_err = instr_gnt_i & ~instr_pmp_err_i;
  // Allocate a new buffer for every granted lookup
  assign fill_new_alloc = lookup_grant_ic0;
  // Track whether a speculative external request was made from IC0, and whether it was granted
  // Speculative requests are only made for branches, or if the cache is disabled
  assign fill_spec_req  = (~icache_enable_i | branch_or_mispredict) & ~|fill_ext_req;
  assign fill_spec_done = fill_spec_req & gnt_not_pmp_err;
  assign fill_spec_hold = fill_spec_req & ~gnt_or_pmp_err;

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : gen_fbs

    /////////////////////////////
    // Fill buffer allocations //
    /////////////////////////////

    // Allocate the lowest available buffer
    if (fb == 0) begin : gen_fb_zero
      assign fill_alloc_sel[fb] = ~fill_busy_q[fb];
    end else begin : gen_fb_rest
      assign fill_alloc_sel[fb] = ~fill_busy_q[fb] & (&fill_busy_q[fb-1:0]);
    end

    assign fill_alloc[fb]      = fill_alloc_sel[fb] & fill_new_alloc;
    assign fill_busy_d[fb]     = fill_alloc[fb] | (fill_busy_q[fb] & ~fill_done[fb]);

    // Track which other fill buffers are older than this one (for age-based arbitration)
    // TODO sparsify
    assign fill_older_d[fb]    = (fill_alloc[fb] ? fill_busy_q : fill_older_q[fb]) & ~fill_done;

    // A fill buffer can release once all its actions are completed
                                 // all data written to the cache (unless hit or error)
    assign fill_done[fb]       = (fill_ram_done_q[fb] | fill_hit_q[fb] | ~fill_cache_q[fb] |
                                  (|fill_err_q[fb])) &
                                 // all data output unless stale due to intervening branch
                                 (fill_out_done[fb] | fill_stale_q[fb] | branch_or_mispredict) &
                                 // all external requests completed
                                 fill_rvd_done[fb];

    /////////////////////////////////
    // Fill buffer status tracking //
    /////////////////////////////////

    // Track staleness (requests become stale when a branch intervenes)
    assign fill_stale_d[fb]    = fill_busy_q[fb] & (branch_or_mispredict | fill_stale_q[fb]);
    // Track whether or not this request should allocate to the cache
    // Any invalidation or disabling of the cache while the buffer is busy will stop allocation
    assign fill_cache_d[fb]    = (fill_alloc[fb] & fill_cache_new) |
                                 (fill_cache_q[fb] & fill_busy_q[fb] &
                                  icache_enable_i & ~icache_inval_i);
    // Record whether the request hit in the cache
    assign fill_hit_ic1[fb]    = lookup_valid_ic1 & fill_in_ic1[fb] & tag_hit_ic1 & ~ecc_err_ic1;
    assign fill_hit_d[fb]      = fill_hit_ic1[fb] | (fill_hit_q[fb] & fill_busy_q[fb]);

    ///////////////////////////////////////////
    // Fill buffer external request tracking //
    ///////////////////////////////////////////

    // Make an external request
    assign fill_ext_req[fb]    = fill_busy_q[fb] & ~fill_ext_done_d[fb];

    // Count the number of completed external requests (each line requires IC_LINE_BEATS requests)
    // Don't count fake PMP error grants here since they will never receive an rvalid response
    assign fill_ext_cnt_d[fb]  = fill_alloc[fb] ?
                                   {{IC_LINE_BEATS_W{1'b0}},fill_spec_done} :
                                   (fill_ext_cnt_q[fb] + {{IC_LINE_BEATS_W{1'b0}},
                                                          fill_ext_arb[fb] & gnt_not_pmp_err});
    // External request must be held until granted
    assign fill_ext_hold_d[fb] = (fill_alloc[fb] & fill_spec_hold) |
                                 (fill_ext_arb[fb] & ~gnt_or_pmp_err);
    // External requests are completed when the counter is filled or when the request is cancelled
    assign fill_ext_done_d[fb] = (fill_ext_cnt_q[fb][IC_LINE_BEATS_W] |
                                  // external requests are considered complete if the request hit
                                  fill_hit_ic1[fb] | fill_hit_q[fb] |
                                  // external requests will stop once any PMP error is received
                                  fill_err_q[fb][fill_ext_off[fb]] |
                                  // cancel if the line won't be cached and, it is stale
                                  (~fill_cache_q[fb] & (branch_or_mispredict | fill_stale_q[fb] |
                                   // or we're already at the end of the line
                                                        fill_ext_beat[fb][IC_LINE_BEATS_W]))) &
                                 // can't cancel while we are waiting for a grant on the bus
                                 ~fill_ext_hold_q[fb] & fill_busy_q[fb];
    // Track whether this fill buffer expects to receive beats of data
    assign fill_rvd_exp[fb]    = fill_busy_q[fb] & ~fill_rvd_done[fb];
    // Count the number of rvalid beats received
    assign fill_rvd_cnt_d[fb]  = fill_alloc[fb] ? '0 :
                                                  (fill_rvd_cnt_q[fb] +
                                                   {{IC_LINE_BEATS_W{1'b0}},fill_rvd_arb[fb]});
    // External data is complete when all issued external requests have received their data
    assign fill_rvd_done[fb]   = (fill_ext_done_q[fb] & ~fill_ext_hold_q[fb]) &
                                 (fill_rvd_cnt_q[fb] == fill_ext_cnt_q[fb]);

    //////////////////////////////////////
    // Fill buffer data output tracking //
    //////////////////////////////////////

    // Send data to the IF stage for requests that are not stale, have not completed their
    // data output, and have data available to send.
    // Data is available if:
    // - The request hit in the cache
    // - The current beat is an error (since a PMP error might not actually receive any data)
    // - Buffered data is available (fill_rvd_cnt_q is ahead of fill_out_cnt_q)
    // - Data is available from the bus this cycle (fill_rvd_arb)
    assign fill_out_req[fb]    = fill_busy_q[fb] & ~fill_stale_q[fb] & ~fill_out_done[fb] &
                                 (fill_hit_ic1[fb] | fill_hit_q[fb] |
                                  (fill_err_q[fb][fill_out_cnt_q[fb][IC_LINE_BEATS_W-1:0]]) |
                                  (fill_rvd_beat[fb] > fill_out_cnt_q[fb]) | fill_rvd_arb[fb]);

    // Calculate when a beat of data is output. Any ECC error squashes the output that cycle.
    assign fill_out_grant[fb]  = fill_out_arb[fb] & output_ready;

    // Count the beats of data output to the IF stage
    assign fill_out_cnt_d[fb]  = fill_alloc[fb] ? {1'b0,lookup_addr_ic0[IC_LINE_W-1:BUS_W]} :
                                                  (fill_out_cnt_q[fb] +
                                                   {{IC_LINE_BEATS_W{1'b0}},fill_out_grant[fb]});
    // Data output complete when the counter fills
    assign fill_out_done[fb]   = fill_out_cnt_q[fb][IC_LINE_BEATS_W];

    //////////////////////////////////////
    // Fill buffer ram request tracking //
    //////////////////////////////////////

                                 // make a fill request once all data beats received
    assign fill_ram_req[fb]    = fill_busy_q[fb] & fill_rvd_cnt_q[fb][IC_LINE_BEATS_W] &
                                 // unless the request hit, was non-allocating or got an error
                                 ~fill_hit_q[fb] & fill_cache_q[fb] & ~|fill_err_q[fb] &
                                 // or the request was already completed
                                 ~fill_ram_done_q[fb];

    // Record when a cache allocation request has been completed
    assign fill_ram_done_d[fb] = fill_ram_arb[fb] | (fill_ram_done_q[fb] & fill_busy_q[fb]);

    //////////////////////////////
    // Fill buffer line offsets //
    //////////////////////////////

    // When we branch into the middle of a line, the output count will not start from zero. This
    // beat count is used to know which incoming rdata beats are relevant.
    assign fill_ext_beat[fb]   = {1'b0,fill_addr_q[fb][IC_LINE_W-1:BUS_W]} +
                                 fill_ext_cnt_q[fb][IC_LINE_BEATS_W:0];
    assign fill_ext_off[fb]    = fill_ext_beat[fb][IC_LINE_BEATS_W-1:0];
    assign fill_rvd_beat[fb]   = {1'b0,fill_addr_q[fb][IC_LINE_W-1:BUS_W]} +
                                 fill_rvd_cnt_q[fb][IC_LINE_BEATS_W:0];
    assign fill_rvd_off[fb]    = fill_rvd_beat[fb][IC_LINE_BEATS_W-1:0];

    /////////////////////////////
    // Fill buffer arbitration //
    /////////////////////////////

    // Age based arbitration - all these signals are one-hot
    assign fill_ext_arb[fb]    = fill_ext_req[fb] & ~|(fill_ext_req & fill_older_q[fb]);
    assign fill_ram_arb[fb]    = fill_ram_req[fb] & fill_grant_ic0 &
                                 ~|(fill_ram_req & fill_older_q[fb]);
    // Calculate which fill buffer is the oldest one which still needs to output data to IF
    assign fill_data_sel[fb]   = ~|(fill_busy_q & ~fill_out_done & ~fill_stale_q &
                                    fill_older_q[fb]);
    // Arbitrate the request which has data available to send, and is the oldest outstanding
    assign fill_out_arb[fb]    = fill_out_req[fb] & fill_data_sel[fb];
    // Assign incoming rvalid data to the oldest fill buffer expecting it
    assign fill_rvd_arb[fb]    = instr_rvalid_i & fill_rvd_exp[fb] &
                                 ~|(fill_rvd_exp & fill_older_q[fb]);

    /////////////////////////////
    // Fill buffer data muxing //
    /////////////////////////////

    // Output data muxing controls
    // 1. Select data from the fill buffer data register
    assign fill_data_reg[fb]   = fill_busy_q[fb] & ~fill_stale_q[fb] &
                                 ~fill_out_done[fb] & fill_data_sel[fb] &
    //                           The incoming data is already ahead of the output count
                                 ((fill_rvd_beat[fb] > fill_out_cnt_q[fb]) | fill_hit_q[fb] |
                                  (|fill_err_q[fb]));
    // 2. Select IC1 hit data
    assign fill_data_hit[fb]   = fill_busy_q[fb] & fill_hit_ic1[fb] & fill_data_sel[fb];
    // 3. Select incoming instr_rdata_i
    assign fill_data_rvd[fb]   = fill_busy_q[fb] & fill_rvd_arb[fb] & ~fill_hit_q[fb] &
                                 ~fill_hit_ic1[fb] & ~fill_stale_q[fb] & ~fill_out_done[fb] &
    //                           The incoming data lines up with the output count
                                 (fill_rvd_beat[fb] == fill_out_cnt_q[fb]) & fill_data_sel[fb];


    ///////////////////////////
    // Fill buffer registers //
    ///////////////////////////

    // Fill buffer general enable
    assign fill_entry_en[fb]   = fill_alloc[fb] | fill_busy_q[fb];

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fill_busy_q[fb]     <= 1'b0;
        fill_older_q[fb]    <= '0;
        fill_stale_q[fb]    <= 1'b0;
        fill_cache_q[fb]    <= 1'b0;
        fill_hit_q[fb]      <= 1'b0;
        fill_ext_cnt_q[fb]  <= '0;
        fill_ext_hold_q[fb] <= 1'b0;
        fill_ext_done_q[fb] <= 1'b0;
        fill_rvd_cnt_q[fb]  <= '0;
        fill_ram_done_q[fb] <= 1'b0;
        fill_out_cnt_q[fb]  <= '0;
      end else if (fill_entry_en[fb]) begin
        fill_busy_q[fb]     <= fill_busy_d[fb];
        fill_older_q[fb]    <= fill_older_d[fb];
        fill_stale_q[fb]    <= fill_stale_d[fb];
        fill_cache_q[fb]    <= fill_cache_d[fb];
        fill_hit_q[fb]      <= fill_hit_d[fb];
        fill_ext_cnt_q[fb]  <= fill_ext_cnt_d[fb];
        fill_ext_hold_q[fb] <= fill_ext_hold_d[fb];
        fill_ext_done_q[fb] <= fill_ext_done_d[fb];
        fill_rvd_cnt_q[fb]  <= fill_rvd_cnt_d[fb];
        fill_ram_done_q[fb] <= fill_ram_done_d[fb];
        fill_out_cnt_q[fb]  <= fill_out_cnt_d[fb];
      end
    end

    ////////////////////////////////////////
    // Fill buffer address / data storage //
    ////////////////////////////////////////

    assign fill_addr_en[fb]    = fill_alloc[fb];
    assign fill_way_en[fb]     = (lookup_valid_ic1 & fill_in_ic1[fb]);

    if (ResetAll) begin : g_fill_addr_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          fill_addr_q[fb] <= '0;
        end else if (fill_addr_en[fb]) begin
          fill_addr_q[fb] <= lookup_addr_ic0;
        end
      end
    end else begin : g_fill_addr_nr
      always_ff @(posedge clk_i) begin
        if (fill_addr_en[fb]) begin
          fill_addr_q[fb] <= lookup_addr_ic0;
        end
      end
    end

    if (ResetAll) begin : g_fill_way_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          fill_way_q[fb]  <= '0;
        end else if (fill_way_en[fb]) begin
          fill_way_q[fb]  <= sel_way_ic1;
        end
      end
    end else begin : g_fill_way_nr
      always_ff @(posedge clk_i) begin
        if (fill_way_en[fb]) begin
          fill_way_q[fb]  <= sel_way_ic1;
        end
      end
    end

    // Data either comes from the cache or the bus. If there was an ECC error, we must take
    // the incoming bus data since the cache hit data is corrupted.
    assign fill_data_d[fb] = fill_hit_ic1[fb] ? hit_data_ic1 :
                                                {IC_LINE_BEATS{instr_rdata_i}};

    for (genvar b = 0; b < IC_LINE_BEATS; b++) begin : gen_data_buf
      // Error tracking (per beat)
      //                           Either a PMP error on a speculative request,
      assign fill_err_d[fb][b]   = (instr_pmp_err_i & fill_alloc[fb] & fill_spec_req &
                                    (lookup_addr_ic0[IC_LINE_W-1:BUS_W] ==
                                     b[IC_LINE_BEATS_W-1:0])) |
      //                           a PMP error on a fill buffer ext req
                                   (instr_pmp_err_i & fill_ext_arb[fb] &
                                    (fill_ext_off[fb] == b[IC_LINE_BEATS_W-1:0])) |
      //                           Or a data error with instr_rvalid_i
                                   (fill_rvd_arb[fb] & instr_err_i &
                                    (fill_rvd_off[fb] == b[IC_LINE_BEATS_W-1:0])) |
      //                           Hold the error once recorded
                                   (fill_busy_q[fb] & fill_err_q[fb][b]);

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          fill_err_q[fb][b] <= '0;
        end else if (fill_entry_en[fb]) begin
          fill_err_q[fb][b] <= fill_err_d[fb][b];
        end
      end

      // Enable the relevant part of the data register (or all for cache hits)
      // Ignore incoming rvalid data when we already have cache hit data
      assign fill_data_en[fb][b] = fill_hit_ic1[fb] |
                                   (fill_rvd_arb[fb] & ~fill_hit_q[fb] &
                                    (fill_rvd_off[fb] == b[IC_LINE_BEATS_W-1:0]));

      if (ResetAll) begin : g_fill_data_ra
        always_ff @(posedge clk_i or negedge rst_ni) begin
          if (!rst_ni) begin
            fill_data_q[fb][b*BUS_SIZE+:BUS_SIZE] <= '0;
          end else if (fill_data_en[fb][b]) begin
            fill_data_q[fb][b*BUS_SIZE+:BUS_SIZE] <= fill_data_d[fb][b*BUS_SIZE+:BUS_SIZE];
          end
        end
      end else begin : g_fill_data_nr
        always_ff @(posedge clk_i) begin
          if (fill_data_en[fb][b]) begin
            fill_data_q[fb][b*BUS_SIZE+:BUS_SIZE] <= fill_data_d[fb][b*BUS_SIZE+:BUS_SIZE];
          end
        end
      end

    end
  end

  ////////////////////////////////
  // Fill buffer one-hot muxing //
  ////////////////////////////////

  // External req info
  always_comb begin
    fill_ext_req_addr = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_ext_arb[i]) begin
        fill_ext_req_addr |= {fill_addr_q[i][ADDR_W-1:IC_LINE_W], fill_ext_off[i]};
      end
    end
  end

  // Cache req info
  always_comb begin
    fill_ram_req_addr = '0;
    fill_ram_req_way  = '0;
    fill_ram_req_data = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_ram_arb[i]) begin
        fill_ram_req_addr |= fill_addr_q[i];
        fill_ram_req_way  |= fill_way_q[i];
        fill_ram_req_data |= fill_data_q[i];
      end
    end
  end

  // IF stage output data
  always_comb begin
    fill_out_data = '0;
    fill_out_err  = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_data_reg[i]) begin
        fill_out_data |= fill_data_q[i];
        // Ignore any speculative errors accumulated on cache hits
        fill_out_err  |= (fill_err_q[i] & ~{IC_LINE_BEATS{fill_hit_q[i]}});
      end
    end
  end

  ///////////////////////
  // External requests //
  ///////////////////////

  assign instr_req  = ((~icache_enable_i | branch_or_mispredict) & lookup_grant_ic0) |
                      (|fill_ext_req);

  assign instr_addr = |fill_ext_req ? fill_ext_req_addr :
                                      lookup_addr_ic0[ADDR_W-1:BUS_W];

  assign instr_req_o  = instr_req;
  assign instr_addr_o = {instr_addr[ADDR_W-1:BUS_W],{BUS_W{1'b0}}};

  ////////////////////////
  // Output data muxing //
  ////////////////////////

  // Mux between line-width data sources
  assign line_data = |fill_data_hit ? hit_data_ic1 : fill_out_data;
  assign line_err  = |fill_data_hit ? {IC_LINE_BEATS{1'b0}} : fill_out_err;

  // Mux the relevant beat of line data, based on the output address
  always_comb begin
    line_data_muxed = '0;
    line_err_muxed  = 1'b0;
    for (int i = 0; i < IC_LINE_BEATS; i++) begin
      // When data has been skidded, the output address is behind by one
      if ((output_addr_q[IC_LINE_W-1:BUS_W] + {{IC_LINE_BEATS_W-1{1'b0}},skid_valid_q}) ==
          i[IC_LINE_BEATS_W-1:0]) begin
        line_data_muxed |= line_data[i*32+:32];
        line_err_muxed  |= line_err[i];
      end
    end
  end

  // Mux between incoming rdata and the muxed line data
  assign output_data = |fill_data_rvd ? instr_rdata_i : line_data_muxed;
  assign output_err  = |fill_data_rvd ? instr_err_i   : line_err_muxed;

  // Output data is valid (from any of the three possible sources). Note that fill_out_arb
  // must be used here rather than fill_out_req because data can become valid out of order
  // (e.g. cache hit data can become available ahead of an older outstanding miss).
  assign data_valid = |fill_out_arb;

  // Skid buffer data
  assign skid_data_d = output_data[31:16];

  assign skid_en     = data_valid & (ready_i | skid_ready);

  if (ResetAll) begin : g_skid_data_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        skid_data_q <= '0;
        skid_err_q  <= '0;
      end else if (skid_en) begin
        skid_data_q <= skid_data_d;
        skid_err_q  <= output_err;
      end
    end
  end else begin : g_skid_data_nr
    always_ff @(posedge clk_i) begin
      if (skid_en) begin
        skid_data_q <= skid_data_d;
        skid_err_q  <= output_err;
      end
    end
  end

  // The data in the skid buffer is ready if it's a complete compressed instruction or if there's
  // an error (no need to wait for the second half)
  assign skid_complete_instr = skid_valid_q & ((skid_data_q[1:0] != 2'b11) | skid_err_q);

  // Data can be loaded into the skid buffer for an unaligned uncompressed instruction
  assign skid_ready = output_addr_q[1] & ~skid_valid_q & (~output_compressed | output_err);

  assign output_ready = (ready_i | skid_ready) & ~skid_complete_instr;

  assign output_compressed = (rdata_o[1:0] != 2'b11);

  assign skid_valid_d =
      // Branches invalidate the skid buffer
      branch_or_mispredict ? 1'b0 :
      // Once valid, the skid buffer stays valid until a compressed instruction realigns the stream
      (skid_valid_q ? ~(ready_i & ((skid_data_q[1:0] != 2'b11) | skid_err_q)) :
      // The skid buffer becomes valid when:
                        // - we branch to an unaligned uncompressed instruction
                      (data_valid &
                       (((output_addr_q[1] & (~output_compressed | output_err)) |
                        // - a compressed instruction misaligns the stream
                        (~output_addr_q[1] & output_compressed & ~output_err & ready_i)))));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      skid_valid_q <= 1'b0;
    end else begin
      skid_valid_q <= skid_valid_d;
    end
  end

  // Signal that valid data is available to the IF stage
  // Note that if the first half of an unaligned instruction reports an error, we do not need
  // to wait for the second half (and for PMP errors we might not have fetched the second half)
                        // Compressed instruction completely satisfied by skid buffer
  assign output_valid = skid_complete_instr |
                        // Output data available and, output stream aligned, or skid data available,
                        (data_valid & (~output_addr_q[1] | skid_valid_q |
                                       // or this is an error or an unaligned compressed instruction
                                       output_err | (output_data[17:16] != 2'b11)));

  // Update the address on branches and every time an instruction is driven
  assign output_addr_en = branch_or_mispredict | (ready_i & valid_o);

  // Increment the address by two every time a compressed instruction is popped
  assign addr_incr_two = output_compressed & ~err_o;

  // Next IF stage PC
  assign output_addr_incr = (output_addr_q[31:1] +
                             // Increment address by 4 or 2
                             {29'd0, ~addr_incr_two, addr_incr_two});

  // Redirect the address on branches or mispredicts
  assign output_addr_d = branch_i            ? addr_i[31:1] :
                         branch_mispredict_i ? branch_mispredict_addr[31:1] :
                                               output_addr_incr;

  if (ResetAll) begin : g_output_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        output_addr_q <= '0;
      end else if (output_addr_en) begin
        output_addr_q <= output_addr_d;
      end
    end
  end else begin : g_output_addr_nr
    always_ff @(posedge clk_i) begin
      if (output_addr_en) begin
        output_addr_q <= output_addr_d;
      end
    end
  end

  // Mux the data from BUS_SIZE to halfword
  // This muxing realigns data when instruction words are split across BUS_W e.g.
  // word 1 |----|*h1*|
  // word 0 |*h0*|----| --> |*h1*|*h0*|
  //        31   15   0     31   15   0
  always_comb begin
    output_data_lo = '0;
    for (int i = 0; i < IC_OUTPUT_BEATS; i++) begin
      if (output_addr_q[BUS_W-1:1] == i[BUS_W-2:0]) begin
        output_data_lo |= output_data[i*16+:16];
      end
    end
  end

  always_comb begin
    output_data_hi = '0;
    for (int i = 0; i < IC_OUTPUT_BEATS-1; i++) begin
      if (output_addr_q[BUS_W-1:1] == i[BUS_W-2:0]) begin
        output_data_hi |= output_data[(i+1)*16+:16];
      end
    end
    if (&output_addr_q[BUS_W-1:1]) begin
      output_data_hi |= output_data[15:0];
    end
  end

  assign valid_o     = output_valid & ~branch_mispredict_i;
  assign rdata_o     = {output_data_hi, (skid_valid_q ? skid_data_q : output_data_lo)};
  assign addr_o      = {output_addr_q, 1'b0};
  assign err_o       = (skid_valid_q & skid_err_q) | (~skid_complete_instr & output_err);
  // Error caused by the second half of a misaligned uncompressed instruction
  // (only relevant when err_o is set)
  assign err_plus2_o = skid_valid_q & ~skid_err_q;

  ///////////////////
  // Invalidations //
  ///////////////////

  // Invalidate on reset, or when instructed. If an invalidation request is received while a
  // previous invalidation is ongoing, it does not need to be restarted.
  assign start_inval   = (~reset_inval_q | icache_inval_i) & ~inval_prog_q;
  assign inval_prog_d  = start_inval | (inval_prog_q & ~inval_done);
  assign inval_done    = &inval_index_q;
  assign inval_index_d = start_inval ? '0 :
                                       (inval_index_q + {{IC_INDEX_W-1{1'b0}},1'b1});

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      inval_prog_q  <= 1'b0;
      reset_inval_q <= 1'b0;
    end else begin
      inval_prog_q  <= inval_prog_d;
      reset_inval_q <= 1'b1;
    end
  end

  if (ResetAll) begin : g_inval_index_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        inval_index_q <= '0;
      end else if (inval_prog_d) begin
        inval_index_q <= inval_index_d;
      end
    end
  end else begin : g_inval_index_nr
    always_ff @(posedge clk_i) begin
      if (inval_prog_d) begin
        inval_index_q <= inval_index_d;
      end
    end
  end

  /////////////////
  // Busy status //
  /////////////////

  // Only busy (for WFI purposes) while an invalidation is in-progress, or external requests are
  // outstanding.
  assign busy_o = inval_prog_q | (|(fill_busy_q & ~fill_rvd_done));

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_INIT(size_param_legal, (IC_LINE_SIZE > 32))

  // ECC primitives will need to be changed for different sizes
  `ASSERT_INIT(ecc_tag_param_legal, (IC_TAG_SIZE <= 27))
  `ASSERT_INIT(ecc_data_param_legal, !ICacheECC || (BUS_SIZE == 32))

  // Lookups in the tag ram should always give a known result
  `ASSERT_KNOWN(TagHitKnown,     lookup_valid_ic1 & tag_hit_ic1)
  `ASSERT_KNOWN(TagInvalidKnown, lookup_valid_ic1 & tag_invalid_ic1)

  // This is only used for the Yosys-based formal flow. Once we have working bind support, we can
  // get rid of it.
`ifdef FORMAL
 `ifdef YOSYS
  // Unfortunately, Yosys doesn't support passing unpacked arrays as ports. Explicitly pack up the
  // signals we need.
  logic [NUM_FB-1:0][ADDR_W-1:0] packed_fill_addr_q;
  always_comb begin
    for (int i = 0; i < NUM_FB; i++) begin
      packed_fill_addr_q[i][ADDR_W-1:0] = fill_addr_q[i];
    end
  end

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

formal_tb tb_i (.*);
 `endif
`endif


endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Instruction Decode Stage
 *
 * Decode stage of the core. It decodes the instructions and hosts the register
 * file.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Disable it for synthesis and where explicitly requested (by defining
// DV_FCOV_DISABLE).
`ifdef SYNTHESIS
  `define DV_FCOV_DISABLE
`elsif YOSYS
  `define DV_FCOV_DISABLE
`endif

// Disable instantiations of FCOV coverpoints or covergroups.
`ifdef VERILATOR
  `define DV_FCOV_DISABLE_CP
`elsif DV_FCOV_DISABLE
  `define DV_FCOV_DISABLE_CP
`endif

// Instantiates a covergroup in an interface or module.
//
// This macro assumes that a covergroup of the same name as the NAME_ arg is defined in the
// interface or module. It just adds some extra signals and logic to control the creation of the
// covergroup instance with ~bit en_<cg_name>~. This defaults to 0. It is ORed with the external
// COND_ signal. The testbench can modify it at t = 0 based on the test being run.
// NOTE: This is not meant to be invoked inside a class.
//
// NAME_ : Name of the covergroup.
// COND_ : External condition / expr that controls the creation of the covergroup.
// ARGS_ : Arguments to covergroup instance, if any. Args MUST BE wrapped in (..).
`ifndef DV_FCOV_INSTANTIATE_CG
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ())
`else
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ()) \
    bit en_``NAME_ = 1'b0; \
    NAME_ NAME_``_inst; \
    initial begin \
      /* The #1 delay below allows any part of the tb to control the conditions first at t = 0. */ \
      #1; \
      if ((en_``NAME_) || (COND_)) begin \
        $display("%0t: (%0s:%0d) [%m] %0s", $time, `__FILE__, `__LINE__, \
                 {"Creating covergroup ", `"NAME_`"}); \
        NAME_``_inst = new``ARGS_; \
      end \
    end
`endif
`endif

// Creates a coverpoint for an expression where only the expression true case is of interest for
// coverage (e.g. where the expression indicates an event has occured).
`ifndef DV_FCOV_EXPR_SEEN
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_)
`else
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_) cp_``NAME_: coverpoint EXPR_ { bins seen = {1}; }
`endif
`endif

// Creates a SVA cover that can be used in a covergroup.
//
// This macro creates an unnamed SVA cover from the property (or an expression) `PROP_` and an event
// with the name `EV_NAME_`. When the SVA cover is hit, the event is triggered. A coverpoint can
// cover the `triggered` property of the event.
`ifndef DV_FCOV_SVA
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni)
`else
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni) \
    event EV_NAME_; \
    cover property (@(posedge CLK_) disable iff (RST_ == 0) (PROP_)) begin \
      -> EV_NAME_; \
    end
`endif
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef DV_FCOV_MARK_UNUSED
  `define DV_FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef DV_FCOV_SIGNAL
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef DV_FCOV_SIGNAL_GEN_IF
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

module ibex_id_stage #(
    parameter bit               RV32E           = 0,
    parameter ibex_pkg::rv32m_e RV32M           = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e RV32B           = ibex_pkg::RV32BNone,
    parameter bit               DataIndTiming   = 1'b0,
    parameter bit               BranchTargetALU = 0,
    parameter bit               SpecBranch      = 0,
    parameter bit               WritebackStage  = 0,
    parameter bit               BranchPredictor = 0
) (
    input  logic                      clk_i,
    input  logic                      rst_ni,

    output logic                      ctrl_busy_o,
    output logic                      illegal_insn_o,

    // Interface to IF stage
    input  logic                      instr_valid_i,
    input  logic [31:0]               instr_rdata_i,         // from IF-ID pipeline registers
    input  logic [31:0]               instr_rdata_alu_i,     // from IF-ID pipeline registers
    input  logic [15:0]               instr_rdata_c_i,       // from IF-ID pipeline registers
    input  logic                      instr_is_compressed_i,
    input  logic                      instr_bp_taken_i,
    output logic                      instr_req_o,
    output logic                      instr_first_cycle_id_o,
    output logic                      instr_valid_clear_o,   // kill instr in IF-ID reg
    output logic                      id_in_ready_o,         // ID stage is ready for next instr
    output logic                      icache_inval_o,

    // Jumps and branches
    input  logic                      branch_decision_i,

    // IF and ID stage signals
    output logic                      pc_set_o,
    output logic                      pc_set_spec_o,
    output ibex_pkg::pc_sel_e         pc_mux_o,
    output logic                      nt_branch_mispredict_o,
    output ibex_pkg::exc_pc_sel_e     exc_pc_mux_o,
    output ibex_pkg::exc_cause_e      exc_cause_o,

    input  logic                      illegal_c_insn_i,
    input  logic                      instr_fetch_err_i,
    input  logic                      instr_fetch_err_plus2_i,

    input  logic [31:0]               pc_id_i,

    // Stalls
    input  logic                      ex_valid_i,       // EX stage has valid output
    input  logic                      lsu_resp_valid_i, // LSU has valid output, or is done
    // ALU
    output ibex_pkg::alu_op_e         alu_operator_ex_o,
    output logic [31:0]               alu_operand_a_ex_o,
    output logic [31:0]               alu_operand_b_ex_o,

    // Multicycle Operation Stage Register
    input  logic [1:0]                imd_val_we_ex_i,
    input  logic [33:0]               imd_val_d_ex_i[2],
    output logic [33:0]               imd_val_q_ex_o[2],

    // Branch target ALU
    output logic [31:0]               bt_a_operand_o,
    output logic [31:0]               bt_b_operand_o,

    // MUL, DIV
    output logic                      mult_en_ex_o,
    output logic                      div_en_ex_o,
    output logic                      mult_sel_ex_o,
    output logic                      div_sel_ex_o,
    output ibex_pkg::md_op_e          multdiv_operator_ex_o,
    output logic  [1:0]               multdiv_signed_mode_ex_o,
    output logic [31:0]               multdiv_operand_a_ex_o,
    output logic [31:0]               multdiv_operand_b_ex_o,
    output logic                      multdiv_ready_id_o,

    // CSR
    output logic                      csr_access_o,
    output ibex_pkg::csr_op_e         csr_op_o,
    output logic                      csr_op_en_o,
    output logic                      csr_save_if_o,
    output logic                      csr_save_id_o,
    output logic                      csr_save_wb_o,
    output logic                      csr_restore_mret_id_o,
    output logic                      csr_restore_dret_id_o,
    output logic                      csr_save_cause_o,
    output logic [31:0]               csr_mtval_o,
    input  ibex_pkg::priv_lvl_e       priv_mode_i,
    input  logic                      csr_mstatus_tw_i,
    input  logic                      illegal_csr_insn_i,
    input  logic                      data_ind_timing_i,

    // Interface to load store unit
    output logic                      lsu_req_o,
    output logic                      lsu_we_o,
    output logic [1:0]                lsu_type_o,
    output logic                      lsu_sign_ext_o,
    output logic [31:0]               lsu_wdata_o,

    input  logic                      lsu_req_done_i, // Data req to LSU is complete and
                                                      // instruction can move to writeback
                                                      // (only relevant where writeback stage is
                                                      // present)

    input  logic                      lsu_addr_incr_req_i,
    input  logic [31:0]               lsu_addr_last_i,

    // Interrupt signals
    input  logic                      csr_mstatus_mie_i,
    input  logic                      irq_pending_i,
    input  ibex_pkg::irqs_t           irqs_i,
    input  logic                      irq_nm_i,
    output logic                      nmi_mode_o,

    input  logic                      lsu_load_err_i,
    input  logic                      lsu_store_err_i,

    // Debug Signal
    output logic                      debug_mode_o,
    output ibex_pkg::dbg_cause_e      debug_cause_o,
    output logic                      debug_csr_save_o,
    input  logic                      debug_req_i,
    input  logic                      debug_single_step_i,
    input  logic                      debug_ebreakm_i,
    input  logic                      debug_ebreaku_i,
    input  logic                      trigger_match_i,

    // Write back signal
    input  logic [31:0]               result_ex_i,
    input  logic [31:0]               csr_rdata_i,

    // Register file read
    output logic [4:0]                rf_raddr_a_o,
    input  logic [31:0]               rf_rdata_a_i,
    output logic [4:0]                rf_raddr_b_o,
    input  logic [31:0]               rf_rdata_b_i,
    output logic                      rf_ren_a_o,
    output logic                      rf_ren_b_o,

    // Register file write (via writeback)
    output logic [4:0]                rf_waddr_id_o,
    output logic [31:0]               rf_wdata_id_o,
    output logic                      rf_we_id_o,
    output logic                      rf_rd_a_wb_match_o,
    output logic                      rf_rd_b_wb_match_o,

    // Register write information from writeback (for resolving data hazards)
    input  logic [4:0]                rf_waddr_wb_i,
    input  logic [31:0]               rf_wdata_fwd_wb_i,
    input  logic                      rf_write_wb_i,

    output  logic                     en_wb_o,
    output  ibex_pkg::wb_instr_type_e instr_type_wb_o,
    output  logic                     instr_perf_count_id_o,
    input logic                       ready_wb_i,
    input logic                       outstanding_load_wb_i,
    input logic                       outstanding_store_wb_i,

    // Performance Counters
    output logic                      perf_jump_o,    // executing a jump instr
    output logic                      perf_branch_o,  // executing a branch instr
    output logic                      perf_tbranch_o, // executing a taken branch instr
    output logic                      perf_dside_wait_o, // instruction in ID/EX is awaiting memory
                                                         // access to finish before proceeding
    output logic                      perf_mul_wait_o,
    output logic                      perf_div_wait_o,
    output logic                      instr_id_done_o
);

  import ibex_pkg::*;

  // Decoder/Controller, ID stage internal signals
  logic        illegal_insn_dec;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        dret_insn_dec;
  logic        ecall_insn_dec;
  logic        wfi_insn_dec;

  logic        wb_exception;

  logic        branch_in_dec;
  logic        branch_spec, branch_set_spec, branch_set_raw_spec;
  logic        branch_set, branch_set_raw, branch_set_raw_d;
  logic        branch_jump_set_done_q, branch_jump_set_done_d;
  logic        branch_not_set;
  logic        branch_taken;
  logic        jump_in_dec;
  logic        jump_set_dec;
  logic        jump_set, jump_set_raw;

  logic        instr_first_cycle;
  logic        instr_executing_spec;
  logic        instr_executing;
  logic        instr_done;
  logic        controller_run;
  logic        stall_ld_hz;
  logic        stall_mem;
  logic        stall_multdiv;
  logic        stall_branch;
  logic        stall_jump;
  logic        stall_id;
  logic        stall_wb;
  logic        flush_id;
  logic        multicycle_done;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // Register file interface

  rf_wd_sel_e  rf_wdata_sel;
  logic        rf_we_dec, rf_we_raw;
  logic        rf_ren_a, rf_ren_b;
  logic        rf_ren_a_dec, rf_ren_b_dec;

  // Read enables should only be asserted for valid and legal instructions
  assign rf_ren_a = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_a_dec;
  assign rf_ren_b = instr_valid_i & ~instr_fetch_err_i & ~illegal_insn_o & rf_ren_b_dec;

  assign rf_ren_a_o = rf_ren_a;
  assign rf_ren_b_o = rf_ren_b;

  logic [31:0] rf_rdata_a_fwd;
  logic [31:0] rf_rdata_b_fwd;

  // ALU Control
  alu_op_e     alu_operator;
  op_a_sel_e   alu_op_a_mux_sel, alu_op_a_mux_sel_dec;
  op_b_sel_e   alu_op_b_mux_sel, alu_op_b_mux_sel_dec;
  logic        alu_multicycle_dec;
  logic        stall_alu;

  logic [33:0] imd_val_q[2];

  op_a_sel_e   bt_a_mux_sel;
  imm_b_sel_e  bt_b_mux_sel;

  imm_a_sel_e  imm_a_mux_sel;
  imm_b_sel_e  imm_b_mux_sel, imm_b_mux_sel_dec;

  // Multiplier Control
  logic        mult_en_id, mult_en_dec; // use integer multiplier
  logic        div_en_id, div_en_dec;   // use integer division or reminder
  logic        multdiv_en_dec;
  md_op_e      multdiv_operator;
  logic [1:0]  multdiv_signed_mode;

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req, lsu_req_dec;
  logic        data_req_allowed;

  // CSR control
  logic        csr_pipe_flush;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  /////////////
  // LSU Mux //
  /////////////

  // Misaligned loads/stores result in two aligned loads/stores, compute second address
  assign alu_op_a_mux_sel = lsu_addr_incr_req_i ? OP_A_FWD        : alu_op_a_mux_sel_dec;
  assign alu_op_b_mux_sel = lsu_addr_incr_req_i ? OP_B_IMM        : alu_op_b_mux_sel_dec;
  assign imm_b_mux_sel    = lsu_addr_incr_req_i ? IMM_B_INCR_ADDR : imm_b_mux_sel_dec;

  ///////////////////
  // Operand MUXES //
  ///////////////////

  // Main ALU immediate MUX for Operand A
  assign imm_a = (imm_a_mux_sel == IMM_A_Z) ? zimm_rs1_type : '0;

  // Main ALU MUX for Operand A
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REG_A:  alu_operand_a = rf_rdata_a_fwd;
      OP_A_FWD:    alu_operand_a = lsu_addr_last_i;
      OP_A_CURRPC: alu_operand_a = pc_id_i;
      OP_A_IMM:    alu_operand_a = imm_a;
      default:     alu_operand_a = pc_id_i;
    endcase
  end

  if (BranchTargetALU) begin : g_btalu_muxes
    // Branch target ALU operand A mux
    always_comb begin : bt_operand_a_mux
      unique case (bt_a_mux_sel)
        OP_A_REG_A:  bt_a_operand_o = rf_rdata_a_fwd;
        OP_A_CURRPC: bt_a_operand_o = pc_id_i;
        default:     bt_a_operand_o = pc_id_i;
      endcase
    end

    // Branch target ALU operand B mux
    always_comb begin : bt_immediate_b_mux
      unique case (bt_b_mux_sel)
        IMM_B_I:         bt_b_operand_o = imm_i_type;
        IMM_B_B:         bt_b_operand_o = imm_b_type;
        IMM_B_J:         bt_b_operand_o = imm_j_type;
        IMM_B_INCR_PC:   bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
        default:         bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
      endcase
    end

    // Reduced main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_U,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end else begin : g_nobtalu
    op_a_sel_e  unused_a_mux_sel;
    imm_b_sel_e unused_b_mux_sel;

    assign unused_a_mux_sel = bt_a_mux_sel;
    assign unused_b_mux_sel = bt_b_mux_sel;
    assign bt_a_operand_o   = '0;
    assign bt_b_operand_o   = '0;

    // Full main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_B:         imm_b = imm_b_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_J:         imm_b = imm_j_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_B,
        IMM_B_U,
        IMM_B_J,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end

  // ALU MUX for Operand B
  assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : rf_rdata_b_fwd;

  /////////////////////////////////////////
  // Multicycle Operation Stage Register //
  /////////////////////////////////////////

  for (genvar i=0; i<2; i++) begin : gen_intermediate_val_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : intermediate_val_reg
      if (!rst_ni) begin
        imd_val_q[i] <= '0;
      end else if (imd_val_we_ex_i[i]) begin
        imd_val_q[i] <= imd_val_d_ex_i[i];
      end
    end
  end

  assign imd_val_q_ex_o = imd_val_q;

  ///////////////////////
  // Register File MUX //
  ///////////////////////

  // Suppress register write if there is an illegal CSR access or instruction is not executing
  assign rf_we_id_o = rf_we_raw & instr_executing & ~illegal_csr_insn_i;

  // Register file write data mux
  always_comb begin : rf_wdata_id_mux
    unique case (rf_wdata_sel)
      RF_WD_EX:  rf_wdata_id_o = result_ex_i;
      RF_WD_CSR: rf_wdata_id_o = csr_rdata_i;
      default:   rf_wdata_id_o = result_ex_i;
    endcase
  end

  /////////////
  // Decoder //
  /////////////

  ibex_decoder #(
      .RV32E           ( RV32E           ),
      .RV32M           ( RV32M           ),
      .RV32B           ( RV32B           ),
      .BranchTargetALU ( BranchTargetALU )
  ) decoder_i (
      .clk_i                           ( clk_i                ),
      .rst_ni                          ( rst_ni               ),

      // controller
      .illegal_insn_o                  ( illegal_insn_dec     ),
      .ebrk_insn_o                     ( ebrk_insn            ),
      .mret_insn_o                     ( mret_insn_dec        ),
      .dret_insn_o                     ( dret_insn_dec        ),
      .ecall_insn_o                    ( ecall_insn_dec       ),
      .wfi_insn_o                      ( wfi_insn_dec         ),
      .jump_set_o                      ( jump_set_dec         ),
      .branch_taken_i                  ( branch_taken         ),
      .icache_inval_o                  ( icache_inval_o       ),

      // from IF-ID pipeline register
      .instr_first_cycle_i             ( instr_first_cycle    ),
      .instr_rdata_i                   ( instr_rdata_i        ),
      .instr_rdata_alu_i               ( instr_rdata_alu_i    ),
      .illegal_c_insn_i                ( illegal_c_insn_i     ),

      // immediates
      .imm_a_mux_sel_o                 ( imm_a_mux_sel        ),
      .imm_b_mux_sel_o                 ( imm_b_mux_sel_dec    ),
      .bt_a_mux_sel_o                  ( bt_a_mux_sel         ),
      .bt_b_mux_sel_o                  ( bt_b_mux_sel         ),

      .imm_i_type_o                    ( imm_i_type           ),
      .imm_s_type_o                    ( imm_s_type           ),
      .imm_b_type_o                    ( imm_b_type           ),
      .imm_u_type_o                    ( imm_u_type           ),
      .imm_j_type_o                    ( imm_j_type           ),
      .zimm_rs1_type_o                 ( zimm_rs1_type        ),

      // register file
      .rf_wdata_sel_o                  ( rf_wdata_sel         ),
      .rf_we_o                         ( rf_we_dec            ),

      .rf_raddr_a_o                    ( rf_raddr_a_o         ),
      .rf_raddr_b_o                    ( rf_raddr_b_o         ),
      .rf_waddr_o                      ( rf_waddr_id_o        ),
      .rf_ren_a_o                      ( rf_ren_a_dec         ),
      .rf_ren_b_o                      ( rf_ren_b_dec         ),

      // ALU
      .alu_operator_o                  ( alu_operator         ),
      .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel_dec ),
      .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel_dec ),
      .alu_multicycle_o                ( alu_multicycle_dec   ),

      // MULT & DIV
      .mult_en_o                       ( mult_en_dec          ),
      .div_en_o                        ( div_en_dec           ),
      .mult_sel_o                      ( mult_sel_ex_o        ),
      .div_sel_o                       ( div_sel_ex_o         ),
      .multdiv_operator_o              ( multdiv_operator     ),
      .multdiv_signed_mode_o           ( multdiv_signed_mode  ),

      // CSRs
      .csr_access_o                    ( csr_access_o         ),
      .csr_op_o                        ( csr_op_o             ),

      // LSU
      .data_req_o                      ( lsu_req_dec          ),
      .data_we_o                       ( lsu_we               ),
      .data_type_o                     ( lsu_type             ),
      .data_sign_extension_o           ( lsu_sign_ext         ),

      // jump/branches
      .jump_in_dec_o                   ( jump_in_dec          ),
      .branch_in_dec_o                 ( branch_in_dec        )
  );

  /////////////////////////////////
  // CSR-related pipline flushes //
  /////////////////////////////////
  always_comb begin : csr_pipeline_flushes
    csr_pipe_flush = 1'b0;

    // A pipeline flush is needed to let the controller react after modifying certain CSRs:
    // - When enabling interrupts, pending IRQs become visible to the controller only during
    //   the next cycle. If during that cycle the core disables interrupts again, it does not
    //   see any pending IRQs and consequently does not start to handle interrupts.
    // - When modifying debug CSRs - TODO: Check if this is really needed
    if (csr_op_en_o == 1'b1 && (csr_op_o == CSR_OP_WRITE || csr_op_o == CSR_OP_SET)) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_MSTATUS   ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_MIE) begin
        csr_pipe_flush = 1'b1;
      end
    end else if (csr_op_en_o == 1'b1 && csr_op_o != CSR_OP_READ) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_DCSR      ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DPC       ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH0 ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH1) begin
        csr_pipe_flush = 1'b1;
      end
    end
  end

  ////////////////
  // Controller //
  ////////////////

  assign illegal_insn_o = instr_valid_i & (illegal_insn_dec | illegal_csr_insn_i);

  ibex_controller #(
    .WritebackStage  ( WritebackStage  ),
    .BranchPredictor ( BranchPredictor )
  ) controller_i (
      .clk_i                          ( clk_i                   ),
      .rst_ni                         ( rst_ni                  ),

      .ctrl_busy_o                    ( ctrl_busy_o             ),

      // decoder related signals
      .illegal_insn_i                 ( illegal_insn_o          ),
      .ecall_insn_i                   ( ecall_insn_dec          ),
      .mret_insn_i                    ( mret_insn_dec           ),
      .dret_insn_i                    ( dret_insn_dec           ),
      .wfi_insn_i                     ( wfi_insn_dec            ),
      .ebrk_insn_i                    ( ebrk_insn               ),
      .csr_pipe_flush_i               ( csr_pipe_flush          ),

      // from IF-ID pipeline
      .instr_valid_i                  ( instr_valid_i           ),
      .instr_i                        ( instr_rdata_i           ),
      .instr_compressed_i             ( instr_rdata_c_i         ),
      .instr_is_compressed_i          ( instr_is_compressed_i   ),
      .instr_bp_taken_i               ( instr_bp_taken_i        ),
      .instr_fetch_err_i              ( instr_fetch_err_i       ),
      .instr_fetch_err_plus2_i        ( instr_fetch_err_plus2_i ),
      .pc_id_i                        ( pc_id_i                 ),

      // to IF-ID pipeline
      .instr_valid_clear_o            ( instr_valid_clear_o     ),
      .id_in_ready_o                  ( id_in_ready_o           ),
      .controller_run_o               ( controller_run          ),

      // to prefetcher
      .instr_req_o                    ( instr_req_o             ),
      .pc_set_o                       ( pc_set_o                ),
      .pc_set_spec_o                  ( pc_set_spec_o           ),
      .pc_mux_o                       ( pc_mux_o                ),
      .nt_branch_mispredict_o         ( nt_branch_mispredict_o  ),
      .exc_pc_mux_o                   ( exc_pc_mux_o            ),
      .exc_cause_o                    ( exc_cause_o             ),

      // LSU
      .lsu_addr_last_i                ( lsu_addr_last_i         ),
      .load_err_i                     ( lsu_load_err_i          ),
      .store_err_i                    ( lsu_store_err_i         ),
      .wb_exception_o                 ( wb_exception            ),

      // jump/branch control
      .branch_set_i                   ( branch_set              ),
      .branch_set_spec_i              ( branch_set_spec         ),
      .branch_not_set_i               ( branch_not_set          ),
      .jump_set_i                     ( jump_set                ),

      // interrupt signals
      .csr_mstatus_mie_i              ( csr_mstatus_mie_i       ),
      .irq_pending_i                  ( irq_pending_i           ),
      .irqs_i                         ( irqs_i                  ),
      .irq_nm_i                       ( irq_nm_i                ),
      .nmi_mode_o                     ( nmi_mode_o              ),

      // CSR Controller Signals
      .csr_save_if_o                  ( csr_save_if_o           ),
      .csr_save_id_o                  ( csr_save_id_o           ),
      .csr_save_wb_o                  ( csr_save_wb_o           ),
      .csr_restore_mret_id_o          ( csr_restore_mret_id_o   ),
      .csr_restore_dret_id_o          ( csr_restore_dret_id_o   ),
      .csr_save_cause_o               ( csr_save_cause_o        ),
      .csr_mtval_o                    ( csr_mtval_o             ),
      .priv_mode_i                    ( priv_mode_i             ),
      .csr_mstatus_tw_i               ( csr_mstatus_tw_i        ),

      // Debug Signal
      .debug_mode_o                   ( debug_mode_o            ),
      .debug_cause_o                  ( debug_cause_o           ),
      .debug_csr_save_o               ( debug_csr_save_o        ),
      .debug_req_i                    ( debug_req_i             ),
      .debug_single_step_i            ( debug_single_step_i     ),
      .debug_ebreakm_i                ( debug_ebreakm_i         ),
      .debug_ebreaku_i                ( debug_ebreaku_i         ),
      .trigger_match_i                ( trigger_match_i         ),

      .stall_id_i                     ( stall_id                ),
      .stall_wb_i                     ( stall_wb                ),
      .flush_id_o                     ( flush_id                ),
      .ready_wb_i                     ( ready_wb_i              ),

      // Performance Counters
      .perf_jump_o                    ( perf_jump_o             ),
      .perf_tbranch_o                 ( perf_tbranch_o          )
  );

  assign multdiv_en_dec   = mult_en_dec | div_en_dec;

  assign lsu_req         = instr_executing ? data_req_allowed & lsu_req_dec  : 1'b0;
  assign mult_en_id      = instr_executing ? mult_en_dec                     : 1'b0;
  assign div_en_id       = instr_executing ? div_en_dec                      : 1'b0;

  assign lsu_req_o               = lsu_req;
  assign lsu_we_o                = lsu_we;
  assign lsu_type_o              = lsu_type;
  assign lsu_sign_ext_o          = lsu_sign_ext;
  assign lsu_wdata_o             = rf_rdata_b_fwd;
  // csr_op_en_o is set when CSR access should actually happen.
  // csv_access_o is set when CSR access instruction is present and is used to compute whether a CSR
  // access is illegal. A combinational loop would be created if csr_op_en_o was used along (as
  // asserting it for an illegal csr access would result in a flush that would need to deassert it).
  assign csr_op_en_o             = csr_access_o & instr_executing & instr_id_done_o;

  assign alu_operator_ex_o           = alu_operator;
  assign alu_operand_a_ex_o          = alu_operand_a;
  assign alu_operand_b_ex_o          = alu_operand_b;

  assign mult_en_ex_o                = mult_en_id;
  assign div_en_ex_o                 = div_en_id;

  assign multdiv_operator_ex_o       = multdiv_operator;
  assign multdiv_signed_mode_ex_o    = multdiv_signed_mode;
  assign multdiv_operand_a_ex_o      = rf_rdata_a_fwd;
  assign multdiv_operand_b_ex_o      = rf_rdata_b_fwd;

  ////////////////////////
  // Branch set control //
  ////////////////////////

  if (BranchTargetALU && !DataIndTiming) begin : g_branch_set_direct
    // Branch set fed straight to controller with branch target ALU
    // (condition pass/fail used same cycle as generated instruction request)
    assign branch_set_raw      = branch_set_raw_d;
    assign branch_set_raw_spec = branch_spec;
  end else begin : g_branch_set_flop
    // Branch set flopped without branch target ALU, or in fixed time execution mode
    // (condition pass/fail used next cycle where branch target is calculated)
    logic branch_set_raw_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_set_raw_q <= 1'b0;
      end else begin
        branch_set_raw_q <= branch_set_raw_d;
      end
    end

    // Branches always take two cycles in fixed time execution mode, with or without the branch
    // target ALU (to avoid a path from the branch decision into the branch target ALU operand
    // muxing).
    assign branch_set_raw      = (BranchTargetALU && !data_ind_timing_i) ? branch_set_raw_d :
                                                                           branch_set_raw_q;

    // Use the speculative branch signal when BTALU is enabled
    assign branch_set_raw_spec = (BranchTargetALU && !data_ind_timing_i) ? branch_spec :
                                                                           branch_set_raw_q;
  end

  // Track whether the current instruction in ID/EX has done a branch or jump set.
  assign branch_jump_set_done_d = (branch_set_raw | jump_set_raw | branch_jump_set_done_q) &
    ~instr_valid_clear_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      branch_jump_set_done_q <= 1'b0;
    end else begin
      branch_jump_set_done_q <= branch_jump_set_done_d;
    end
  end

  // the _raw signals from the state machine may be asserted for multiple cycles when
  // instr_executing_spec is asserted and instr_executing is not asserted. This may occur where
  // a memory error is seen or a there are outstanding memory accesses (indicate a load or store is
  // in the WB stage). The branch or jump speculatively begins the fetch but is held back from
  // completing until it is certain the outstanding access hasn't seen a memory error. This logic
  // ensures only the first cycle of a branch or jump set is sent to the controller to prevent
  // needless extra IF flushes and fetches.
  assign jump_set        = jump_set_raw        & ~branch_jump_set_done_q;
  assign branch_set      = branch_set_raw      & ~branch_jump_set_done_q;
  assign branch_set_spec = branch_set_raw_spec & ~branch_jump_set_done_q;

  // Branch condition is calculated in the first cycle and flopped for use in the second cycle
  // (only used in fixed time execution mode to determine branch destination).
  if (DataIndTiming) begin : g_sec_branch_taken
    logic branch_taken_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_taken_q <= 1'b0;
      end else begin
        branch_taken_q <= branch_decision_i;
      end
    end

    assign branch_taken = ~data_ind_timing_i | branch_taken_q;

  end else begin : g_nosec_branch_taken

    // Signal unused without fixed time execution mode - only taken branches will trigger
    // branch_set_raw
    assign branch_taken = 1'b1;

  end

  // Holding branch_set/jump_set high for more than one cycle should not cause a functional issue.
  // However it could generate needless prefetch buffer flushes and instruction fetches. The ID/EX
  // designs ensures that this never happens for non-predicted branches.
  `ASSERT(NeverDoubleBranch, branch_set & ~instr_bp_taken_i |=> ~branch_set)
  `ASSERT(NeverDoubleJump, jump_set & ~instr_bp_taken_i |=> ~jump_set)

  ///////////////
  // ID-EX FSM //
  ///////////////

  typedef enum logic { FIRST_CYCLE, MULTI_CYCLE } id_fsm_e;
  id_fsm_e id_fsm_q, id_fsm_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : id_pipeline_reg
    if (!rst_ni) begin
      id_fsm_q <= FIRST_CYCLE;
    end else if (instr_executing) begin
      id_fsm_q <= id_fsm_d;
    end
  end

  // ID/EX stage can be in two states, FIRST_CYCLE and MULTI_CYCLE. An instruction enters
  // MULTI_CYCLE if it requires multiple cycles to complete regardless of stalls and other
  // considerations. An instruction may be held in FIRST_CYCLE if it's unable to begin executing
  // (this is controlled by instr_executing).

  always_comb begin
    id_fsm_d                = id_fsm_q;
    rf_we_raw               = rf_we_dec;
    stall_multdiv           = 1'b0;
    stall_jump              = 1'b0;
    stall_branch            = 1'b0;
    stall_alu               = 1'b0;
    branch_set_raw_d        = 1'b0;
    branch_spec             = 1'b0;
    branch_not_set          = 1'b0;
    jump_set_raw            = 1'b0;
    perf_branch_o           = 1'b0;

    if (instr_executing_spec) begin
      unique case (id_fsm_q)
        FIRST_CYCLE: begin
          unique case (1'b1)
            lsu_req_dec: begin
              if (!WritebackStage) begin
                // LSU operation
                id_fsm_d    = MULTI_CYCLE;
              end else begin
                if(~lsu_req_done_i) begin
                  id_fsm_d  = MULTI_CYCLE;
                end
              end
            end
            multdiv_en_dec: begin
              // MUL or DIV operation
              if (~ex_valid_i) begin
                // When single-cycle multiply is configured mul can finish in the first cycle so
                // only enter MULTI_CYCLE state if a result isn't immediately available
                id_fsm_d      = MULTI_CYCLE;
                rf_we_raw     = 1'b0;
                stall_multdiv = 1'b1;
              end
            end
            branch_in_dec: begin
              // cond branch operation
              // All branches take two cycles in fixed time execution mode, regardless of branch
              // condition.
              id_fsm_d         = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i)) ?
                                     MULTI_CYCLE : FIRST_CYCLE;
              stall_branch     = (~BranchTargetALU & branch_decision_i) | data_ind_timing_i;
              branch_set_raw_d = (branch_decision_i | data_ind_timing_i);

              if (BranchPredictor) begin
                branch_not_set = ~branch_decision_i;
              end

              // Speculative branch (excludes branch_decision_i)
              branch_spec   = SpecBranch ? 1'b1 : branch_decision_i;
              perf_branch_o = 1'b1;
            end
            jump_in_dec: begin
              // uncond branch operation
              // BTALU means jumps only need one cycle
              id_fsm_d      = BranchTargetALU ? FIRST_CYCLE : MULTI_CYCLE;
              stall_jump    = ~BranchTargetALU;
              jump_set_raw  = jump_set_dec;
            end
            alu_multicycle_dec: begin
              stall_alu     = 1'b1;
              id_fsm_d      = MULTI_CYCLE;
              rf_we_raw     = 1'b0;
            end
            default: begin
              id_fsm_d      = FIRST_CYCLE;
            end
          endcase
        end

        MULTI_CYCLE: begin
          if(multdiv_en_dec) begin
            rf_we_raw       = rf_we_dec & ex_valid_i;
          end

          if (multicycle_done & ready_wb_i) begin
            id_fsm_d        = FIRST_CYCLE;
          end else begin
            stall_multdiv   = multdiv_en_dec;
            stall_branch    = branch_in_dec;
            stall_jump      = jump_in_dec;
          end
        end

        default: begin
          id_fsm_d          = FIRST_CYCLE;
        end
      endcase
    end
  end

  // Note for the two-stage configuration ready_wb_i is always set
  assign multdiv_ready_id_o = ready_wb_i;

  `ASSERT(StallIDIfMulticycle, (id_fsm_q == FIRST_CYCLE) & (id_fsm_d == MULTI_CYCLE) |-> stall_id)


  // Stall ID/EX stage for reason that relates to instruction in ID/EX, update assertion below if
  // modifying this.
  assign stall_id = stall_ld_hz | stall_mem | stall_multdiv | stall_jump | stall_branch |
                      stall_alu;

  // Generally illegal instructions have no reason to stall, however they must still stall waiting
  // for outstanding memory requests so exceptions related to them take priority over the illegal
  // instruction exception.
  `ASSERT(IllegalInsnStallMustBeMemStall, illegal_insn_o & stall_id |-> stall_mem &
    ~(stall_ld_hz | stall_multdiv | stall_jump | stall_branch | stall_alu))

  assign instr_done = ~stall_id & ~flush_id & instr_executing;

  // Signal instruction in ID is in it's first cycle. It can remain in its
  // first cycle if it is stalled.
  assign instr_first_cycle      = instr_valid_i & (id_fsm_q == FIRST_CYCLE);
  // Used by RVFI to know when to capture register read data
  // Used by ALU to access RS3 if ternary instruction.
  assign instr_first_cycle_id_o = instr_first_cycle;

  if (WritebackStage) begin : gen_stall_mem
    // Register read address matches write address in WB
    logic rf_rd_a_wb_match;
    logic rf_rd_b_wb_match;
    // Hazard between registers being read and written
    logic rf_rd_a_hz;
    logic rf_rd_b_hz;

    logic outstanding_memory_access;

    logic instr_kill;

    assign multicycle_done = lsu_req_dec ? ~stall_mem : ex_valid_i;

    // Is a memory access ongoing that isn't finishing this cycle
    assign outstanding_memory_access = (outstanding_load_wb_i | outstanding_store_wb_i) &
                                       ~lsu_resp_valid_i;

    // Can start a new memory access if any previous one has finished or is finishing
    assign data_req_allowed = ~outstanding_memory_access;

    // Instruction won't execute because:
    // - There is a pending exception in writeback
    //   The instruction in ID/EX will be flushed and the core will jump to an exception handler
    // - The controller isn't running instructions
    //   This either happens in preparation for a flush and jump to an exception handler e.g. in
    //   response to an IRQ or debug request or whilst the core is sleeping or resetting/fetching
    //   first instruction in which case any valid instruction in ID/EX should be ignored.
    // - There was an error on instruction fetch
    assign instr_kill = instr_fetch_err_i |
                        wb_exception      |
                        ~controller_run;

    // With writeback stage instructions must be prevented from executing if there is:
    // - A load hazard
    // - A pending memory access
    //   If it receives an error response this results in a precise exception from WB so ID/EX
    //   instruction must not execute until error response is known).
    // - A load/store error
    //   This will cause a precise exception for the instruction in WB so ID/EX instruction must not
    //   execute
    //
    // instr_executing_spec is a speculative signal. It indicates an instruction can execute
    // assuming there are no exceptions from writeback and any outstanding memory access won't
    // receive an error. It is required so branch and jump requests don't factor in an incoming dmem
    // error (that in turn would factor directly into imem requests leading to a feedthrough path).
    //
    // instr_executing is the full signal, it will only allow execution once any potential
    // exceptions from writeback have been resolved.
    assign instr_executing_spec = instr_valid_i      &
                                  ~instr_fetch_err_i &
                                  controller_run     &
                                  ~stall_ld_hz;

    assign instr_executing = instr_valid_i              &
                             ~instr_kill                &
                             ~stall_ld_hz               &
                             ~outstanding_memory_access;

    `ASSERT(IbexExecutingSpecIfExecuting, instr_executing |-> instr_executing_spec)

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_kill & ~instr_executing |-> stall_id)

    `ASSERT(IbexCannotRetireWithPendingExceptions,
      instr_done |-> ~(wb_exception | outstanding_memory_access))

    // Stall for reasons related to memory:
    // * There is an outstanding memory access that won't resolve this cycle (need to wait to allow
    //   precise exceptions)
    // * There is a load/store request not being granted or which is unaligned and waiting to issue
    //   a second request (needs to stay in ID for the address calculation)
    assign stall_mem = instr_valid_i &
                       (outstanding_memory_access | (lsu_req_dec & ~lsu_req_done_i));

    // If we stall a load in ID for any reason, it must not make an LSU request
    // (otherwide we might issue two requests for the same instruction)
    `ASSERT(IbexStallMemNoRequest,
      instr_valid_i & lsu_req_dec & ~instr_done |-> ~lsu_req_done_i)

    assign rf_rd_a_wb_match = (rf_waddr_wb_i == rf_raddr_a_o) & |rf_raddr_a_o;
    assign rf_rd_b_wb_match = (rf_waddr_wb_i == rf_raddr_b_o) & |rf_raddr_b_o;

    assign rf_rd_a_wb_match_o = rf_rd_a_wb_match;
    assign rf_rd_b_wb_match_o = rf_rd_b_wb_match;

    // If instruction is reading register that load will be writing stall in
    // ID until load is complete. No need to stall when reading zero register.
    assign rf_rd_a_hz = rf_rd_a_wb_match & rf_ren_a;
    assign rf_rd_b_hz = rf_rd_b_wb_match & rf_ren_b;

    // If instruction is read register that writeback is writing forward writeback data to read
    // data. Note this doesn't factor in load data as it arrives too late, such hazards are
    // resolved via a stall (see above).
    assign rf_rdata_a_fwd = rf_rd_a_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rd_b_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_b_i;

    assign stall_ld_hz = outstanding_load_wb_i & (rf_rd_a_hz | rf_rd_b_hz);

    assign instr_type_wb_o = ~lsu_req_dec ? WB_INSTR_OTHER :
                              lsu_we      ? WB_INSTR_STORE :
                                            WB_INSTR_LOAD;

    assign instr_id_done_o = en_wb_o & ready_wb_i;

    // Stall ID/EX as instruction in ID/EX cannot proceed to writeback yet
    assign stall_wb = en_wb_o & ~ready_wb_i;

    assign perf_dside_wait_o = instr_valid_i & ~instr_kill &
                               (outstanding_memory_access | stall_ld_hz);
  end else begin : gen_no_stall_mem

    assign multicycle_done = lsu_req_dec ? lsu_resp_valid_i : ex_valid_i;

    assign data_req_allowed = instr_first_cycle;

    // Without Writeback Stage always stall the first cycle of a load/store.
    // Then stall until it is complete
    assign stall_mem = instr_valid_i & (lsu_req_dec & (~lsu_resp_valid_i | instr_first_cycle));

    // No load hazards without Writeback Stage
    assign stall_ld_hz   = 1'b0;

    // Without writeback stage any valid instruction that hasn't seen an error will execute
    assign instr_executing_spec = instr_valid_i & ~instr_fetch_err_i & controller_run;
    assign instr_executing = instr_executing_spec;

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_fetch_err_i & ~instr_executing & controller_run |-> stall_id)

    // No data forwarding without writeback stage so always take source register data direct from
    // register file
    assign rf_rdata_a_fwd = rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rdata_b_i;

    assign rf_rd_a_wb_match_o = 1'b0;
    assign rf_rd_b_wb_match_o = 1'b0;

    // Unused Writeback stage only IO & wiring
    // Assign inputs and internal wiring to unused signals to satisfy lint checks
    // Tie-off outputs to constant values
    logic unused_data_req_done_ex;
    logic [4:0] unused_rf_waddr_wb;
    logic unused_rf_write_wb;
    logic unused_outstanding_load_wb;
    logic unused_outstanding_store_wb;
    logic unused_wb_exception;
    logic [31:0] unused_rf_wdata_fwd_wb;

    assign unused_data_req_done_ex     = lsu_req_done_i;
    assign unused_rf_waddr_wb          = rf_waddr_wb_i;
    assign unused_rf_write_wb          = rf_write_wb_i;
    assign unused_outstanding_load_wb  = outstanding_load_wb_i;
    assign unused_outstanding_store_wb = outstanding_store_wb_i;
    assign unused_wb_exception         = wb_exception;
    assign unused_rf_wdata_fwd_wb      = rf_wdata_fwd_wb_i;

    assign instr_type_wb_o = WB_INSTR_OTHER;
    assign stall_wb        = 1'b0;

    assign perf_dside_wait_o = instr_executing & lsu_req_dec & ~lsu_resp_valid_i;

    assign instr_id_done_o = instr_done;
  end

  // Signal which instructions to count as retired in minstret, all traps along with ebrk and
  // ecall instructions are not counted.
  assign instr_perf_count_id_o = ~ebrk_insn & ~ecall_insn_dec & ~illegal_insn_dec &
      ~illegal_csr_insn_i & ~instr_fetch_err_i;

  // An instruction is ready to move to the writeback stage (or retire if there is no writeback
  // stage)
  assign en_wb_o = instr_done;

  assign perf_mul_wait_o = stall_multdiv & mult_en_dec;
  assign perf_div_wait_o = stall_multdiv & div_en_dec;

  //////////
  // FCOV //
  //////////

  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_rd_wb_hz,
    (gen_stall_mem.rf_rd_a_hz | gen_stall_mem.rf_rd_b_hz) & instr_valid_i, WritebackStage)
  `DV_FCOV_SIGNAL(logic, branch_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & branch_decision_i)
  `DV_FCOV_SIGNAL(logic, branch_not_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & ~branch_decision_i)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN_IF(IbexAluOpMuxSelKnown, alu_op_a_mux_sel, instr_valid_i)
  `ASSERT(IbexAluAOpMuxSelValid, instr_valid_i |-> alu_op_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_FWD,
      OP_A_CURRPC,
      OP_A_IMM})
  `ASSERT_KNOWN_IF(IbexBTAluAOpMuxSelKnown, bt_a_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluAOpMuxSelValid, instr_valid_i |-> bt_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_CURRPC})
  `ASSERT_KNOWN_IF(IbexBTAluBOpMuxSelKnown, bt_b_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluBOpMuxSelValid, instr_valid_i |-> bt_b_mux_sel inside {
      IMM_B_I,
      IMM_B_B,
      IMM_B_J,
      IMM_B_INCR_PC})
  `ASSERT(IbexRegfileWdataSelValid, instr_valid_i |-> rf_wdata_sel inside {
      RF_WD_EX,
      RF_WD_CSR})
  `ASSERT_KNOWN(IbexWbStateKnown, id_fsm_q)

  // Branch decision must be valid when jumping.
  `ASSERT_KNOWN_IF(IbexBranchDecisionValid, branch_decision_i,
      instr_valid_i && !(illegal_csr_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrKnown, instr_rdata_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrALUKnown, instr_rdata_alu_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Multicycle enable signals must be unique.
  `ASSERT(IbexMulticycleEnableUnique,
      $onehot0({lsu_req_dec, multdiv_en_dec, branch_in_dec, jump_in_dec}))

  // Duplicated instruction flops must match
  // === as DV environment can produce instructions with Xs in, so must use precise match that
  // includes Xs
  `ASSERT(IbexDuplicateInstrMatch, instr_valid_i |-> instr_rdata_i === instr_rdata_alu_i)

  `ifdef CHECK_MISALIGNED
  `ASSERT(IbexMisalignedMemoryAccess, !lsu_addr_incr_req_i)
  `endif

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Instruction Fetch Stage
 *
 * Instruction fetch unit: Selection of the next PC, and buffering (sampling) of
 * the read instruction.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_if_stage import ibex_pkg::*; #(
    parameter int unsigned DmHaltAddr        = 32'h1A110800,
    parameter int unsigned DmExceptionAddr   = 32'h1A110808,
    parameter bit          DummyInstructions = 1'b0,
    parameter bit          ICache            = 1'b0,
    parameter bit          ICacheECC         = 1'b0,
    parameter int unsigned BusSizeECC        = BUS_SIZE,
    parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
    parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
    parameter bit          PCIncrCheck       = 1'b0,
    parameter bit          ResetAll          = 1'b0,
    parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
    parameter bit          BranchPredictor   = 1'b0
) (
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic [31:0]                  boot_addr_i,              // also used for mtvec
    input  logic                         req_i,                    // instruction request control

    // instruction cache interface
    output logic                        instr_req_o,
    output logic [31:0]                 instr_addr_o,
    input  logic                        instr_gnt_i,
    input  logic                        instr_rvalid_i,
    input  logic [31:0]                 instr_rdata_i,
    input  logic                        instr_err_i,
    input  logic                        instr_pmp_err_i,

    // ICache RAM IO
    output logic [IC_NUM_WAYS-1:0]      ic_tag_req_o,
    output logic                        ic_tag_write_o,
    output logic [IC_INDEX_W-1:0]       ic_tag_addr_o,
    output logic [TagSizeECC-1:0]       ic_tag_wdata_o,
    input  logic [TagSizeECC-1:0]       ic_tag_rdata_i [IC_NUM_WAYS],
    output logic [IC_NUM_WAYS-1:0]      ic_data_req_o,
    output logic                        ic_data_write_o,
    output logic [IC_INDEX_W-1:0]       ic_data_addr_o,
    output logic [LineSizeECC-1:0]      ic_data_wdata_o,
    input  logic [LineSizeECC-1:0]      ic_data_rdata_i [IC_NUM_WAYS],

    // output of ID stage
    output logic                        instr_valid_id_o,         // instr in IF-ID is valid
    output logic                        instr_new_id_o,           // instr in IF-ID is new
    output logic [31:0]                 instr_rdata_id_o,         // instr for ID stage
    output logic [31:0]                 instr_rdata_alu_id_o,     // replicated instr for ID stage
                                                                  // to reduce fan-out
    output logic [15:0]                 instr_rdata_c_id_o,       // compressed instr for ID stage
                                                                  // (mtval), meaningful only if
                                                                  // instr_is_compressed_id_o = 1'b1
    output logic                        instr_is_compressed_id_o, // compressed decoder thinks this
                                                                  // is a compressed instr
    output logic                        instr_bp_taken_o,         // instruction was predicted to be
                                                                  // a taken branch
    output logic                        instr_fetch_err_o,        // bus error on fetch
    output logic                        instr_fetch_err_plus2_o,  // bus error misaligned
    output logic                        illegal_c_insn_id_o,      // compressed decoder thinks this
                                                                  // is an invalid instr
    output logic                        dummy_instr_id_o,         // Instruction is a dummy
    output logic [31:0]                 pc_if_o,
    output logic [31:0]                 pc_id_o,

    // control signals
    input  logic                        instr_valid_clear_i,      // clear instr valid bit in IF-ID
    input  logic                        pc_set_i,                 // set the PC to a new value
    input  logic                        pc_set_spec_i,
    input  pc_sel_e                     pc_mux_i,                 // selector for PC multiplexer
    input  logic                        nt_branch_mispredict_i,   // Not-taken branch in ID/EX was
                                                                  // mispredicted (predicted taken)
    input  exc_pc_sel_e                 exc_pc_mux_i,             // selects ISR address
    input  exc_cause_e                  exc_cause,                // selects ISR address for
                                                                  // vectorized interrupt lines
    input logic                         dummy_instr_en_i,
    input logic [2:0]                   dummy_instr_mask_i,
    input logic                         dummy_instr_seed_en_i,
    input logic [31:0]                  dummy_instr_seed_i,
    input logic                         icache_enable_i,
    input logic                         icache_inval_i,

    // jump and branch target
    input  logic [31:0]                 branch_target_ex_i,       // branch/jump target address

    // CSRs
    input  logic [31:0]                 csr_mepc_i,               // PC to restore after handling
                                                                  // the interrupt/exception
    input  logic [31:0]                 csr_depc_i,               // PC to restore after handling
                                                                  // the debug request
    input  logic [31:0]                 csr_mtvec_i,              // base PC to jump to on exception
    output logic                        csr_mtvec_init_o,         // tell CS regfile to init mtvec

    // pipeline stall
    input  logic                        id_in_ready_i,            // ID stage is ready for new instr

    // misc signals
    output logic                        pc_mismatch_alert_o,
    output logic                        if_busy_o                 // IF stage is busy fetching instr
);

  logic              instr_valid_id_d, instr_valid_id_q;
  logic              instr_new_id_d, instr_new_id_q;

  // prefetch buffer related signals
  logic              prefetch_busy;
  logic              branch_req;
  logic              branch_spec;
  logic              predicted_branch;
  logic       [31:0] fetch_addr_n;
  logic              unused_fetch_addr_n0;

  logic              fetch_valid;
  logic              fetch_ready;
  logic       [31:0] fetch_rdata;
  logic       [31:0] fetch_addr;
  logic              fetch_err;
  logic              fetch_err_plus2;

  logic              if_instr_valid;
  logic       [31:0] if_instr_rdata;
  logic       [31:0] if_instr_addr;
  logic              if_instr_err;

  logic       [31:0] exc_pc;

  logic        [5:0] irq_id;
  logic              unused_irq_bit;

  logic              if_id_pipe_reg_we; // IF-ID pipeline reg write enable

  // Dummy instruction signals
  logic              stall_dummy_instr;
  logic [31:0]       instr_out;
  logic              instr_is_compressed_out;
  logic              illegal_c_instr_out;
  logic              instr_err_out;

  logic              predict_branch_taken;
  logic       [31:0] predict_branch_pc;

  ibex_pkg::pc_sel_e pc_mux_internal;

  logic        [7:0] unused_boot_addr;
  logic        [7:0] unused_csr_mtvec;

  assign unused_boot_addr = boot_addr_i[7:0];
  assign unused_csr_mtvec = csr_mtvec_i[7:0];

  // extract interrupt ID from exception cause
  assign irq_id         = {exc_cause};
  assign unused_irq_bit = irq_id[5];   // MSB distinguishes interrupts from exceptions

  // exception PC selection mux
  always_comb begin : exc_pc_mux
    unique case (exc_pc_mux_i)
      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                    };
      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_id[4:0], 2'b00 };
      EXC_PC_DBD:     exc_pc = DmHaltAddr;
      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;
      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                    };
    endcase
  end

  // The Branch predictor can provide a new PC which is internal to if_stage. Only override the mux
  // select to choose this if the core isn't already trying to set a PC.
  assign pc_mux_internal =
    (BranchPredictor && predict_branch_taken && !pc_set_i) ? PC_BP : pc_mux_i;

  // fetch address selection mux
  always_comb begin : fetch_addr_mux
    unique case (pc_mux_internal)
      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
      PC_JUMP: fetch_addr_n = branch_target_ex_i;
      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler
      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC
      PC_DRET: fetch_addr_n = csr_depc_i;
      // Without branch predictor will never get pc_mux_internal == PC_BP. We still handle no branch
      // predictor case here to ensure redundant mux logic isn't synthesised.
      PC_BP:   fetch_addr_n = BranchPredictor ? predict_branch_pc : { boot_addr_i[31:8], 8'h80 };
      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;

  if (ICache) begin : gen_icache
    // Full I-Cache option
    ibex_icache #(
      .BranchPredictor (BranchPredictor),
      .ICacheECC       (ICacheECC),
      .ResetAll        (ResetAll),
      .BusSizeECC      (BusSizeECC),
      .TagSizeECC      (TagSizeECC),
      .LineSizeECC     (LineSizeECC)
    ) icache_i (
        .clk_i               ( clk_i                      ),
        .rst_ni              ( rst_ni                     ),

        .req_i               ( req_i                      ),

        .branch_i            ( branch_req                 ),
        .branch_spec_i       ( branch_spec                ),
        .predicted_branch_i  ( predicted_branch           ),
        .branch_mispredict_i ( nt_branch_mispredict_i     ),
        .addr_i              ( {fetch_addr_n[31:1], 1'b0} ),

        .ready_i             ( fetch_ready                ),
        .valid_o             ( fetch_valid                ),
        .rdata_o             ( fetch_rdata                ),
        .addr_o              ( fetch_addr                 ),
        .err_o               ( fetch_err                  ),
        .err_plus2_o         ( fetch_err_plus2            ),

        .instr_req_o         ( instr_req_o                ),
        .instr_addr_o        ( instr_addr_o               ),
        .instr_gnt_i         ( instr_gnt_i                ),
        .instr_rvalid_i      ( instr_rvalid_i             ),
        .instr_rdata_i       ( instr_rdata_i              ),
        .instr_err_i         ( instr_err_i                ),
        .instr_pmp_err_i     ( instr_pmp_err_i            ),

        .ic_tag_req_o        ( ic_tag_req_o               ),
        .ic_tag_write_o      ( ic_tag_write_o             ),
        .ic_tag_addr_o       ( ic_tag_addr_o              ),
        .ic_tag_wdata_o      ( ic_tag_wdata_o             ),
        .ic_tag_rdata_i      ( ic_tag_rdata_i             ),
        .ic_data_req_o       ( ic_data_req_o              ),
        .ic_data_write_o     ( ic_data_write_o            ),
        .ic_data_addr_o      ( ic_data_addr_o             ),
        .ic_data_wdata_o     ( ic_data_wdata_o            ),
        .ic_data_rdata_i     ( ic_data_rdata_i            ),

        .icache_enable_i     ( icache_enable_i            ),
        .icache_inval_i      ( icache_inval_i             ),
        .busy_o              ( prefetch_busy              )
    );
  end else begin : gen_prefetch_buffer
    // prefetch buffer, caches a fixed number of instructions
    ibex_prefetch_buffer #(
      .BranchPredictor (BranchPredictor),
      .ResetAll        (ResetAll)
    ) prefetch_buffer_i (
        .clk_i               ( clk_i                      ),
        .rst_ni              ( rst_ni                     ),

        .req_i               ( req_i                      ),

        .branch_i            ( branch_req                 ),
        .branch_spec_i       ( branch_spec                ),
        .predicted_branch_i  ( predicted_branch           ),
        .branch_mispredict_i ( nt_branch_mispredict_i     ),
        .addr_i              ( {fetch_addr_n[31:1], 1'b0} ),

        .ready_i             ( fetch_ready                ),
        .valid_o             ( fetch_valid                ),
        .rdata_o             ( fetch_rdata                ),
        .addr_o              ( fetch_addr                 ),
        .err_o               ( fetch_err                  ),
        .err_plus2_o         ( fetch_err_plus2            ),

        .instr_req_o         ( instr_req_o                ),
        .instr_addr_o        ( instr_addr_o               ),
        .instr_gnt_i         ( instr_gnt_i                ),
        .instr_rvalid_i      ( instr_rvalid_i             ),
        .instr_rdata_i       ( instr_rdata_i              ),
        .instr_err_i         ( instr_err_i                ),
        .instr_pmp_err_i     ( instr_pmp_err_i            ),

        .busy_o              ( prefetch_busy              )
    );
    // ICache tieoffs
    logic                   unused_icen, unused_icinv;
    logic [TagSizeECC-1:0]  unused_tag_ram_input [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] unused_data_ram_input [IC_NUM_WAYS];
    assign unused_icen           = icache_enable_i;
    assign unused_icinv          = icache_inval_i;
    assign unused_tag_ram_input  = ic_tag_rdata_i;
    assign unused_data_ram_input = ic_data_rdata_i;
    assign ic_tag_req_o          = 'b0;
    assign ic_tag_write_o        = 'b0;
    assign ic_tag_addr_o         = 'b0;
    assign ic_tag_wdata_o        = 'b0;
    assign ic_data_req_o         = 'b0;
    assign ic_data_write_o       = 'b0;
    assign ic_data_addr_o        = 'b0;
    assign ic_data_wdata_o       = 'b0;
  end

  assign unused_fetch_addr_n0 = fetch_addr_n[0];

  assign branch_req  = pc_set_i | predict_branch_taken;
  assign branch_spec = pc_set_spec_i | predict_branch_taken;

  assign pc_if_o     = if_instr_addr;
  assign if_busy_o   = prefetch_busy;

  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  logic [31:0] instr_decompressed;
  logic        illegal_c_insn;
  logic        instr_is_compressed;

  ibex_compressed_decoder compressed_decoder_i (
      .clk_i           ( clk_i                    ),
      .rst_ni          ( rst_ni                   ),
      .valid_i         ( fetch_valid & ~fetch_err ),
      .instr_i         ( if_instr_rdata           ),
      .instr_o         ( instr_decompressed       ),
      .is_compressed_o ( instr_is_compressed      ),
      .illegal_instr_o ( illegal_c_insn           )
  );

  // Dummy instruction insertion
  if (DummyInstructions) begin : gen_dummy_instr
    logic        insert_dummy_instr;
    logic [31:0] dummy_instr_data;

    ibex_dummy_instr #(
      .RndCnstLfsrSeed (RndCnstLfsrSeed),
      .RndCnstLfsrPerm (RndCnstLfsrPerm)
    ) dummy_instr_i (
      .clk_i                 ( clk_i                 ),
      .rst_ni                ( rst_ni                ),
      .dummy_instr_en_i      ( dummy_instr_en_i      ),
      .dummy_instr_mask_i    ( dummy_instr_mask_i    ),
      .dummy_instr_seed_en_i ( dummy_instr_seed_en_i ),
      .dummy_instr_seed_i    ( dummy_instr_seed_i    ),
      .fetch_valid_i         ( fetch_valid           ),
      .id_in_ready_i         ( id_in_ready_i         ),
      .insert_dummy_instr_o  ( insert_dummy_instr    ),
      .dummy_instr_data_o    ( dummy_instr_data      )
    );

    // Mux between actual instructions and dummy instructions
    assign instr_out               = insert_dummy_instr ? dummy_instr_data : instr_decompressed;
    assign instr_is_compressed_out = insert_dummy_instr ? 1'b0 : instr_is_compressed;
    assign illegal_c_instr_out     = insert_dummy_instr ? 1'b0 : illegal_c_insn;
    assign instr_err_out           = insert_dummy_instr ? 1'b0 : if_instr_err;

    // Stall the IF stage if we insert a dummy instruction. The dummy will execute between whatever
    // is currently in the ID stage and whatever is valid from the prefetch buffer this cycle. The
    // PC of the dummy instruction will match whatever is next from the prefetch buffer.
    assign stall_dummy_instr = insert_dummy_instr;

    // Register the dummy instruction indication into the ID stage
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        dummy_instr_id_o <= 1'b0;
      end else if (if_id_pipe_reg_we) begin
        dummy_instr_id_o <= insert_dummy_instr;
      end
    end

  end else begin : gen_no_dummy_instr
    logic        unused_dummy_en;
    logic [2:0]  unused_dummy_mask;
    logic        unused_dummy_seed_en;
    logic [31:0] unused_dummy_seed;

    assign unused_dummy_en         = dummy_instr_en_i;
    assign unused_dummy_mask       = dummy_instr_mask_i;
    assign unused_dummy_seed_en    = dummy_instr_seed_en_i;
    assign unused_dummy_seed       = dummy_instr_seed_i;
    assign instr_out               = instr_decompressed;
    assign instr_is_compressed_out = instr_is_compressed;
    assign illegal_c_instr_out     = illegal_c_insn;
    assign instr_err_out           = if_instr_err;
    assign stall_dummy_instr       = 1'b0;
    assign dummy_instr_id_o        = 1'b0;
  end

  // The ID stage becomes valid as soon as any instruction is registered in the ID stage flops.
  // Note that the current instruction is squashed by the incoming pc_set_i signal.
  // Valid is held until it is explicitly cleared (due to an instruction completing or an exception)
  assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |
                            (instr_valid_id_q & ~instr_valid_clear_i);
  assign instr_new_id_d   = if_instr_valid & id_in_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_valid_id_q <= 1'b0;
      instr_new_id_q   <= 1'b0;
    end else begin
      instr_valid_id_q <= instr_valid_id_d;
      instr_new_id_q   <= instr_new_id_d;
    end
  end

  assign instr_valid_id_o = instr_valid_id_q;
  // Signal when a new instruction enters the ID stage (only used for RVFI signalling).
  assign instr_new_id_o   = instr_new_id_q;

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  assign if_id_pipe_reg_we = instr_new_id_d;

  if (ResetAll) begin : g_instr_rdata_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_rdata_id_o         <= '0;
        instr_rdata_alu_id_o     <= '0;
        instr_fetch_err_o        <= '0;
        instr_fetch_err_plus2_o  <= '0;
        instr_rdata_c_id_o       <= '0;
        instr_is_compressed_id_o <= '0;
        illegal_c_insn_id_o      <= '0;
        pc_id_o                  <= '0;
      end else if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= fetch_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end else begin : g_instr_rdata_nr
    always_ff @(posedge clk_i) begin
      if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= fetch_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end

  // Check for expected increments of the PC when security hardening enabled
  if (PCIncrCheck) begin : g_secure_pc
    logic [31:0] prev_instr_addr_incr;
    logic        prev_instr_seq_q, prev_instr_seq_d;

    // Do not check for sequential increase after a branch, jump, exception, interrupt or debug
    // request, all of which will set branch_req. Also do not check after reset or for dummys.
    assign prev_instr_seq_d = (prev_instr_seq_q | instr_new_id_d) &
        ~branch_req & ~stall_dummy_instr;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prev_instr_seq_q <= 1'b0;
      end else begin
        prev_instr_seq_q <= prev_instr_seq_d;
      end
    end

    assign prev_instr_addr_incr = pc_id_o + ((instr_is_compressed_id_o && !instr_fetch_err_o) ?
                                             32'd2 : 32'd4);

    // Check that the address equals the previous address +2/+4
    assign pc_mismatch_alert_o = prev_instr_seq_q & (pc_if_o != prev_instr_addr_incr);

  end else begin : g_no_secure_pc
    assign pc_mismatch_alert_o = 1'b0;
  end

  if (BranchPredictor) begin : g_branch_predictor
    logic [31:0] instr_skid_data_q;
    logic [31:0] instr_skid_addr_q;
    logic        instr_skid_bp_taken_q;
    logic        instr_skid_valid_q, instr_skid_valid_d;
    logic        instr_skid_en;
    logic        instr_bp_taken_q, instr_bp_taken_d;

    logic        predict_branch_taken_raw;

    // ID stages needs to know if branch was predicted taken so it can signal mispredicts
    if (ResetAll) begin : g_bp_taken_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          instr_bp_taken_q <= '0;
        end else if (if_id_pipe_reg_we) begin
          instr_bp_taken_q <= instr_bp_taken_d;
        end
      end
    end else begin : g_bp_taken_nr
      always_ff @(posedge clk_i) begin
        if (if_id_pipe_reg_we) begin
          instr_bp_taken_q <= instr_bp_taken_d;
        end
      end
    end

    // When branch prediction is enabled a skid buffer between the IF and ID/EX stage is introduced.
    // If an instruction in IF is predicted to be a taken branch and ID/EX is not ready the
    // instruction in IF is moved to the skid buffer which becomes the output of the IF stage until
    // the ID/EX stage accepts the instruction. The skid buffer is required as otherwise the ID/EX
    // ready signal is coupled to the instr_req_o output which produces a feedthrough path from
    // data_gnt_i -> instr_req_o (which needs to be avoided as for some interconnects this will
    // result in a combinational loop).

    assign instr_skid_en = predicted_branch & ~id_in_ready_i & ~instr_skid_valid_q;

    assign instr_skid_valid_d = (instr_skid_valid_q & ~id_in_ready_i & ~stall_dummy_instr) |
                                instr_skid_en;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_skid_valid_q <= 1'b0;
      end else begin
        instr_skid_valid_q <= instr_skid_valid_d;
      end
    end

    if (ResetAll) begin : g_instr_skid_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          instr_skid_bp_taken_q <= '0;
          instr_skid_data_q     <= '0;
          instr_skid_addr_q     <= '0;
        end else if (instr_skid_en) begin
          instr_skid_bp_taken_q <= predict_branch_taken;
          instr_skid_data_q     <= fetch_rdata;
          instr_skid_addr_q     <= fetch_addr;
        end
      end
    end else begin : g_instr_skid_nr
      always_ff @(posedge clk_i) begin
        if (instr_skid_en) begin
          instr_skid_bp_taken_q <= predict_branch_taken;
          instr_skid_data_q     <= fetch_rdata;
          instr_skid_addr_q     <= fetch_addr;
        end
      end
    end

    ibex_branch_predict branch_predict_i (
      .clk_i                  ( clk_i                    ),
      .rst_ni                 ( rst_ni                   ),
      .fetch_rdata_i          ( fetch_rdata              ),
      .fetch_pc_i             ( fetch_addr               ),
      .fetch_valid_i          ( fetch_valid              ),

      .predict_branch_taken_o ( predict_branch_taken_raw ),
      .predict_branch_pc_o    ( predict_branch_pc        )
    );

    // If there is an instruction in the skid buffer there must be no branch prediction.
    // Instructions are only placed in the skid after they have been predicted to be a taken branch
    // so with the skid valid any prediction has already occurred.
    // Do not branch predict on instruction errors.
    assign predict_branch_taken = predict_branch_taken_raw & ~instr_skid_valid_q & ~fetch_err;

    // pc_set_i takes precendence over branch prediction
    assign predicted_branch = predict_branch_taken & ~pc_set_i;

    assign if_instr_valid   = fetch_valid | instr_skid_valid_q;
    assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;
    assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;

    // Don't branch predict on instruction error so only instructions without errors end up in the
    // skid buffer.
    assign if_instr_err     = ~instr_skid_valid_q & fetch_err;
    assign instr_bp_taken_d = instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken;

    assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;

    assign instr_bp_taken_o = instr_bp_taken_q;

    `ASSERT(NoPredictSkid, instr_skid_valid_q |-> ~predict_branch_taken)
    `ASSERT(NoPredictIllegal, predict_branch_taken |-> ~illegal_c_insn)
  end else begin : g_no_branch_predictor
    assign instr_bp_taken_o     = 1'b0;
    assign predict_branch_taken = 1'b0;
    assign predicted_branch     = 1'b0;
    assign predict_branch_pc    = 32'b0;

    assign if_instr_valid = fetch_valid;
    assign if_instr_rdata = fetch_rdata;
    assign if_instr_addr  = fetch_addr;
    assign if_instr_err   = fetch_err;
    assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN(IbexExcPcMuxKnown, exc_pc_mux_i)

  if (BranchPredictor) begin : g_branch_predictor_asserts
    `ASSERT_IF(IbexPcMuxValid, pc_mux_internal inside {
        PC_BOOT,
        PC_JUMP,
        PC_EXC,
        PC_ERET,
        PC_DRET,
        PC_BP},
      pc_set_i)

`ifdef INC_ASSERT
    /**
     * Checks for branch prediction interface to fetch_fifo/icache
     *
     * The interface has two signals:
     * - predicted_branch_i: When set with a branch (branch_i) indicates the branch is a predicted
     *   one, it should be ignored when a branch_i isn't set.
     * - branch_mispredict_i: Indicates the previously predicted branch was mis-predicted and
     *   execution should resume with the not-taken side of the branch (i.e. continue with the PC
     *   that followed the predicted branch). This must be raised before the instruction that is
     *   made available following a predicted branch is accepted (Following a cycle with branch_i
     *   & predicted_branch_i, branch_mispredict_i can only be asserted before or on the same cycle
     *   as seeing fetch_valid & fetch_ready). When branch_mispredict_i is asserted, fetch_valid may
     *   be asserted in response. If fetch_valid is asserted on the same cycle as
     *   branch_mispredict_i this indicates the fetch_fifo/icache has the not-taken side of the
     *   branch immediately ready for use
     */
    logic        predicted_branch_live_q, predicted_branch_live_d;
    logic [31:0] predicted_branch_nt_pc_q, predicted_branch_nt_pc_d;
    logic [31:0] awaiting_instr_after_mispredict_q, awaiting_instr_after_mispredict_d;
    logic [31:0] next_pc;

    logic mispredicted, mispredicted_d, mispredicted_q;

    assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);

    always_comb begin
      predicted_branch_live_d = predicted_branch_live_q;
      mispredicted_d          = mispredicted_q;

      if (branch_req & predicted_branch) begin
        predicted_branch_live_d = 1'b1;
        mispredicted_d          = 1'b0;
      end else if (predicted_branch_live_q) begin
        if (fetch_valid & fetch_ready) begin
          predicted_branch_live_d = 1'b0;
        end else if (nt_branch_mispredict_i) begin
          mispredicted_d = 1'b1;
        end
      end
    end

    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        predicted_branch_live_q <= 1'b0;
        mispredicted_q          <= 1'b0;
      end else begin
        predicted_branch_live_q <= predicted_branch_live_d;
        mispredicted_q          <= mispredicted_d;
      end
    end

    always @(posedge clk_i) begin
      if (branch_req & predicted_branch) begin
        predicted_branch_nt_pc_q <= next_pc;
      end
    end

    // Must only see mispredict after we've performed a predicted branch but before we've accepted
    // any instruction (with fetch_ready & fetch_valid) that follows that predicted branch.
    `ASSERT(MispredictOnlyImmediatelyAfterPredictedBranch,
      nt_branch_mispredict_i |-> predicted_branch_live_q)
    // Check that on mispredict we get the correct PC for the non-taken side of the branch when
    // prefetch buffer/icache makes that PC available.
    `ASSERT(CorrectPCOnMispredict,
      predicted_branch_live_q & mispredicted_d & fetch_valid |->
      fetch_addr == predicted_branch_nt_pc_q)
    // Must not signal mispredict over multiple cycles but it's possible to have back to back
    // mispredicts for different branches (core signals mispredict, prefetch buffer/icache immediate
    // has not-taken side of the mispredicted branch ready, which itself is a predicted branch,
    // following cycle core signal that that branch has mispredicted).
    `ASSERT(MispredictSingleCycle,
      nt_branch_mispredict_i & ~(fetch_valid & fetch_ready) |=> ~nt_branch_mispredict_i)
    // Note that we should never see a mispredict and an incoming branch on the same cycle.
    // The mispredict also cancels any predicted branch so overall branch_req must be low.
    `ASSERT(NoMispredBranch, nt_branch_mispredict_i |-> ~branch_req)
`endif

  end else begin : g_no_branch_predictor_asserts
    `ASSERT_IF(IbexPcMuxValid, pc_mux_internal inside {
        PC_BOOT,
        PC_JUMP,
        PC_EXC,
        PC_ERET,
        PC_DRET},
      pc_set_i)
  end

  // Boot address must be aligned to 256 bytes.
  `ASSERT(IbexBootAddrUnaligned, boot_addr_i[7:0] == 8'h00)

  // Address must not contain X when request is sent.
  `ASSERT(IbexInstrAddrUnknown, instr_req_o |-> !$isunknown(instr_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexInstrAddrUnaligned, instr_req_o |-> (instr_addr_o[1:0] == 2'b00))

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Disable it for synthesis and where explicitly requested (by defining
// DV_FCOV_DISABLE).
`ifdef SYNTHESIS
  `define DV_FCOV_DISABLE
`elsif YOSYS
  `define DV_FCOV_DISABLE
`endif

// Disable instantiations of FCOV coverpoints or covergroups.
`ifdef VERILATOR
  `define DV_FCOV_DISABLE_CP
`elsif DV_FCOV_DISABLE
  `define DV_FCOV_DISABLE_CP
`endif

// Instantiates a covergroup in an interface or module.
//
// This macro assumes that a covergroup of the same name as the NAME_ arg is defined in the
// interface or module. It just adds some extra signals and logic to control the creation of the
// covergroup instance with ~bit en_<cg_name>~. This defaults to 0. It is ORed with the external
// COND_ signal. The testbench can modify it at t = 0 based on the test being run.
// NOTE: This is not meant to be invoked inside a class.
//
// NAME_ : Name of the covergroup.
// COND_ : External condition / expr that controls the creation of the covergroup.
// ARGS_ : Arguments to covergroup instance, if any. Args MUST BE wrapped in (..).
`ifndef DV_FCOV_INSTANTIATE_CG
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ())
`else
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ()) \
    bit en_``NAME_ = 1'b0; \
    NAME_ NAME_``_inst; \
    initial begin \
      /* The #1 delay below allows any part of the tb to control the conditions first at t = 0. */ \
      #1; \
      if ((en_``NAME_) || (COND_)) begin \
        $display("%0t: (%0s:%0d) [%m] %0s", $time, `__FILE__, `__LINE__, \
                 {"Creating covergroup ", `"NAME_`"}); \
        NAME_``_inst = new``ARGS_; \
      end \
    end
`endif
`endif

// Creates a coverpoint for an expression where only the expression true case is of interest for
// coverage (e.g. where the expression indicates an event has occured).
`ifndef DV_FCOV_EXPR_SEEN
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_)
`else
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_) cp_``NAME_: coverpoint EXPR_ { bins seen = {1}; }
`endif
`endif

// Creates a SVA cover that can be used in a covergroup.
//
// This macro creates an unnamed SVA cover from the property (or an expression) `PROP_` and an event
// with the name `EV_NAME_`. When the SVA cover is hit, the event is triggered. A coverpoint can
// cover the `triggered` property of the event.
`ifndef DV_FCOV_SVA
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni)
`else
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni) \
    event EV_NAME_; \
    cover property (@(posedge CLK_) disable iff (RST_ == 0) (PROP_)) begin \
      -> EV_NAME_; \
    end
`endif
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef DV_FCOV_MARK_UNUSED
  `define DV_FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef DV_FCOV_SIGNAL
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef DV_FCOV_SIGNAL_GEN_IF
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

module ibex_load_store_unit
(
    input  logic         clk_i,
    input  logic         rst_ni,

    // data interface
    output logic         data_req_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic         data_err_i,
    input  logic         data_pmp_err_i,

    output logic [31:0]  data_addr_o,
    output logic         data_we_o,
    output logic [3:0]   data_be_o,
    output logic [31:0]  data_wdata_o,
    input  logic [31:0]  data_rdata_i,

    // signals to/from ID/EX stage
    input  logic         lsu_we_i,             // write enable                     -> from ID/EX
    input  logic [1:0]   lsu_type_i,           // data type: word, half word, byte -> from ID/EX
    input  logic [31:0]  lsu_wdata_i,          // data to write to memory          -> from ID/EX
    input  logic         lsu_sign_ext_i,       // sign extension                   -> from ID/EX

    output logic [31:0]  lsu_rdata_o,          // requested data                   -> to ID/EX
    output logic         lsu_rdata_valid_o,
    input  logic         lsu_req_i,            // data request                     -> from ID/EX

    input  logic [31:0]  adder_result_ex_i,    // address computed in ALU          -> from ID/EX

    output logic         addr_incr_req_o,      // request address increment for
                                               // misaligned accesses              -> to ID/EX
    output logic [31:0]  addr_last_o,          // address of last transaction      -> to controller
                                               // -> mtval
                                               // -> AGU for misaligned accesses

    output logic         lsu_req_done_o,       // Signals that data request is complete
                                               // (only need to await final data
                                               // response)                        -> to ID/EX

    output logic         lsu_resp_valid_o,     // LSU has response from transaction -> to ID/EX

    // exception signals
    output logic         load_err_o,
    output logic         store_err_o,

    output logic         busy_o,

    output logic         perf_load_o,
    output logic         perf_store_o
);

  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_q, addr_last_d;

  logic         addr_update;
  logic         ctrl_update;
  logic         rdata_update;
  logic [31:8]  rdata_q;
  logic [1:0]   rdata_offset_q;
  logic [1:0]   data_type_q;
  logic         data_sign_ext_q;
  logic         data_we_q;

  logic [1:0]   data_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata;

  logic [31:0]  data_rdata_ext;

  logic [31:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_q, handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_q, pmp_err_d;
  logic         lsu_err_q, lsu_err_d;
  logic         data_or_pmp_err;

  typedef enum logic [2:0]  {
    IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT,
    WAIT_RVALID_MIS_GNTS_DONE
  } ls_fsm_e;

  ls_fsm_e ls_fsm_cs, ls_fsm_ns;

  assign data_addr   = adder_result_ex_i;
  assign data_offset = data_addr[1:0];

  ///////////////////
  // BE generation //
  ///////////////////

  always_comb begin
    unique case (lsu_type_i) // Data type 00 Word, 01 Half word, 11,10 byte
      2'b00: begin // Writing a word
        if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
          unique case (data_offset)
            2'b00:   data_be = 4'b1111;
            2'b01:   data_be = 4'b1110;
            2'b10:   data_be = 4'b1100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end else begin // second part of misaligned transaction
          unique case (data_offset)
            2'b00:   data_be = 4'b0000; // this is not used, but included for completeness
            2'b01:   data_be = 4'b0001;
            2'b10:   data_be = 4'b0011;
            2'b11:   data_be = 4'b0111;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end
      end

      2'b01: begin // Writing a half word
        if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
          unique case (data_offset)
            2'b00:   data_be = 4'b0011;
            2'b01:   data_be = 4'b0110;
            2'b10:   data_be = 4'b1100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end else begin // second part of misaligned transaction
          data_be = 4'b0001;
        end
      end

      2'b10,
      2'b11: begin // Writing a byte
        unique case (data_offset)
          2'b00:   data_be = 4'b0001;
          2'b01:   data_be = 4'b0010;
          2'b10:   data_be = 4'b0100;
          2'b11:   data_be = 4'b1000;
          default: data_be = 4'b1111;
        endcase // case (data_offset)
      end

      default:     data_be = 4'b1111;
    endcase // case (lsu_type_i)
  end

  /////////////////////
  // WData alignment //
  /////////////////////

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses here
  always_comb begin
    unique case (data_offset)
      2'b00:   data_wdata =  lsu_wdata_i[31:0];
      2'b01:   data_wdata = {lsu_wdata_i[23:0], lsu_wdata_i[31:24]};
      2'b10:   data_wdata = {lsu_wdata_i[15:0], lsu_wdata_i[31:16]};
      2'b11:   data_wdata = {lsu_wdata_i[ 7:0], lsu_wdata_i[31: 8]};
      default: data_wdata =  lsu_wdata_i[31:0];
    endcase // case (data_offset)
  end

  /////////////////////
  // RData alignment //
  /////////////////////

  // register for unaligned rdata
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q <= '0;
    end else if (rdata_update) begin
      rdata_q <= data_rdata_i[31:8];
    end
  end

  // registers for transaction control
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_offset_q  <= 2'h0;
      data_type_q     <= 2'h0;
      data_sign_ext_q <= 1'b0;
      data_we_q       <= 1'b0;
    end else if (ctrl_update) begin
      rdata_offset_q  <= data_offset;
      data_type_q     <= lsu_type_i;
      data_sign_ext_q <= lsu_sign_ext_i;
      data_we_q       <= lsu_we_i;
    end
  end

  // Store last address for mtval + AGU for misaligned transactions.  Do not update in case of
  // errors, mtval needs the (first) failing address.  Where an aligned access or the first half of
  // a misaligned access sees an error provide the calculated access address. For the second half of
  // a misaligned access provide the word aligned address of the second half.
  assign addr_last_d = addr_incr_req_o ? data_addr_w_aligned : data_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_last_q <= '0;
    end else if (addr_update) begin
      addr_last_q <= addr_last_d;
    end
  end

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext =  data_rdata_i[31:0];
    endcase
  end

  ////////////////////
  // Sign extension //
  ////////////////////

  // sign extension for half words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
        end
      end

      default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
        end
      end

      default: rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
      default:     data_rdata_ext = rdata_w_ext;
    endcase // case (data_type_q)
  end

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =
      ((lsu_type_i == 2'b00) && (data_offset != 2'b00)) || // misaligned word access
      ((lsu_type_i == 2'b01) && (data_offset == 2'b11));   // misaligned half-word access

  // FSM
  always_comb begin
    ls_fsm_ns       = ls_fsm_cs;

    data_req_o          = 1'b0;
    addr_incr_req_o     = 1'b0;
    handle_misaligned_d = handle_misaligned_q;
    pmp_err_d           = pmp_err_q;
    lsu_err_d           = lsu_err_q;

    addr_update         = 1'b0;
    ctrl_update         = 1'b0;
    rdata_update        = 1'b0;

    perf_load_o         = 1'b0;
    perf_store_o        = 1'b0;

    unique case (ls_fsm_cs)

      IDLE: begin
        pmp_err_d = 1'b0;
        if (lsu_req_i) begin
          data_req_o   = 1'b1;
          pmp_err_d    = data_pmp_err_i;
          lsu_err_d    = 1'b0;
          perf_load_o  = ~lsu_we_i;
          perf_store_o = lsu_we_i;

          if (data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            handle_misaligned_d = split_misaligned_access;
            ls_fsm_ns           = split_misaligned_access ? WAIT_RVALID_MIS : IDLE;
          end else begin
            ls_fsm_ns           = split_misaligned_access ? WAIT_GNT_MIS    : WAIT_GNT;
          end
        end
      end

      WAIT_GNT_MIS: begin
        data_req_o = 1'b1;
        // data_pmp_err_i is valid during the address phase of a request. An error will block the
        // external request and so a data_gnt_i might never be signalled. The registered version
        // pmp_err_q is only updated for new address phases and so can be used in WAIT_GNT* and
        // WAIT_RVALID* states
        if (data_gnt_i || pmp_err_q) begin
          addr_update         = 1'b1;
          ctrl_update         = 1'b1;
          handle_misaligned_d = 1'b1;
          ls_fsm_ns           = WAIT_RVALID_MIS;
        end
      end

      WAIT_RVALID_MIS: begin
        // push out second request
        data_req_o = 1'b1;
        // tell ID/EX stage to update the address
        addr_incr_req_o = 1'b1;

        // first part rvalid is received, or gets a PMP error
        if (data_rvalid_i || pmp_err_q) begin
          // Update the PMP error for the second part
          pmp_err_d = data_pmp_err_i;
          // Record the error status of the first part
          lsu_err_d = data_err_i | pmp_err_q;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // If already granted, wait for second rvalid
          ls_fsm_ns = data_gnt_i ? IDLE : WAIT_GNT;
          // Update the address for the second part, if no error
          addr_update = data_gnt_i & ~(data_err_i | pmp_err_q);
          // clear handle_misaligned if second request is granted
          handle_misaligned_d = ~data_gnt_i;
        end else begin
          // first part rvalid is NOT received
          if (data_gnt_i) begin
            // second grant is received
            ls_fsm_ns = WAIT_RVALID_MIS_GNTS_DONE;
            handle_misaligned_d = 1'b0;
          end
        end
      end

      WAIT_GNT: begin
        // tell ID/EX stage to update the address
        addr_incr_req_o = handle_misaligned_q;
        data_req_o      = 1'b1;
        if (data_gnt_i || pmp_err_q) begin
          ctrl_update         = 1'b1;
          // Update the address, unless there was an error
          addr_update         = ~lsu_err_q;
          ls_fsm_ns           = IDLE;
          handle_misaligned_d = 1'b0;
        end
      end

      WAIT_RVALID_MIS_GNTS_DONE: begin
        // tell ID/EX stage to update the address (to make sure the
        // second address can be captured correctly for mtval and PMP checking)
        addr_incr_req_o = 1'b1;
        // Wait for the first rvalid, second request is already granted
        if (data_rvalid_i) begin
          // Update the pmp error for the second part
          pmp_err_d = data_pmp_err_i;
          // The first part cannot see a PMP error in this state
          lsu_err_d = data_err_i;
          // Now we can update the address for the second part if no error
          addr_update = ~data_err_i;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // Wait for second rvalid
          ls_fsm_ns = IDLE;
        end
      end

      default: begin
        ls_fsm_ns = IDLE;
      end
    endcase
  end

  assign lsu_req_done_o = (lsu_req_i | (ls_fsm_cs != IDLE)) & (ls_fsm_ns == IDLE);

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ls_fsm_cs           <= IDLE;
      handle_misaligned_q <= '0;
      pmp_err_q           <= '0;
      lsu_err_q           <= '0;
    end else begin
      ls_fsm_cs           <= ls_fsm_ns;
      handle_misaligned_q <= handle_misaligned_d;
      pmp_err_q           <= pmp_err_d;
      lsu_err_q           <= lsu_err_d;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign data_or_pmp_err    = lsu_err_q | data_err_i | pmp_err_q;
  assign lsu_resp_valid_o   = (data_rvalid_i | pmp_err_q) & (ls_fsm_cs == IDLE);
  assign lsu_rdata_valid_o  = (ls_fsm_cs == IDLE) & data_rvalid_i & ~data_or_pmp_err & ~data_we_q;

  // output to register file
  assign lsu_rdata_o = data_rdata_ext;

  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  assign data_wdata_o  = data_wdata;
  assign data_we_o     = lsu_we_i;
  assign data_be_o     = data_be;

  // output to ID stage: mtval + AGU for misaligned transactions
  assign addr_last_o   = addr_last_q;

  // Signal a load or store error depending on the transaction type outstanding
  assign load_err_o    = data_or_pmp_err & ~data_we_q & lsu_resp_valid_o;
  assign store_err_o   = data_or_pmp_err &  data_we_q & lsu_resp_valid_o;

  assign busy_o = (ls_fsm_cs != IDLE);

  //////////
  // FCOV //
  //////////

  `DV_FCOV_SIGNAL(logic, ls_error_exception, (load_err_o | store_err_o) & ~pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_pmp_exception, (load_err_o | store_err_o) & pmp_err_q)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexDataTypeKnown, (lsu_req_i | busy_o) |-> !$isunknown(lsu_type_i))
  `ASSERT(IbexDataOffsetKnown, (lsu_req_i | busy_o) |-> !$isunknown(data_offset))
  `ASSERT_KNOWN(IbexRDataOffsetQKnown, rdata_offset_q)
  `ASSERT_KNOWN(IbexDataTypeQKnown, data_type_q)
  `ASSERT(IbexLsuStateValid, ls_fsm_cs inside {
      IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT,
      WAIT_RVALID_MIS_GNTS_DONE})

  // Address must not contain X when request is sent.
  `ASSERT(IbexDataAddrUnknown, data_req_o |-> !$isunknown(data_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexDataAddrUnaligned, data_req_o |-> (data_addr_o[1:0] == 2'b00))

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex lockstep module
// This module instantiates a second copy of the core logic, and compares it's outputs against
// those from the main core. The second core runs synchronously with the main core, delayed by
// LockstepOffset cycles.
module ibex_lockstep import ibex_pkg::*; #(
    parameter int unsigned LockstepOffset    = 2,
    parameter bit          PMPEnable         = 1'b0,
    parameter int unsigned PMPGranularity    = 0,
    parameter int unsigned PMPNumRegions     = 4,
    parameter int unsigned MHPMCounterNum    = 0,
    parameter int unsigned MHPMCounterWidth  = 40,
    parameter bit          RV32E             = 1'b0,
    parameter rv32m_e      RV32M             = RV32MFast,
    parameter rv32b_e      RV32B             = RV32BNone,
    parameter bit          BranchTargetALU   = 1'b0,
    parameter bit          WritebackStage    = 1'b0,
    parameter bit          ICache            = 1'b0,
    parameter bit          ICacheECC         = 1'b0,
    parameter int unsigned BusSizeECC        = BUS_SIZE,
    parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
    parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
    parameter bit          BranchPredictor   = 1'b0,
    parameter bit          DbgTriggerEn      = 1'b0,
    parameter int unsigned DbgHwBreakNum     = 1,
    parameter bit          ResetAll          = 1'b0,
    parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
    parameter bit          SecureIbex        = 1'b0,
    parameter bit          DummyInstructions = 1'b0,
    parameter bit          RegFileECC        = 1'b0,
    parameter int unsigned RegFileDataWidth  = 32,
    parameter int unsigned DmHaltAddr        = 32'h1A110800,
    parameter int unsigned DmExceptionAddr   = 32'h1A110808
) (
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    input  logic                         instr_req_i,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    input  logic [31:0]                  instr_addr_i,
    input  logic [31:0]                  instr_rdata_i,
    input  logic [6:0]                   instr_rdata_intg_i,
    input  logic                         instr_err_i,

    input  logic                         data_req_i,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    input  logic                         data_we_i,
    input  logic [3:0]                   data_be_i,
    input  logic [31:0]                  data_addr_i,
    input  logic [31:0]                  data_wdata_i,
    output logic [6:0]                   data_wdata_intg_o,
    input  logic [31:0]                  data_rdata_i,
    input  logic [6:0]                   data_rdata_intg_i,
    input  logic                         data_err_i,

    input  logic                         dummy_instr_id_i,
    input  logic [4:0]                   rf_raddr_a_i,
    input  logic [4:0]                   rf_raddr_b_i,
    input  logic [4:0]                   rf_waddr_wb_i,
    input  logic                         rf_we_wb_i,
    input  logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_i,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

    input  logic [IC_NUM_WAYS-1:0]       ic_tag_req_i,
    input  logic                         ic_tag_write_i,
    input  logic [IC_INDEX_W-1:0]        ic_tag_addr_i,
    input  logic [TagSizeECC-1:0]        ic_tag_wdata_i,
    input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
    input  logic [IC_NUM_WAYS-1:0]       ic_data_req_i,
    input  logic                         ic_data_write_i,
    input  logic [IC_INDEX_W-1:0]        ic_data_addr_i,
    input  logic [LineSizeECC-1:0]       ic_data_wdata_i,
    input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],

    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,
    input  logic                         irq_pending_i,

    input  logic                         debug_req_i,
    input  crash_dump_t                  crash_dump_i,

    input  logic                         fetch_enable_i,
    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    input  logic                         core_busy_i,
    input  logic                         test_en_i,
    input  logic                         scan_rst_ni
);

  localparam int unsigned LockstepOffsetW = $clog2(LockstepOffset);
  // Core outputs are delayed for an extra cycle due to shadow output registers
  localparam int unsigned OutputsOffset = LockstepOffset + 1;

  //////////////////////
  // Reset generation //
  //////////////////////

  logic [LockstepOffsetW-1:0] rst_shadow_cnt_d, rst_shadow_cnt_q;
  // Internally generated resets cause IMPERFECTSCH warnings
  /* verilator lint_off IMPERFECTSCH */
  logic                       rst_shadow_set_d, rst_shadow_set_q;
  logic                       rst_shadow_n, enable_cmp_q;
  /* verilator lint_on IMPERFECTSCH */

  assign rst_shadow_set_d = (rst_shadow_cnt_q == LockstepOffsetW'(LockstepOffset - 1));
  assign rst_shadow_cnt_d = rst_shadow_set_d ? rst_shadow_cnt_q :
                                               (rst_shadow_cnt_q + LockstepOffsetW'(1));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_shadow_cnt_q <= '0;
      rst_shadow_set_q <= '0;
      enable_cmp_q     <= '0;
    end else begin
      rst_shadow_cnt_q <= rst_shadow_cnt_d;
      rst_shadow_set_q <= rst_shadow_set_d;
      enable_cmp_q     <= rst_shadow_set_q;
    end
  end

  assign rst_shadow_n = test_en_i ? scan_rst_ni : rst_shadow_set_q;

  //////////////////
  // Input delays //
  //////////////////

  typedef struct packed {
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [31:0]                 instr_rdata;
    logic                        instr_err;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [31:0]                 data_rdata;
    logic                        data_err;
    logic [RegFileDataWidth-1:0] rf_rdata_a_ecc;
    logic [RegFileDataWidth-1:0] rf_rdata_b_ecc;
    logic                        irq_software;
    logic                        irq_timer;
    logic                        irq_external;
    logic [14:0]                 irq_fast;
    logic                        irq_nm;
    logic                        debug_req;
    logic                        fetch_enable;
  } delayed_inputs_t;

  delayed_inputs_t [LockstepOffset-1:0] shadow_inputs_q;
  delayed_inputs_t                      shadow_inputs_in;
  logic [6:0]                           instr_rdata_intg_q, data_rdata_intg_q;
  // Packed arrays must be dealt with separately
  logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
  logic [LineSizeECC-1:0]               shadow_data_rdata_q [IC_NUM_WAYS][LockstepOffset];

  // Assign the inputs to the delay structure
  assign shadow_inputs_in.instr_gnt      = instr_gnt_i;
  assign shadow_inputs_in.instr_rvalid   = instr_rvalid_i;
  assign shadow_inputs_in.instr_rdata    = instr_rdata_i;
  assign shadow_inputs_in.instr_err      = instr_err_i;
  assign shadow_inputs_in.data_gnt       = data_gnt_i;
  assign shadow_inputs_in.data_rvalid    = data_rvalid_i;
  assign shadow_inputs_in.data_rdata     = data_rdata_i;
  assign shadow_inputs_in.data_err       = data_err_i;
  assign shadow_inputs_in.rf_rdata_a_ecc = rf_rdata_a_ecc_i;
  assign shadow_inputs_in.rf_rdata_b_ecc = rf_rdata_b_ecc_i;
  assign shadow_inputs_in.irq_software   = irq_software_i;
  assign shadow_inputs_in.irq_timer      = irq_timer_i;
  assign shadow_inputs_in.irq_external   = irq_external_i;
  assign shadow_inputs_in.irq_fast       = irq_fast_i;
  assign shadow_inputs_in.irq_nm         = irq_nm_i;
  assign shadow_inputs_in.debug_req      = debug_req_i;
  assign shadow_inputs_in.fetch_enable   = fetch_enable_i;

  // Delay the inputs
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rdata_intg_q <= '0;
      data_rdata_intg_q  <= '0;
      for (int unsigned i = 0; i < LockstepOffset; i++) begin
        shadow_inputs_q[i]     <= delayed_inputs_t'('0);
        shadow_tag_rdata_q[i]  <= '{default:0};
        shadow_data_rdata_q[i] <= '{default:0};
      end
    end else begin
      instr_rdata_intg_q <= instr_rdata_intg_i;
      data_rdata_intg_q  <= data_rdata_intg_i;
      for (int unsigned i = 0; i < LockstepOffset-1; i++) begin
        shadow_inputs_q[i]     <= shadow_inputs_q[i+1];
        shadow_tag_rdata_q[i]  <= shadow_tag_rdata_q[i+1];
        shadow_data_rdata_q[i] <= shadow_data_rdata_q[i+1];
      end
      shadow_inputs_q[LockstepOffset-1]     <= shadow_inputs_in;
      shadow_tag_rdata_q[LockstepOffset-1]  <= ic_tag_rdata_i;
      shadow_data_rdata_q[LockstepOffset-1] <= ic_data_rdata_i;
    end
  end

  ////////////////////////////
  // Bus integrity checking //
  ////////////////////////////

  logic        bus_intg_err;
  logic [1:0]  instr_intg_err, data_intg_err;
  logic [31:0] unused_wdata;

  // Checks on incoming data
  prim_secded_39_32_dec u_instr_intg_dec (
    .data_i     ({instr_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].instr_rdata}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (instr_intg_err)
  );

  prim_secded_39_32_dec u_data_intg_dec (
    .data_i     ({data_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].data_rdata}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (data_intg_err)
  );

  assign bus_intg_err = (shadow_inputs_q[LockstepOffset-1].instr_rvalid & |instr_intg_err) |
                        (shadow_inputs_q[LockstepOffset-1].data_rvalid  & |data_intg_err);

  // Generate integrity bits
  prim_secded_39_32_enc u_data_gen (
    .data_i (data_wdata_i),
    .data_o ({data_wdata_intg_o, unused_wdata})
  );

  ///////////////////
  // Output delays //
  ///////////////////

  typedef struct packed {
    logic                        instr_req;
    logic [31:0]                 instr_addr;
    logic                        data_req;
    logic                        data_we;
    logic [3:0]                  data_be;
    logic [31:0]                 data_addr;
    logic [31:0]                 data_wdata;
    logic                        dummy_instr_id;
    logic [4:0]                  rf_raddr_a;
    logic [4:0]                  rf_raddr_b;
    logic [4:0]                  rf_waddr_wb;
    logic                        rf_we_wb;
    logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
    logic [IC_NUM_WAYS-1:0]      ic_tag_req;
    logic                        ic_tag_write;
    logic [IC_INDEX_W-1:0]       ic_tag_addr;
    logic [TagSizeECC-1:0]       ic_tag_wdata;
    logic [IC_NUM_WAYS-1:0]      ic_data_req;
    logic                        ic_data_write;
    logic [IC_INDEX_W-1:0]       ic_data_addr;
    logic [LineSizeECC-1:0]      ic_data_wdata;
    logic                        irq_pending;
    crash_dump_t                 crash_dump;
    logic                        core_busy;
  } delayed_outputs_t;

  delayed_outputs_t [OutputsOffset-1:0]  core_outputs_q;
  delayed_outputs_t                      core_outputs_in;
  delayed_outputs_t                      shadow_outputs_d, shadow_outputs_q;

  // Assign core outputs to the structure
  assign core_outputs_in.instr_req       = instr_req_i;
  assign core_outputs_in.instr_addr      = instr_addr_i;
  assign core_outputs_in.data_req        = data_req_i;
  assign core_outputs_in.data_we         = data_we_i;
  assign core_outputs_in.data_be         = data_be_i;
  assign core_outputs_in.data_addr       = data_addr_i;
  assign core_outputs_in.data_wdata      = data_wdata_i;
  assign core_outputs_in.dummy_instr_id  = dummy_instr_id_i;
  assign core_outputs_in.rf_raddr_a      = rf_raddr_a_i;
  assign core_outputs_in.rf_raddr_b      = rf_raddr_b_i;
  assign core_outputs_in.rf_waddr_wb     = rf_waddr_wb_i;
  assign core_outputs_in.rf_we_wb        = rf_we_wb_i;
  assign core_outputs_in.rf_wdata_wb_ecc = rf_wdata_wb_ecc_i;
  assign core_outputs_in.ic_tag_req      = ic_tag_req_i;
  assign core_outputs_in.ic_tag_write    = ic_tag_write_i;
  assign core_outputs_in.ic_tag_addr     = ic_tag_addr_i;
  assign core_outputs_in.ic_tag_wdata    = ic_tag_wdata_i;
  assign core_outputs_in.ic_data_req     = ic_data_req_i;
  assign core_outputs_in.ic_data_write   = ic_data_write_i;
  assign core_outputs_in.ic_data_addr    = ic_data_addr_i;
  assign core_outputs_in.ic_data_wdata   = ic_data_wdata_i;
  assign core_outputs_in.irq_pending     = irq_pending_i;
  assign core_outputs_in.crash_dump      = crash_dump_i;
  assign core_outputs_in.core_busy       = core_busy_i;

  // Delay the outputs
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < OutputsOffset-1; i++) begin
      core_outputs_q[i] <= core_outputs_q[i+1];
    end
    core_outputs_q[OutputsOffset-1] <= core_outputs_in;
  end

  ///////////////////////////////
  // Shadow core instantiation //
  ///////////////////////////////

  logic shadow_alert_minor, shadow_alert_major;

  ibex_core #(
    .PMPEnable         ( PMPEnable         ),
    .PMPGranularity    ( PMPGranularity    ),
    .PMPNumRegions     ( PMPNumRegions     ),
    .MHPMCounterNum    ( MHPMCounterNum    ),
    .MHPMCounterWidth  ( MHPMCounterWidth  ),
    .RV32E             ( RV32E             ),
    .RV32M             ( RV32M             ),
    .RV32B             ( RV32B             ),
    .BranchTargetALU   ( BranchTargetALU   ),
    .ICache            ( ICache            ),
    .ICacheECC         ( ICacheECC         ),
    .BusSizeECC        ( BusSizeECC        ),
    .TagSizeECC        ( TagSizeECC        ),
    .LineSizeECC       ( LineSizeECC       ),
    .BranchPredictor   ( BranchPredictor   ),
    .DbgTriggerEn      ( DbgTriggerEn      ),
    .DbgHwBreakNum     ( DbgHwBreakNum     ),
    .WritebackStage    ( WritebackStage    ),
    .ResetAll          ( ResetAll          ),
    .RndCnstLfsrSeed   ( RndCnstLfsrSeed   ),
    .RndCnstLfsrPerm   ( RndCnstLfsrPerm   ),
    .SecureIbex        ( SecureIbex        ),
    .DummyInstructions ( DummyInstructions ),
    .RegFileECC        ( RegFileECC        ),
    .RegFileDataWidth  ( RegFileDataWidth  ),
    .DmHaltAddr        ( DmHaltAddr        ),
    .DmExceptionAddr   ( DmExceptionAddr   )
  ) u_shadow_core (
    .clk_i             (clk_i),
    .rst_ni            (rst_shadow_n),

    .hart_id_i         (hart_id_i),
    .boot_addr_i       (boot_addr_i),

    .instr_req_o       (shadow_outputs_d.instr_req),
    .instr_gnt_i       (shadow_inputs_q[0].instr_gnt),
    .instr_rvalid_i    (shadow_inputs_q[0].instr_rvalid),
    .instr_addr_o      (shadow_outputs_d.instr_addr),
    .instr_rdata_i     (shadow_inputs_q[0].instr_rdata),
    .instr_err_i       (shadow_inputs_q[0].instr_err),

    .data_req_o        (shadow_outputs_d.data_req),
    .data_gnt_i        (shadow_inputs_q[0].data_gnt),
    .data_rvalid_i     (shadow_inputs_q[0].data_rvalid),
    .data_we_o         (shadow_outputs_d.data_we),
    .data_be_o         (shadow_outputs_d.data_be),
    .data_addr_o       (shadow_outputs_d.data_addr),
    .data_wdata_o      (shadow_outputs_d.data_wdata),
    .data_rdata_i      (shadow_inputs_q[0].data_rdata),
    .data_err_i        (shadow_inputs_q[0].data_err),

    .dummy_instr_id_o  (shadow_outputs_d.dummy_instr_id),
    .rf_raddr_a_o      (shadow_outputs_d.rf_raddr_a),
    .rf_raddr_b_o      (shadow_outputs_d.rf_raddr_b),
    .rf_waddr_wb_o     (shadow_outputs_d.rf_waddr_wb),
    .rf_we_wb_o        (shadow_outputs_d.rf_we_wb),
    .rf_wdata_wb_ecc_o (shadow_outputs_d.rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i  (shadow_inputs_q[0].rf_rdata_a_ecc),
    .rf_rdata_b_ecc_i  (shadow_inputs_q[0].rf_rdata_b_ecc),

    .ic_tag_req_o      (shadow_outputs_d.ic_tag_req),
    .ic_tag_write_o    (shadow_outputs_d.ic_tag_write),
    .ic_tag_addr_o     (shadow_outputs_d.ic_tag_addr),
    .ic_tag_wdata_o    (shadow_outputs_d.ic_tag_wdata),
    .ic_tag_rdata_i    (shadow_tag_rdata_q[0]),
    .ic_data_req_o     (shadow_outputs_d.ic_data_req),
    .ic_data_write_o   (shadow_outputs_d.ic_data_write),
    .ic_data_addr_o    (shadow_outputs_d.ic_data_addr),
    .ic_data_wdata_o   (shadow_outputs_d.ic_data_wdata),
    .ic_data_rdata_i   (shadow_data_rdata_q[0]),

    .irq_software_i    (shadow_inputs_q[0].irq_software),
    .irq_timer_i       (shadow_inputs_q[0].irq_timer),
    .irq_external_i    (shadow_inputs_q[0].irq_external),
    .irq_fast_i        (shadow_inputs_q[0].irq_fast),
    .irq_nm_i          (shadow_inputs_q[0].irq_nm),
    .irq_pending_o     (shadow_outputs_d.irq_pending),

    .debug_req_i       (shadow_inputs_q[0].debug_req),
    .crash_dump_o      (shadow_outputs_d.crash_dump),

`ifdef RVFI
    .rvfi_valid        (),
    .rvfi_order        (),
    .rvfi_insn         (),
    .rvfi_trap         (),
    .rvfi_halt         (),
    .rvfi_intr         (),
    .rvfi_mode         (),
    .rvfi_ixl          (),
    .rvfi_rs1_addr     (),
    .rvfi_rs2_addr     (),
    .rvfi_rs3_addr     (),
    .rvfi_rs1_rdata    (),
    .rvfi_rs2_rdata    (),
    .rvfi_rs3_rdata    (),
    .rvfi_rd_addr      (),
    .rvfi_rd_wdata     (),
    .rvfi_pc_rdata     (),
    .rvfi_pc_wdata     (),
    .rvfi_mem_addr     (),
    .rvfi_mem_rmask    (),
    .rvfi_mem_wmask    (),
    .rvfi_mem_rdata    (),
    .rvfi_mem_wdata    (),
`endif

    .fetch_enable_i    (shadow_inputs_q[0].fetch_enable),
    .alert_minor_o     (shadow_alert_minor),
    .alert_major_o     (shadow_alert_major),
    .core_busy_o       (shadow_outputs_d.core_busy)
  );

  // Register the shadow core outputs
  always_ff @(posedge clk_i) begin
    shadow_outputs_q <= shadow_outputs_d;
  end

  /////////////////////////
  // Compare the outputs //
  /////////////////////////

  logic outputs_mismatch;

  assign outputs_mismatch = enable_cmp_q & (shadow_outputs_q != core_outputs_q[0]);
  assign alert_major_o    = outputs_mismatch | shadow_alert_major | bus_intg_err;
  assign alert_minor_o    = shadow_alert_minor;

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define OP_L 15:0
`define OP_H 31:16

/**
 * Fast Multiplier and Division
 *
 * 16x16 kernel multiplier and Long Division
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_multdiv_fast #(
    parameter ibex_pkg::rv32m_e RV32M = ibex_pkg::RV32MFast
  ) (
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             mult_en_i,  // dynamic enable signal, for FSM control
    input  logic             div_en_i,   // dynamic enable signal, for FSM control
    input  logic             mult_sel_i, // static decoder output, for data muxes
    input  logic             div_sel_i,  // static decoder output, for data muxes
    input  ibex_pkg::md_op_e operator_i,
    input  logic  [1:0]      signed_mode_i,
    input  logic [31:0]      op_a_i,
    input  logic [31:0]      op_b_i,
    input  logic [33:0]      alu_adder_ext_i,
    input  logic [31:0]      alu_adder_i,
    input  logic             equal_to_zero_i,
    input  logic             data_ind_timing_i,

    output logic [32:0]      alu_operand_a_o,
    output logic [32:0]      alu_operand_b_o,

    input  logic [33:0]      imd_val_q_i[2],
    output logic [33:0]      imd_val_d_o[2],
    output logic [1:0]       imd_val_we_o,

    input  logic             multdiv_ready_id_i,

    output logic [31:0]      multdiv_result_o,
    output logic             valid_o
);

  import ibex_pkg::*;

  // Both multiplier variants
  logic signed [34:0] mac_res_signed;
  logic        [34:0] mac_res_ext;
  logic        [33:0] accum;
  logic        sign_a, sign_b;
  logic        mult_valid;
  logic        signed_mult;

  // Results that become intermediate value depending on whether mul or div is being calculated
  logic [33:0] mac_res_d, op_remainder_d;
  // Raw output of MAC calculation
  logic [33:0] mac_res;

  // Divider signals
  logic        div_sign_a, div_sign_b;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q;
  logic [31:0] op_numerator_q;
  logic [31:0] op_quotient_q;
  logic [31:0] op_denominator_d;
  logic [31:0] op_numerator_d;
  logic [31:0] op_quotient_d;
  logic [31:0] next_remainder;
  logic [32:0] next_quotient;
  logic [31:0] res_adder_h;
  logic        div_valid;
  logic [ 4:0] div_counter_q, div_counter_d;
  logic        multdiv_en;
  logic        mult_hold;
  logic        div_hold;
  logic        div_by_zero_d, div_by_zero_q;

  logic        mult_en_internal;
  logic        div_en_internal;

  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_d;

  logic unused_mult_sel_i;
  assign unused_mult_sel_i = mult_sel_i;

  assign mult_en_internal = mult_en_i & ~mult_hold;
  assign div_en_internal  = div_en_i & ~div_hold;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      div_counter_q    <= '0;
      md_state_q       <= MD_IDLE;
      op_numerator_q   <= '0;
      op_quotient_q    <= '0;
      div_by_zero_q    <= '0;
    end else if (div_en_internal) begin
      div_counter_q    <= div_counter_d;
      op_numerator_q   <= op_numerator_d;
      op_quotient_q    <= op_quotient_d;
      md_state_q       <= md_state_d;
      div_by_zero_q    <= div_by_zero_d;
    end
  end

  `ASSERT_KNOWN(DivEnKnown, div_en_internal)
  `ASSERT_KNOWN(MultEnKnown, mult_en_internal)
  `ASSERT_KNOWN(MultDivEnKnown, multdiv_en)

  assign multdiv_en = mult_en_internal | div_en_internal;

  // Intermediate value register shared with ALU
  assign imd_val_d_o[0] = div_sel_i ? op_remainder_d : mac_res_d;
  assign imd_val_we_o[0] = multdiv_en;

  assign imd_val_d_o[1] = {2'b0, op_denominator_d};
  assign imd_val_we_o[1] = div_en_internal;
  assign op_denominator_q = imd_val_q_i[1][31:0];
  logic [1:0] unused_imd_val;
  assign unused_imd_val = imd_val_q_i[1][33:32];
  logic unused_mac_res_ext;
  assign unused_mac_res_ext = mac_res_ext[34];

  assign signed_mult      = (signed_mode_i != 2'b00);
  assign multdiv_result_o = div_sel_i ? imd_val_q_i[0][31:0] : mac_res_d[31:0];

  // The single cycle multiplier uses three 17 bit multipliers to compute MUL instructions in a
  // single cycle and MULH instructions in two cycles.
  if (RV32M == RV32MSingleCycle) begin : gen_mult_single_cycle

    typedef enum logic {
      MULL, MULH
    } mult_fsm_e;
    mult_fsm_e mult_state_q, mult_state_d;

    logic signed [33:0] mult1_res, mult2_res, mult3_res;
    logic [33:0]        mult1_res_uns;
    logic [33:32]       unused_mult1_res_uns;
    logic [15:0]        mult1_op_a, mult1_op_b;
    logic [15:0]        mult2_op_a, mult2_op_b;
    logic [15:0]        mult3_op_a, mult3_op_b;
    logic               mult1_sign_a, mult1_sign_b;
    logic               mult2_sign_a, mult2_sign_b;
    logic               mult3_sign_a, mult3_sign_b;
    logic [33:0]        summand1, summand2, summand3;

    assign mult1_res = $signed({mult1_sign_a, mult1_op_a}) * $signed({mult1_sign_b, mult1_op_b});
    assign mult2_res = $signed({mult2_sign_a, mult2_op_a}) * $signed({mult2_sign_b, mult2_op_b});
    assign mult3_res = $signed({mult3_sign_a, mult3_op_a}) * $signed({mult3_sign_b, mult3_op_b});

    assign mac_res_signed = $signed(summand1) + $signed(summand2) + $signed(summand3);

    assign mult1_res_uns  = $unsigned(mult1_res);
    assign mac_res_ext    = $unsigned(mac_res_signed);
    assign mac_res        = mac_res_ext[33:0];

    assign sign_a = signed_mode_i[0] & op_a_i[31];
    assign sign_b = signed_mode_i[1] & op_b_i[31];

    // The first two multipliers are only used in state 1 (MULL). We can assign them statically.
    // al*bl
    assign mult1_sign_a = 1'b0;
    assign mult1_sign_b = 1'b0;
    assign mult1_op_a = op_a_i[`OP_L];
    assign mult1_op_b = op_b_i[`OP_L];

    // al*bh
    assign mult2_sign_a = 1'b0;
    assign mult2_sign_b = sign_b;
    assign mult2_op_a = op_a_i[`OP_L];
    assign mult2_op_b = op_b_i[`OP_H];

    // used in MULH
    assign accum[17:0] = imd_val_q_i[0][33:16];
    assign accum[33:18] = {16{signed_mult & imd_val_q_i[0][33]}};

    always_comb begin
      // Default values == MULL

      // ah*bl
      mult3_sign_a = sign_a;
      mult3_sign_b = 1'b0;
      mult3_op_a = op_a_i[`OP_H];
      mult3_op_b = op_b_i[`OP_L];

      summand1 = {18'h0, mult1_res_uns[`OP_H]};
      summand2 = $unsigned(mult2_res);
      summand3 = $unsigned(mult3_res);

      // mac_res = A*B[47:16], mult1_res = A*B[15:0]
      mac_res_d = {2'b0, mac_res[`OP_L], mult1_res_uns[`OP_L]};
      mult_valid = mult_en_i;
      mult_state_d = MULL;

      mult_hold = 1'b0;

      unique case (mult_state_q)

        MULL: begin
          if (operator_i != MD_OP_MULL) begin
            mac_res_d = mac_res;
            mult_valid = 1'b0;
            mult_state_d = MULH;
          end else begin
            mult_hold = ~multdiv_ready_id_i;
          end
        end

        MULH: begin
          // ah*bh
          mult3_sign_a = sign_a;
          mult3_sign_b = sign_b;
          mult3_op_a = op_a_i[`OP_H];
          mult3_op_b = op_b_i[`OP_H];
          mac_res_d = mac_res;

          summand1 = '0;
          summand2 = accum;
          summand3 = $unsigned(mult3_res);

          mult_state_d = MULL;
          mult_valid = 1'b1;

          mult_hold = ~multdiv_ready_id_i;
        end

        default: begin
          mult_state_d = MULL;
        end

      endcase // mult_state_q
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mult_state_q <= MULL;
      end else begin
        if (mult_en_internal) begin
          mult_state_q <= mult_state_d;
        end
      end
    end

    assign unused_mult1_res_uns = mult1_res_uns[33:32];

    // States must be knwon/valid.
    `ASSERT_KNOWN(IbexMultStateKnown, mult_state_q)

  // The fast multiplier uses one 17 bit multiplier to compute MUL instructions in 3 cycles
  // and MULH instructions in 4 cycles.
  end else begin : gen_mult_fast
    logic [15:0] mult_op_a;
    logic [15:0] mult_op_b;

    typedef enum logic [1:0] {
      ALBL, ALBH, AHBL, AHBH
    } mult_fsm_e;
    mult_fsm_e mult_state_q, mult_state_d;

    // The 2 MSBs of mac_res_ext (mac_res_ext[34:33]) are always equal since:
    // 1. The 2 MSBs of the multiplicants are always equal, and
    // 2. The 16 MSBs of the addend (accum[33:18]) are always equal.
    // Thus, it is safe to ignore mac_res_ext[34].
    assign mac_res_signed =
        $signed({sign_a, mult_op_a}) * $signed({sign_b, mult_op_b}) + $signed(accum);
    assign mac_res_ext    = $unsigned(mac_res_signed);
    assign mac_res        = mac_res_ext[33:0];

    always_comb begin
      mult_op_a    = op_a_i[`OP_L];
      mult_op_b    = op_b_i[`OP_L];
      sign_a       = 1'b0;
      sign_b       = 1'b0;
      accum        = imd_val_q_i[0];
      mac_res_d    = mac_res;
      mult_state_d = mult_state_q;
      mult_valid   = 1'b0;
      mult_hold    = 1'b0;

      unique case (mult_state_q)

        ALBL: begin
          // al*bl
          mult_op_a = op_a_i[`OP_L];
          mult_op_b = op_b_i[`OP_L];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          accum     = '0;
          mac_res_d = mac_res;
          mult_state_d = ALBH;
        end

        ALBH: begin
          // al*bh<<16
          mult_op_a = op_a_i[`OP_L];
          mult_op_b = op_b_i[`OP_H];
          sign_a    = 1'b0;
          sign_b    = signed_mode_i[1] & op_b_i[31];
          // result of AL*BL (in imd_val_q_i[0]) always unsigned with no carry
          accum     = {18'b0, imd_val_q_i[0][31:16]};
          if (operator_i == MD_OP_MULL) begin
            mac_res_d = {2'b0, mac_res[`OP_L], imd_val_q_i[0][`OP_L]};
          end else begin
            // MD_OP_MULH
            mac_res_d = mac_res;
          end
          mult_state_d = AHBL;
        end

        AHBL: begin
          // ah*bl<<16
          mult_op_a = op_a_i[`OP_H];
          mult_op_b = op_b_i[`OP_L];
          sign_a    = signed_mode_i[0] & op_a_i[31];
          sign_b    = 1'b0;
          if (operator_i == MD_OP_MULL) begin
            accum        = {18'b0, imd_val_q_i[0][31:16]};
            mac_res_d    = {2'b0, mac_res[15:0], imd_val_q_i[0][15:0]};
            mult_valid   = 1'b1;

            // Note no state transition will occur if mult_hold is set
            mult_state_d = ALBL;
            mult_hold    = ~multdiv_ready_id_i;
          end else begin
            accum        = imd_val_q_i[0];
            mac_res_d    = mac_res;
            mult_state_d = AHBH;
          end
        end

        AHBH: begin
          // only MD_OP_MULH here
          // ah*bh
          mult_op_a = op_a_i[`OP_H];
          mult_op_b = op_b_i[`OP_H];
          sign_a    = signed_mode_i[0] & op_a_i[31];
          sign_b    = signed_mode_i[1] & op_b_i[31];
          accum[17: 0]  = imd_val_q_i[0][33:16];
          accum[33:18]  = {16{signed_mult & imd_val_q_i[0][33]}};
          // result of AH*BL is not signed only if signed_mode_i == 2'b00
          mac_res_d    = mac_res;
          mult_valid   = 1'b1;

          // Note no state transition will occur if mult_hold is set
          mult_state_d = ALBL;
          mult_hold    = ~multdiv_ready_id_i;
        end
        default: begin
          mult_state_d = ALBL;
        end
      endcase // mult_state_q
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mult_state_q <= ALBL;
      end else begin
        if (mult_en_internal) begin
          mult_state_q <= mult_state_d;
        end
      end
    end

    // States must be knwon/valid.
    `ASSERT_KNOWN(IbexMultStateKnown, mult_state_q)

  end // gen_mult_fast

  // Divider
  assign res_adder_h    = alu_adder_ext_i[32:1];
  logic [1:0] unused_alu_adder_ext;
  assign unused_alu_adder_ext = {alu_adder_ext_i[33],alu_adder_ext_i[0]};

  assign next_remainder = is_greater_equal ? res_adder_h[31:0] : imd_val_q_i[0][31:0];
  assign next_quotient  = is_greater_equal ? {1'b0, op_quotient_q} | {1'b0, one_shift} :
                                             {1'b0, op_quotient_q};

  assign one_shift      = {31'b0, 1'b1} << div_counter_q;

  // The adder in the ALU computes alu_operand_a_o + alu_operand_b_o which means
  // Remainder - Divisor. If Remainder - Divisor >= 0, is_greater_equal is equal to 1,
  // the next Remainder is Remainder - Divisor contained in res_adder_h and the
  always_comb begin
    if ((imd_val_q_i[0][31] ^ op_denominator_q[31]) == 1'b0) begin
      is_greater_equal = (res_adder_h[31] == 1'b0);
    end else begin
      is_greater_equal = imd_val_q_i[0][31];
    end
  end

  assign div_sign_a      = op_a_i[31] & signed_mode_i[0];
  assign div_sign_b      = op_b_i[31] & signed_mode_i[1];
  assign div_change_sign = (div_sign_a ^ div_sign_b) & ~div_by_zero_q;
  assign rem_change_sign = div_sign_a;


  always_comb begin
    div_counter_d    = div_counter_q - 5'h1;
    op_remainder_d   = imd_val_q_i[0];
    op_quotient_d    = op_quotient_q;
    md_state_d       = md_state_q;
    op_numerator_d   = op_numerator_q;
    op_denominator_d = op_denominator_q;
    alu_operand_a_o  = {32'h0  , 1'b1};
    alu_operand_b_o  = {~op_b_i, 1'b1};
    div_valid        = 1'b0;
    div_hold         = 1'b0;
    div_by_zero_d    = div_by_zero_q;

    unique case(md_state_q)
      MD_IDLE: begin
        if (operator_i == MD_OP_DIV) begin
          // Check if the Denominator is 0
          // quotient for division by 0 is specified to be -1
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return -1
          op_remainder_d = '1;
          md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
          // Record that this is a div by zero to stop the sign change at the end of the
          // division (in data_ind_timing mode).
          div_by_zero_d  = equal_to_zero_i;
        end else begin
          // Check if the Denominator is 0
          // remainder for division by 0 is specified to be the numerator (operand a)
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return operand a
          op_remainder_d = {2'b0, op_a_i};
          md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
        end
        // 0 - B = 0 iff B == 0
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~op_b_i, 1'b1};
        div_counter_d    = 5'd31;
      end

      MD_ABS_A: begin
        // quotient
        op_quotient_d   = '0;
        // A abs value
        op_numerator_d  = div_sign_a ? alu_adder_i : op_a_i;
        md_state_d      = MD_ABS_B;
        div_counter_d   = 5'd31;
        // ABS(A) = 0 - A
        alu_operand_a_o = {32'h0  , 1'b1};
        alu_operand_b_o = {~op_a_i, 1'b1};
      end

      MD_ABS_B: begin
        // remainder
        op_remainder_d   = { 33'h0, op_numerator_q[31]};
        // B abs value
        op_denominator_d = div_sign_b ? alu_adder_i : op_b_i;
        md_state_d       = MD_COMP;
        div_counter_d    = 5'd31;
        // ABS(B) = 0 - B
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~op_b_i, 1'b1};
      end

      MD_COMP: begin
        op_remainder_d  = {1'b0, next_remainder[31:0], op_numerator_q[div_counter_d]};
        op_quotient_d   = next_quotient[31:0];
        md_state_d      = (div_counter_q == 5'd1) ? MD_LAST : MD_COMP;
        // Division
        alu_operand_a_o = {imd_val_q_i[0][31:0], 1'b1}; // it contains the remainder
        alu_operand_b_o = {~op_denominator_q[31:0], 1'b1};  // -denominator two's compliment
      end

      MD_LAST: begin
        if (operator_i == MD_OP_DIV) begin
          // this time we save the quotient in op_remainder_d (i.e. imd_val_q_i[0]) since
          // we do not need anymore the remainder
          op_remainder_d = {1'b0, next_quotient};
        end else begin
          // this time we do not save the quotient anymore since we need only the remainder
          op_remainder_d = {2'b0, next_remainder[31:0]};
        end
        // Division
        alu_operand_a_o  = {imd_val_q_i[0][31:0], 1'b1}; // it contains the remainder
        alu_operand_b_o  = {~op_denominator_q[31:0], 1'b1};  // -denominator two's compliment

        md_state_d = MD_CHANGE_SIGN;
      end

      MD_CHANGE_SIGN: begin
        md_state_d  = MD_FINISH;
        if (operator_i == MD_OP_DIV) begin
          op_remainder_d = (div_change_sign) ? {2'h0, alu_adder_i} : imd_val_q_i[0];
        end else begin
          op_remainder_d = (rem_change_sign) ? {2'h0, alu_adder_i} : imd_val_q_i[0];
        end
        // ABS(Quotient) = 0 - Quotient (or Remainder)
        alu_operand_a_o  = {32'h0  , 1'b1};
        alu_operand_b_o  = {~imd_val_q_i[0][31:0], 1'b1};
      end

      MD_FINISH: begin
        // Hold result until ID stage is ready to accept it
        // Note no state transition will occur if div_hold is set
        md_state_d = MD_IDLE;
        div_hold   = ~multdiv_ready_id_i;
        div_valid   = 1'b1;
      end

      default: begin
        md_state_d = MD_IDLE;
      end
    endcase // md_state_q
  end

  assign valid_o = mult_valid | div_valid;

  // States must be knwon/valid.
  `ASSERT(IbexMultDivStateValid, md_state_q inside {
      MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH})

`ifdef FORMAL
  `ifdef YOSYS
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

formal_tb tb_i (.*);
  `endif
`endif

endmodule // ibex_mult
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Slow Multiplier and Division
 *
 * Baugh-Wooley multiplier and Long Division
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

module ibex_multdiv_slow
(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             mult_en_i,  // dynamic enable signal, for FSM control
    input  logic             div_en_i,   // dynamic enable signal, for FSM control
    input  logic             mult_sel_i, // static decoder output, for data muxes
    input  logic             div_sel_i,  // static decoder output, for data muxes
    input  ibex_pkg::md_op_e operator_i,
    input  logic  [1:0]      signed_mode_i,
    input  logic [31:0]      op_a_i,
    input  logic [31:0]      op_b_i,
    input  logic [33:0]      alu_adder_ext_i,
    input  logic [31:0]      alu_adder_i,
    input  logic             equal_to_zero_i,
    input  logic             data_ind_timing_i,

    output logic [32:0]      alu_operand_a_o,
    output logic [32:0]      alu_operand_b_o,

    input  logic [33:0]      imd_val_q_i[2],
    output logic [33:0]      imd_val_d_o[2],
    output logic  [1:0]      imd_val_we_o,

    input  logic             multdiv_ready_id_i,

    output logic [31:0]      multdiv_result_o,

    output logic             valid_o
);

  import ibex_pkg::*;

  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_d;

  logic [32:0] accum_window_q, accum_window_d;
  logic        unused_imd_val0;
  logic [ 1:0] unused_imd_val1;

  logic [32:0] res_adder_l;
  logic [32:0] res_adder_h;

  logic [ 4:0] multdiv_count_q, multdiv_count_d;
  logic [32:0] op_b_shift_q, op_b_shift_d;
  logic [32:0] op_a_shift_q, op_a_shift_d;
  logic [32:0] op_a_ext, op_b_ext;
  logic [32:0] one_shift;
  logic [32:0] op_a_bw_pp, op_a_bw_last_pp;
  logic [31:0] b_0;
  logic        sign_a, sign_b;
  logic [32:0] next_quotient;
  logic [31:0] next_remainder;
  logic [31:0] op_numerator_q, op_numerator_d;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic        div_by_zero_d, div_by_zero_q;
  logic        multdiv_hold;
  logic        multdiv_en;

   // (accum_window_q + op_a_shift_q)
  assign res_adder_l = alu_adder_ext_i[32:0];
   // (accum_window_q + op_a_shift_q)>>1
  assign res_adder_h = alu_adder_ext_i[33:1];

  /////////////////////
  // ALU Operand MUX //
  /////////////////////

  // Intermediate value register shared with ALU
  assign imd_val_d_o[0]  = {1'b0,accum_window_d};
  assign imd_val_we_o[0] = ~multdiv_hold;
  assign accum_window_q  = imd_val_q_i[0][32:0];
  assign unused_imd_val0 = imd_val_q_i[0][33];

  assign imd_val_d_o[1]  = {2'b00, op_numerator_d};
  assign imd_val_we_o[1] = multdiv_en;
  assign op_numerator_q  = imd_val_q_i[1][31:0];
  assign unused_imd_val1 = imd_val_q_i[1][33:32];

  always_comb begin
    alu_operand_a_o = accum_window_q;

    unique case(operator_i)

      MD_OP_MULL: begin
        alu_operand_b_o = op_a_bw_pp;
      end

      MD_OP_MULH: begin
        alu_operand_b_o = (md_state_q == MD_LAST) ? op_a_bw_last_pp : op_a_bw_pp;
      end

      MD_OP_DIV,
      MD_OP_REM: begin
        unique case(md_state_q)
          MD_IDLE: begin
            // 0 - B = 0 iff B == 0
            alu_operand_a_o = {32'h0  , 1'b1};
            alu_operand_b_o = {~op_b_i, 1'b1};
          end
          MD_ABS_A: begin
            // ABS(A) = 0 - A
            alu_operand_a_o = {32'h0  , 1'b1};
            alu_operand_b_o = {~op_a_i, 1'b1};
          end
          MD_ABS_B: begin
            // ABS(B) = 0 - B
            alu_operand_a_o = {32'h0  , 1'b1};
            alu_operand_b_o = {~op_b_i, 1'b1};
          end
          MD_CHANGE_SIGN: begin
            // ABS(Quotient) = 0 - Quotient (or Reminder)
            alu_operand_a_o = {32'h0  , 1'b1};
            alu_operand_b_o = {~accum_window_q[31:0], 1'b1};
          end
          default: begin
            // Division
            alu_operand_a_o = {accum_window_q[31:0], 1'b1}; // it contains the remainder
            alu_operand_b_o = {~op_b_shift_q[31:0], 1'b1};  // -denominator two's compliment
          end
        endcase
      end
      default: begin
        alu_operand_a_o = accum_window_q;
        alu_operand_b_o = {~op_b_shift_q[31:0], 1'b1};
      end
    endcase
  end

  // Multiplier partial product calculation
  assign b_0             = {32{op_b_shift_q[0]}};
  assign op_a_bw_pp      = { ~(op_a_shift_q[32] & op_b_shift_q[0]),  (op_a_shift_q[31:0] & b_0) };
  assign op_a_bw_last_pp = {  (op_a_shift_q[32] & op_b_shift_q[0]), ~(op_a_shift_q[31:0] & b_0) };

  // Sign extend the input operands
  assign sign_a   = op_a_i[31] & signed_mode_i[0];
  assign sign_b   = op_b_i[31] & signed_mode_i[1];

  assign op_a_ext = {sign_a, op_a_i};
  assign op_b_ext = {sign_b, op_b_i};

  // Divider calculations

  // The adder in the ALU computes Remainder - Divisor. If Remainder - Divisor >= 0,
  // is_greater_equal is true, the next Remainder is the subtraction result and the Quotient
  // multdiv_count_q-th bit is set to 1.
  assign is_greater_equal = (accum_window_q[31] == op_b_shift_q[31]) ?
      ~res_adder_h[31] : accum_window_q[31];

  assign one_shift      = {32'b0, 1'b1} << multdiv_count_q;

  assign next_remainder = is_greater_equal ? res_adder_h[31:0]        : accum_window_q[31:0];
  assign next_quotient  = is_greater_equal ? op_a_shift_q | one_shift : op_a_shift_q;

  assign div_change_sign  = (sign_a ^ sign_b) & ~div_by_zero_q;
  assign rem_change_sign  = sign_a;

  always_comb begin
    multdiv_count_d  = multdiv_count_q;
    accum_window_d   = accum_window_q;
    op_b_shift_d     = op_b_shift_q;
    op_a_shift_d     = op_a_shift_q;
    op_numerator_d   = op_numerator_q;
    md_state_d       = md_state_q;
    multdiv_hold     = 1'b0;
    div_by_zero_d    = div_by_zero_q;
    if (mult_sel_i || div_sel_i) begin
      unique case(md_state_q)
        MD_IDLE: begin
          unique case(operator_i)
            MD_OP_MULL: begin
              op_a_shift_d   = op_a_ext << 1;
              accum_window_d = {       ~(op_a_ext[32]   &     op_b_i[0]),
                                         op_a_ext[31:0] & {32{op_b_i[0]}}  };
              op_b_shift_d   = op_b_ext >> 1;
              // Proceed with multiplication by 0/1 in data-independent time mode
              md_state_d     = (!data_ind_timing_i && ((op_b_ext >> 1) == 0)) ? MD_LAST : MD_COMP;
            end
            MD_OP_MULH: begin
              op_a_shift_d   = op_a_ext;
              accum_window_d = { 1'b1, ~(op_a_ext[32]   &     op_b_i[0]),
                                         op_a_ext[31:1] & {31{op_b_i[0]}}  };
              op_b_shift_d   = op_b_ext >> 1;
              md_state_d     = MD_COMP;
            end
            MD_OP_DIV: begin
              // Check if the denominator is 0
              // quotient for division by 0 is specified to be -1
              // Note with data-independent time option, the full divide operation will proceed as
              // normal and will naturally return -1
              accum_window_d = {33{1'b1}};
              md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
              // Record that this is a div by zero to stop the sign change at the end of the
              // division (in data_ind_timing mode).
              div_by_zero_d  = equal_to_zero_i;
            end
            MD_OP_REM: begin
              // Check if the denominator is 0
              // remainder for division by 0 is specified to be the numerator (operand a)
              // Note with data-independent time option, the full divide operation will proceed as
              // normal and will naturally return operand a
              accum_window_d = op_a_ext;
              md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
            end
            default:;
          endcase
          multdiv_count_d   = 5'd31;
        end

        MD_ABS_A: begin
          // quotient
          op_a_shift_d   = '0;
          // A abs value
          op_numerator_d = sign_a ? alu_adder_i : op_a_i;
          md_state_d     = MD_ABS_B;
        end

        MD_ABS_B: begin
          // remainder
          accum_window_d = {32'h0,op_numerator_q[31]};
          // B abs value
          op_b_shift_d   = sign_b ? {1'b0,alu_adder_i} : {1'b0,op_b_i};
          md_state_d     = MD_COMP;
        end

        MD_COMP: begin
          multdiv_count_d = multdiv_count_q - 5'h1;
          unique case(operator_i)
            MD_OP_MULL: begin
              accum_window_d = res_adder_l;
              op_a_shift_d   = op_a_shift_q << 1;
              op_b_shift_d   = op_b_shift_q >> 1;
              // Multiplication is complete once op_b is zero, unless in data_ind_timing mode where
              // the maximum possible shift-add operations will be completed regardless of op_b
              md_state_d     = ((!data_ind_timing_i && (op_b_shift_d == 0)) ||
                                (multdiv_count_q == 5'd1)) ? MD_LAST : MD_COMP;
            end
            MD_OP_MULH: begin
              accum_window_d = res_adder_h;
              op_a_shift_d   = op_a_shift_q;
              op_b_shift_d   = op_b_shift_q >> 1;
              md_state_d     = (multdiv_count_q == 5'd1) ? MD_LAST : MD_COMP;
            end
            MD_OP_DIV,
            MD_OP_REM: begin
              accum_window_d = {next_remainder[31:0], op_numerator_q[multdiv_count_d]};
              op_a_shift_d   = next_quotient;
              md_state_d     = (multdiv_count_q == 5'd1) ? MD_LAST : MD_COMP;
            end
            default: ;
          endcase
        end

        MD_LAST: begin
          unique case(operator_i)
            MD_OP_MULL: begin
              accum_window_d = res_adder_l;

              // Note no state transition will occur if multdiv_hold is set
              md_state_d   = MD_IDLE;
              multdiv_hold = ~multdiv_ready_id_i;
            end
            MD_OP_MULH: begin
              accum_window_d = res_adder_l;
              md_state_d     = MD_IDLE;

              // Note no state transition will occur if multdiv_hold is set
              md_state_d   = MD_IDLE;
              multdiv_hold = ~multdiv_ready_id_i;
            end
            MD_OP_DIV: begin
              // this time we save the quotient in accum_window_q since we do not need anymore the
              // remainder
              accum_window_d = next_quotient;
              md_state_d     = MD_CHANGE_SIGN;
            end
            MD_OP_REM: begin
              // this time we do not save the quotient anymore since we need only the remainder
              accum_window_d = {1'b0, next_remainder[31:0]};
              md_state_d     = MD_CHANGE_SIGN;
            end
            default: ;
          endcase
        end

        MD_CHANGE_SIGN: begin
          md_state_d = MD_FINISH;
          unique case(operator_i)
            MD_OP_DIV:
              accum_window_d = div_change_sign ? {1'b0,alu_adder_i} : accum_window_q;
            MD_OP_REM:
              accum_window_d = rem_change_sign ? {1'b0,alu_adder_i} : accum_window_q;
            default: ;
          endcase
        end

        MD_FINISH: begin
          // Note no state transition will occur if multdiv_hold is set
          md_state_d   = MD_IDLE;
          multdiv_hold = ~multdiv_ready_id_i;
        end

        default: begin
          md_state_d = MD_IDLE;
        end
      endcase // md_state_q
    end // (mult_sel_i || div_sel_i)
  end

  //////////////////////////////////////////
  // Mutliplier / Divider state registers //
  //////////////////////////////////////////

  assign multdiv_en = (mult_en_i | div_en_i) & ~multdiv_hold;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      multdiv_count_q  <= 5'h0;
      op_b_shift_q     <= 33'h0;
      op_a_shift_q     <= 33'h0;
      md_state_q       <= MD_IDLE;
      div_by_zero_q    <= 1'b0;
    end else if (multdiv_en) begin
      multdiv_count_q  <= multdiv_count_d;
      op_b_shift_q     <= op_b_shift_d;
      op_a_shift_q     <= op_a_shift_d;
      md_state_q       <= md_state_d;
      div_by_zero_q    <= div_by_zero_d;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign valid_o = (md_state_q == MD_FINISH) |
                   (md_state_q == MD_LAST &
                   (operator_i == MD_OP_MULL |
                    operator_i == MD_OP_MULH));

  assign multdiv_result_o = div_en_i ? accum_window_q[31:0] : res_adder_l[31:0];

  ////////////////
  // Assertions //
  ////////////////

  // State must be valid.
  `ASSERT(IbexMultDivStateValid, md_state_q inside {
      MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
      }, clk_i, !rst_ni)

`ifdef FORMAL
  `ifdef YOSYS
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

formal_tb tb_i (.*);
  `endif
`endif

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_pmp #(
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMPGranularity = 0,
    // Number of access channels (e.g. i-side + d-side)
    parameter int unsigned PMPNumChan     = 2,
    // Number of implemented regions
    parameter int unsigned PMPNumRegions  = 4
) (
    // Clock and Reset
    input  logic                    clk_i,
    input  logic                    rst_ni,

    // Interface to CSRs
    input  ibex_pkg::pmp_cfg_t      csr_pmp_cfg_i     [PMPNumRegions],
    input  logic [33:0]             csr_pmp_addr_i    [PMPNumRegions],
    input  ibex_pkg::pmp_mseccfg_t  csr_pmp_mseccfg_i,

    input  ibex_pkg::priv_lvl_e     priv_mode_i    [PMPNumChan],
    // Access checking channels
    input  logic [33:0]             pmp_req_addr_i [PMPNumChan],
    input  ibex_pkg::pmp_req_e      pmp_req_type_i [PMPNumChan],
    output logic                    pmp_req_err_o  [PMPNumChan]

);

  import ibex_pkg::*;

  // Access Checking Signals
  logic [33:0]                                region_start_addr [PMPNumRegions];
  logic [33:PMPGranularity+2]                 region_addr_mask  [PMPNumRegions];
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_gt;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_lt;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_eq;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_all;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_basic_perm_check;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_mml_perm_check;
  logic [PMPNumChan-1:0]                      access_fault;


  // ---------------
  // Access checking
  // ---------------

  for (genvar r = 0; r < PMPNumRegions; r++) begin : g_addr_exp
    // Start address for TOR matching
    if (r == 0) begin : g_entry0
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? 34'h000000000 :
                                                                              csr_pmp_addr_i[r];
    end else begin : g_oth
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? csr_pmp_addr_i[r-1] :
                                                                              csr_pmp_addr_i[r];
    end
    // Address mask for NA matching
    for (genvar b = PMPGranularity+2; b < 34; b++) begin : g_bitmask
      if (b == 2) begin : g_bit0
        // Always mask bit 2 for NAPOT
        assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT);
      end else begin : g_others
        // We will mask this bit if it is within the programmed granule
        // i.e. addr = yyyy 0111
        //                  ^
        //                  | This bit pos is the top of the mask, all lower bits set
        // thus mask = 1111 0000
        if (PMPGranularity == 0) begin : g_region_addr_mask_zero_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:2];
        end else begin : g_region_addr_mask_other_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:PMPGranularity+1];
        end
      end
    end
  end

  for (genvar c = 0; c < PMPNumChan; c++) begin : g_access_check
    for (genvar r = 0; r < PMPNumRegions; r++) begin : g_regions
      // Comparators are sized according to granularity
      assign region_match_eq[c][r] = (pmp_req_addr_i[c][33:PMPGranularity+2] &
                                      region_addr_mask[r]) ==
                                     (region_start_addr[r][33:PMPGranularity+2] &
                                      region_addr_mask[r]);
      assign region_match_gt[c][r] = pmp_req_addr_i[c][33:PMPGranularity+2] >
                                     region_start_addr[r][33:PMPGranularity+2];
      assign region_match_lt[c][r] = pmp_req_addr_i[c][33:PMPGranularity+2] <
                                     csr_pmp_addr_i[r][33:PMPGranularity+2];

      always_comb begin
        region_match_all[c][r] = 1'b0;
        unique case (csr_pmp_cfg_i[r].mode)
          PMP_MODE_OFF   : region_match_all[c][r] = 1'b0;
          PMP_MODE_NA4   : region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_NAPOT : region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_TOR   : begin
            region_match_all[c][r] = (region_match_eq[c][r] | region_match_gt[c][r]) &
                                     region_match_lt[c][r];
          end
          default        : region_match_all[c][r] = 1'b0;
        endcase
      end

      // Check specific required permissions
      assign region_basic_perm_check[c][r] =
          ((pmp_req_type_i[c] == PMP_ACC_EXEC)  & csr_pmp_cfg_i[r].exec) |
          ((pmp_req_type_i[c] == PMP_ACC_WRITE) & csr_pmp_cfg_i[r].write) |
          ((pmp_req_type_i[c] == PMP_ACC_READ)  & csr_pmp_cfg_i[r].read);


      // Compute permission checks that apply when MSECCFG.MML is set.
      always_comb begin
        region_mml_perm_check[c][r] = 1'b0;

        if (!csr_pmp_cfg_i[r].read && csr_pmp_cfg_i[r].write) begin
          // Special-case shared regions where R = 0, W = 1
          unique case ({csr_pmp_cfg_i[r].lock, csr_pmp_cfg_i[r].exec})
            // Read/write in M, read only in S/U
            2'b00: region_mml_perm_check[c][r] =
                (pmp_req_type_i[c] == PMP_ACC_READ) |
                ((pmp_req_type_i[c] == PMP_ACC_WRITE) & (priv_mode_i[c] == PRIV_LVL_M));
            // Read/write in M/S/U
            2'b01: region_mml_perm_check[c][r] =
                (pmp_req_type_i[c] == PMP_ACC_READ) | (pmp_req_type_i[c] == PMP_ACC_WRITE);
            // Execute only on M/S/U
            2'b10: region_mml_perm_check[c][r] = (pmp_req_type_i[c] == PMP_ACC_EXEC);
            // Read/execute in M, execute only on S/U
            2'b11: region_mml_perm_check[c][r] =
                (pmp_req_type_i[c] == PMP_ACC_EXEC) |
                ((pmp_req_type_i[c] == PMP_ACC_READ) & (priv_mode_i[c] == PRIV_LVL_M));
            default: ;
          endcase
        end else begin
          if (csr_pmp_cfg_i[r].read & csr_pmp_cfg_i[r].write & csr_pmp_cfg_i[r].exec
              & csr_pmp_cfg_i[r].lock) begin
            // Special-case shared read only region when R = 1, W = 1, X = 1, L = 1
            region_mml_perm_check[c][r] = pmp_req_type_i[c] == PMP_ACC_READ;
          end else begin
            // Otherwise use basic permission check. Permission is always denied if in S/U mode and
            // L is set or if in M mode and L is unset.
            region_mml_perm_check[c][r] =
              priv_mode_i[c] == PRIV_LVL_M ? csr_pmp_cfg_i[r].lock & region_basic_perm_check[c][r] :
                                            ~csr_pmp_cfg_i[r].lock & region_basic_perm_check[c][r];
          end
        end
      end
    end

    // Access fault determination / prioritization
    always_comb begin
      // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
      // modes
      access_fault[c] = csr_pmp_mseccfg_i.mmwp | (priv_mode_i[c] != PRIV_LVL_M);

      // PMP entries are statically prioritized, from 0 to N-1
      // The lowest-numbered PMP entry which matches an address determines accessability
      for (int r = PMPNumRegions-1; r >= 0; r--) begin
        if (region_match_all[c][r]) begin
          if (csr_pmp_mseccfg_i.mml) begin
            // When MSECCFG.MML is set use MML specific permission check
            access_fault[c] = ~region_mml_perm_check[c][r];
          end else begin
            // Otherwise use original PMP behaviour
            access_fault[c] = (priv_mode_i[c] == PRIV_LVL_M) ?
                // For M-mode, any region which matches with the L-bit clear, or with sufficient
                // access permissions will be allowed
                (csr_pmp_cfg_i[r].lock & ~region_basic_perm_check[c][r]) :
                // For other modes, the lock bit doesn't matter
                ~region_basic_perm_check[c][r];
          end
        end
      end
    end

    assign pmp_req_err_o[c] = access_fault[c];
  end

  // RLB, rule locking bypass, is only relevant to ibex_cs_registers which controls writes to the
  // PMP CSRs. Tie to unused signal here to prevent lint warnings.
  logic unused_csr_pmp_mseccfg_rlb;
  assign unused_csr_pmp_mseccfg_rlb = csr_pmp_mseccfg_i.rlb;
endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Prefetcher Buffer for 32 bit memory interface
 *
 * Prefetch Buffer that caches instructions. This cuts overly long critical
 * paths to the instruction cache.
 */
module ibex_prefetch_buffer #(
  parameter bit BranchPredictor = 1'b0,
  parameter bit ResetAll        = 1'b0
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        req_i,

    input  logic        branch_i,
    input  logic        branch_spec_i,
    input  logic        predicted_branch_i,
    input  logic        branch_mispredict_i,
    input  logic [31:0] addr_i,


    input  logic        ready_i,
    output logic        valid_o,
    output logic [31:0] rdata_o,
    output logic [31:0] addr_o,
    output logic        err_o,
    output logic        err_plus2_o,


    // goes to instruction memory / instruction cache
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,
    input  logic        instr_err_i,
    input  logic        instr_pmp_err_i,
    input  logic        instr_rvalid_i,

    // Prefetch Buffer Status
    output logic        busy_o
);

  localparam int unsigned NUM_REQS  = 2;

  logic                branch_suppress;
  logic                valid_new_req, valid_req;
  logic                valid_req_d, valid_req_q;
  logic                discard_req_d, discard_req_q;
  logic                gnt_or_pmp_err, rvalid_or_pmp_err;
  logic [NUM_REQS-1:0] rdata_outstanding_n, rdata_outstanding_s, rdata_outstanding_q;
  logic [NUM_REQS-1:0] branch_discard_n, branch_discard_s, branch_discard_q;
  logic [NUM_REQS-1:0] rdata_pmp_err_n, rdata_pmp_err_s, rdata_pmp_err_q;
  logic [NUM_REQS-1:0] rdata_outstanding_rev;

  logic [31:0]         stored_addr_d, stored_addr_q;
  logic                stored_addr_en;
  logic [31:0]         fetch_addr_d, fetch_addr_q;
  logic                fetch_addr_en;
  logic [31:0]         branch_mispredict_addr;
  logic [31:0]         instr_addr, instr_addr_w_aligned;
  logic                instr_or_pmp_err;

  logic                fifo_valid;
  logic [31:0]         fifo_addr;
  logic                fifo_ready;
  logic                fifo_clear;
  logic [NUM_REQS-1:0] fifo_busy;

  logic                valid_raw;

  logic [31:0]         addr_next;

  logic                branch_or_mispredict;

  ////////////////////////////
  // Prefetch buffer status //
  ////////////////////////////

  assign busy_o = (|rdata_outstanding_q) | instr_req_o;

  assign branch_or_mispredict = branch_i | branch_mispredict_i;

  //////////////////////////////////////////////
  // Fetch fifo - consumes addresses and data //
  //////////////////////////////////////////////

  // Instruction fetch errors are valid on the data phase of a request
  // PMP errors are generated in the address phase, and registered into a fake data phase
  assign instr_or_pmp_err = instr_err_i | rdata_pmp_err_q[0];

  // A branch will invalidate any previously fetched instructions.
  // Note that the FENCE.I instruction relies on this flushing behaviour on branch. If it is
  // altered the FENCE.I implementation may require changes.
  assign fifo_clear = branch_or_mispredict;

  // Reversed version of rdata_outstanding_q which can be overlaid with fifo fill state
  for (genvar i = 0; i < NUM_REQS; i++) begin : gen_rd_rev
    assign rdata_outstanding_rev[i] = rdata_outstanding_q[NUM_REQS-1-i];
  end

  // The fifo is ready to accept a new request if it is not full - including space reserved for
  // requests already outstanding.
  // Overlay the fifo fill state with the outstanding requests to see if there is space.
  assign fifo_ready = ~&(fifo_busy | rdata_outstanding_rev);

  ibex_fetch_fifo #(
    .NUM_REQS (NUM_REQS),
    .ResetAll (ResetAll)
  ) fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),
      .busy_o                ( fifo_busy         ),

      .in_valid_i            ( fifo_valid        ),
      .in_addr_i             ( fifo_addr         ),
      .in_rdata_i            ( instr_rdata_i     ),
      .in_err_i              ( instr_or_pmp_err  ),

      .out_valid_o           ( valid_raw         ),
      .out_ready_i           ( ready_i           ),
      .out_rdata_o           ( rdata_o           ),
      .out_addr_o            ( addr_o            ),
      .out_addr_next_o       ( addr_next         ),
      .out_err_o             ( err_o             ),
      .out_err_plus2_o       ( err_plus2_o       )
  );

  //////////////
  // Requests //
  //////////////

  // Suppress a new request on a not-taken branch (as the external address will be incorrect)
  assign branch_suppress = branch_spec_i & ~branch_i;

  // Make a new request any time there is space in the FIFO, and space in the request queue
  assign valid_new_req = ~branch_suppress & req_i & (fifo_ready | branch_or_mispredict) &
                         ~rdata_outstanding_q[NUM_REQS-1];

  assign valid_req = valid_req_q | valid_new_req;

  // If a request address triggers a PMP error, the external bus request is suppressed. We might
  // therefore never receive a grant for such a request. The grant is faked in this case to make
  // sure the request proceeds and the error is pushed to the FIFO.
  assign gnt_or_pmp_err = instr_gnt_i | instr_pmp_err_i;

  // As with the grant, the rvalid must be faked for a PMP error, since the request was suppressed.
  assign rvalid_or_pmp_err = rdata_outstanding_q[0] & (instr_rvalid_i | rdata_pmp_err_q[0]);

  // Hold the request stable for requests that didn't get granted
  assign valid_req_d = valid_req & ~gnt_or_pmp_err;

  // Record whether an outstanding bus request is cancelled by a branch
  assign discard_req_d = valid_req_q & (branch_or_mispredict | discard_req_q);

  ////////////////
  // Fetch addr //
  ////////////////

  // Two addresses are tracked in the prefetch buffer:
  // 1. stored_addr_q - This is the address issued on the bus. It stays stable until
  //                    the request is granted.
  // 2. fetch_addr_q  - This is our next address to fetch from. It is updated on branches to
  //                    capture the new address, and then for each new request issued.
  // A third address is tracked in the fetch FIFO itself:
  // 3. instr_addr_q  - This is the address at the head of the FIFO, efectively our oldest fetched
  //                    address. This address is updated on branches, and does its own increment
  //                    each time the FIFO is popped.

  // 1. stored_addr_q

  // Only update stored_addr_q for new ungranted requests
  assign stored_addr_en = valid_new_req & ~valid_req_q & ~gnt_or_pmp_err;

  // Store whatever address was issued on the bus
  assign stored_addr_d = instr_addr;

  // CPU resets with a branch, so no need to reset these addresses
  if (ResetAll) begin : g_stored_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        stored_addr_q <= '0;
      end else if (stored_addr_en) begin
        stored_addr_q <= stored_addr_d;
      end
    end
  end else begin : g_stored_addr_nr
    always_ff @(posedge clk_i) begin
      if (stored_addr_en) begin
        stored_addr_q <= stored_addr_d;
      end
    end
  end

  if (BranchPredictor) begin : g_branch_predictor
    // Where the branch predictor is present record what address followed a predicted branch.  If
    // that branch is predicted taken but mispredicted (so not-taken) this is used to resume on
    // the not-taken code path.
    logic [31:0] branch_mispredict_addr_q;
    logic        branch_mispredict_addr_en;

    assign branch_mispredict_addr_en = branch_i & predicted_branch_i;

    if (ResetAll) begin : g_branch_misp_addr_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          branch_mispredict_addr_q <= '0;
        end else if (branch_mispredict_addr_en) begin
          branch_mispredict_addr_q <= addr_next;
        end
      end
    end else begin : g_branch_misp_addr_nr
      always_ff @(posedge clk_i) begin
        if (branch_mispredict_addr_en) begin
          branch_mispredict_addr_q <= addr_next;
        end
      end
    end

    assign branch_mispredict_addr = branch_mispredict_addr_q;
  end else begin : g_no_branch_predictor
    logic        unused_predicted_branch;
    logic [31:0] unused_addr_next;

    assign unused_predicted_branch = predicted_branch_i;
    assign unused_addr_next        = addr_next;

    assign branch_mispredict_addr = '0;
  end

  // 2. fetch_addr_q

  // Update on a branch or as soon as a request is issued
  assign fetch_addr_en = branch_or_mispredict | (valid_new_req & ~valid_req_q);

  assign fetch_addr_d = (branch_i            ? addr_i :
                         branch_mispredict_i ? {branch_mispredict_addr[31:2], 2'b00} :
                                               {fetch_addr_q[31:2], 2'b00}) +
                        // Current address + 4
                        {{29{1'b0}},(valid_new_req & ~valid_req_q),2'b00};

  if (ResetAll) begin : g_fetch_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fetch_addr_q <= '0;
      end else if (fetch_addr_en) begin
        fetch_addr_q <= fetch_addr_d;
      end
    end
  end else begin : g_fetch_addr_nr
    always_ff @(posedge clk_i) begin
      if (fetch_addr_en) begin
        fetch_addr_q <= fetch_addr_d;
      end
    end
  end

  // Address mux
  assign instr_addr = valid_req_q         ? stored_addr_q :
                      branch_spec_i       ? addr_i :
                      branch_mispredict_i ? branch_mispredict_addr :
                                            fetch_addr_q;

  assign instr_addr_w_aligned = {instr_addr[31:2], 2'b00};

  ///////////////////////////////
  // Request outstanding queue //
  ///////////////////////////////

  for (genvar i = 0; i < NUM_REQS; i++) begin : g_outstanding_reqs
    // Request 0 (always the oldest outstanding request)
    if (i == 0) begin : g_req0
      // A request becomes outstanding once granted, and is cleared once the rvalid is received.
      // Outstanding requests shift down the queue towards entry 0.
      assign rdata_outstanding_n[i] = (valid_req & gnt_or_pmp_err) |
                                      rdata_outstanding_q[i];
      // If a branch is received at any point while a request is outstanding, it must be tracked
      // to ensure we discard the data once received
      assign branch_discard_n[i]    = (valid_req & gnt_or_pmp_err & discard_req_d) |
                                      (branch_or_mispredict & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];
      // Record whether this request received a PMP error
      assign rdata_pmp_err_n[i]     = (valid_req & ~rdata_outstanding_q[i] & instr_pmp_err_i) |
                                      rdata_pmp_err_q[i];

    end else begin : g_reqtop
    // Entries > 0 consider the FIFO fill state to calculate their next state (by checking
    // whether the previous entry is valid)

      assign rdata_outstanding_n[i] = (valid_req & gnt_or_pmp_err &
                                       rdata_outstanding_q[i-1]) |
                                      rdata_outstanding_q[i];
      assign branch_discard_n[i]    = (valid_req & gnt_or_pmp_err & discard_req_d &
                                       rdata_outstanding_q[i-1]) |
                                      (branch_or_mispredict & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];
      assign rdata_pmp_err_n[i]     = (valid_req & ~rdata_outstanding_q[i] & instr_pmp_err_i &
                                       rdata_outstanding_q[i-1]) |
                                      rdata_pmp_err_q[i];
    end
  end

  // Shift the entries down on each instr_rvalid_i
  assign rdata_outstanding_s = rvalid_or_pmp_err ? {1'b0,rdata_outstanding_n[NUM_REQS-1:1]} :
                                                   rdata_outstanding_n;
  assign branch_discard_s    = rvalid_or_pmp_err ? {1'b0,branch_discard_n[NUM_REQS-1:1]} :
                                                   branch_discard_n;
  assign rdata_pmp_err_s     = rvalid_or_pmp_err ? {1'b0,rdata_pmp_err_n[NUM_REQS-1:1]} :
                                                   rdata_pmp_err_n;

  // Push a new entry to the FIFO once complete (and not cancelled by a branch)
  assign fifo_valid = rvalid_or_pmp_err & ~branch_discard_q[0];

  assign fifo_addr = branch_i ? addr_i : branch_mispredict_addr;

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_req_q          <= 1'b0;
      discard_req_q        <= 1'b0;
      rdata_outstanding_q  <= 'b0;
      branch_discard_q     <= 'b0;
      rdata_pmp_err_q      <= 'b0;
    end else begin
      valid_req_q          <= valid_req_d;
      discard_req_q        <= discard_req_d;
      rdata_outstanding_q  <= rdata_outstanding_s;
      branch_discard_q     <= branch_discard_s;
      rdata_pmp_err_q      <= rdata_pmp_err_s;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign instr_req_o  = valid_req;
  assign instr_addr_o = instr_addr_w_aligned;

  assign valid_o = valid_raw & ~branch_mispredict_i;

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */
module ibex_register_file_ff #(
    parameter bit          RV32E             = 0,
    parameter int unsigned DataWidth         = 32,
    parameter bit          DummyInstructions = 0
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    input  logic                 test_en_i,
    input  logic                 dummy_instr_id_i,

    //Read port R1
    input  logic [4:0]           raddr_a_i,
    output logic [DataWidth-1:0] rdata_a_o,

    //Read port R2
    input  logic [4:0]           raddr_b_i,
    output logic [DataWidth-1:0] rdata_b_o,


    // Write port W1
    input  logic [4:0]           waddr_a_i,
    input  logic [DataWidth-1:0] wdata_a_i,
    input  logic                 we_a_i

);

  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [NUM_WORDS-1:0][DataWidth-1:0] rf_reg;
  logic [NUM_WORDS-1:1][DataWidth-1:0] rf_reg_q;
  logic [NUM_WORDS-1:1]                we_a_dec;

  always_comb begin : we_a_decoder
    for (int unsigned i = 1; i < NUM_WORDS; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ?  we_a_i : 1'b0;
    end
  end

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_flops
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q[i] <= '0;
      end else if(we_a_dec[i]) begin
        rf_reg_q[i] <= wdata_a_i;
      end
    end
  end

  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    logic                 we_r0_dummy;
    logic [DataWidth-1:0] rf_r0_q;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_id_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_r0_q <= '0;
      end else if (we_r0_dummy) begin
        rf_r0_q <= wdata_a_i;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign rf_reg[0] = dummy_instr_id_i ? rf_r0_q : '0;

  end else begin : g_normal_r0
    logic unused_dummy_instr_id;
    assign unused_dummy_instr_id = dummy_instr_id_i;

    // R0 is nil
    assign rf_reg[0] = '0;
  end

  assign rf_reg[NUM_WORDS-1:1] = rf_reg_q[NUM_WORDS-1:1];

  assign rdata_a_o = rf_reg[raddr_a_i];
  assign rdata_b_o = rf_reg[raddr_b_i];

  // Signal not used in FF register file
  logic unused_test_en;
  assign unused_test_en = test_en_i;

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module ibex_register_file_fpga #(
  parameter bit          RV32E             = 0,
  parameter int unsigned DataWidth         = 32,
  parameter bit          DummyInstructions = 0
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,

  //Read port R1
  input  logic [          4:0] raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,
  //Read port R2
  input  logic [          4:0] raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,
  // Write port W1
  input  logic [          4:0] waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i
);

  localparam int ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int NUM_WORDS  = 2**ADDR_WIDTH;

  logic [DataWidth-1:0] mem[NUM_WORDS];
  logic we; // write enable if writing to any register other than R0

  // async_read a
  assign rdata_a_o = (raddr_a_i == '0) ? '0 : mem[raddr_a_i];

  // async_read b
  assign rdata_b_o = (raddr_b_i == '0) ? '0 : mem[raddr_b_i];

  // we select
  assign we = (waddr_a_i == '0) ? 1'b0 : we_a_i;

  always_ff @(posedge clk_i) begin : sync_write
    if (we == 1'b1) begin
      mem[waddr_a_i] <= wdata_a_i;
    end
  end : sync_write

  // Reset not used in this register file version
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // Dummy instruction changes not relevant for FPGA implementation
  logic unused_dummy_instr;
  assign unused_dummy_instr = dummy_instr_id_i;
  // Test enable signal not used in FPGA implementation
  logic unused_test_en;
  assign unused_test_en = test_en_i;

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on latches and is thus smaller than the flip-flop
 * based RF. It requires a target technology-specific clock gating cell. Use this
 * register file when targeting ASIC synthesis or event-based simulators.
 */
module ibex_register_file_latch #(
    parameter bit          RV32E             = 0,
    parameter int unsigned DataWidth         = 32,
    parameter bit          DummyInstructions = 0
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    input  logic                 test_en_i,
    input  logic                 dummy_instr_id_i,

    //Read port R1
    input  logic [4:0]           raddr_a_i,
    output logic [DataWidth-1:0] rdata_a_o,

    //Read port R2
    input  logic [4:0]           raddr_b_i,
    output logic [DataWidth-1:0] rdata_b_o,

    // Write port W1
    input  logic [4:0]           waddr_a_i,
    input  logic [DataWidth-1:0] wdata_a_i,
    input  logic                 we_a_i

);

  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [DataWidth-1:0] mem[NUM_WORDS];

  logic [NUM_WORDS-1:1] waddr_onehot_a;

  logic [NUM_WORDS-1:1] mem_clocks;
  logic [DataWidth-1:0] wdata_a_q;

  // internal addresses
  logic [ADDR_WIDTH-1:0] raddr_a_int, raddr_b_int, waddr_a_int;

  assign raddr_a_int = raddr_a_i[ADDR_WIDTH-1:0];
  assign raddr_b_int = raddr_b_i[ADDR_WIDTH-1:0];
  assign waddr_a_int = waddr_a_i[ADDR_WIDTH-1:0];

  logic clk_int;

  //////////
  // READ //
  //////////
  assign rdata_a_o = mem[raddr_a_int];
  assign rdata_b_o = mem[raddr_b_int];

  ///////////
  // WRITE //
  ///////////
  // Global clock gating
  prim_clock_gating cg_we_global (
      .clk_i     ( clk_i     ),
      .en_i      ( we_a_i    ),
      .test_en_i ( test_en_i ),
      .clk_o     ( clk_int   )
  );

  // Sample input data
  // Use clk_int here, since otherwise we don't want to write anything anyway.
  always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
    if (!rst_ni) begin
      wdata_a_q   <= '0;
    end else begin
      if (we_a_i) begin
        wdata_a_q <= wdata_a_i;
      end
    end
  end

  // Write address decoding
  always_comb begin : wad
    for (int i = 1; i < NUM_WORDS; i++) begin : wad_word_iter
      if (we_a_i && (waddr_a_int == 5'(i))) begin
        waddr_onehot_a[i] = 1'b1;
      end else begin
        waddr_onehot_a[i] = 1'b0;
      end
    end
  end

  // Individual clock gating (if integrated clock-gating cells are available)
  for (genvar x = 1; x < NUM_WORDS; x++) begin : gen_cg_word_iter
    prim_clock_gating cg_i (
        .clk_i     ( clk_int           ),
        .en_i      ( waddr_onehot_a[x] ),
        .test_en_i ( test_en_i         ),
        .clk_o     ( mem_clocks[x]     )
    );
  end

  // Actual write operation:
  // Generate the sequential process for the NUM_WORDS words of the memory.
  // The process is synchronized with the clocks mem_clocks[i], i = 1, ..., NUM_WORDS-1.
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_latches
    always_latch begin
      if (mem_clocks[i]) begin
        mem[i] = wdata_a_q;
      end
    end
  end

  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    logic                 we_r0_dummy;
    logic                 r0_clock;
    logic [DataWidth-1:0] mem_r0;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_id_i;

    // R0 clock gate
    prim_clock_gating cg_i (
        .clk_i     ( clk_int     ),
        .en_i      ( we_r0_dummy ),
        .test_en_i ( test_en_i   ),
        .clk_o     ( r0_clock    )
    );

    always_latch begin : latch_wdata
      if (r0_clock) begin
        mem_r0 = wdata_a_q;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign mem[0] = dummy_instr_id_i ? mem_r0 : '0;

  end else begin : g_normal_r0
    logic unused_dummy_instr_id;
    assign unused_dummy_instr_id = dummy_instr_id_i;

    assign mem[0] = '0;
  end

`ifdef VERILATOR
  initial begin
    $display("Latch-based register file not supported for Verilator simulation");
    $fatal;
  end
`endif

endmodule
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_top import ibex_pkg::*; #(
    parameter bit          PMPEnable        = 1'b0,
    parameter int unsigned PMPGranularity   = 0,
    parameter int unsigned PMPNumRegions    = 4,
    parameter int unsigned MHPMCounterNum   = 0,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit          RV32E            = 1'b0,
    parameter rv32m_e      RV32M            = RV32MFast,
    parameter rv32b_e      RV32B            = RV32BNone,
    parameter regfile_e    RegFile          = RegFileFF,
    parameter bit          BranchTargetALU  = 1'b0,
    parameter bit          WritebackStage   = 1'b0,
    parameter bit          ICache           = 1'b0,
    parameter bit          ICacheECC        = 1'b0,
    parameter bit          BranchPredictor  = 1'b0,
    parameter bit          DbgTriggerEn     = 1'b0,
    parameter int unsigned DbgHwBreakNum    = 1,
    parameter bit          SecureIbex       = 1'b0,
    parameter lfsr_seed_t  RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t  RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
    parameter int unsigned DmHaltAddr       = 32'h1A110800,
    parameter int unsigned DmExceptionAddr  = 32'h1A110808
) (
    // Clock and Reset
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic                         test_en_i,     // enable all clock gates for testing
    input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    // Instruction memory interface
    output logic                         instr_req_o,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    output logic [31:0]                  instr_addr_o,
    input  logic [31:0]                  instr_rdata_i,
    input  logic [6:0]                   instr_rdata_intg_i,
    input  logic                         instr_err_i,

    // Data memory interface
    output logic                         data_req_o,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    output logic                         data_we_o,
    output logic [3:0]                   data_be_o,
    output logic [31:0]                  data_addr_o,
    output logic [31:0]                  data_wdata_o,
    output logic [6:0]                   data_wdata_intg_o,
    input  logic [31:0]                  data_rdata_i,
    input  logic [6:0]                   data_rdata_intg_i,
    input  logic                         data_err_i,

    // Interrupt inputs
    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,       // non-maskeable interrupt

    // Debug Interface
    input  logic                         debug_req_i,
    output crash_dump_t                  crash_dump_o,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic                         rvfi_valid,
    output logic [63:0]                  rvfi_order,
    output logic [31:0]                  rvfi_insn,
    output logic                         rvfi_trap,
    output logic                         rvfi_halt,
    output logic                         rvfi_intr,
    output logic [ 1:0]                  rvfi_mode,
    output logic [ 1:0]                  rvfi_ixl,
    output logic [ 4:0]                  rvfi_rs1_addr,
    output logic [ 4:0]                  rvfi_rs2_addr,
    output logic [ 4:0]                  rvfi_rs3_addr,
    output logic [31:0]                  rvfi_rs1_rdata,
    output logic [31:0]                  rvfi_rs2_rdata,
    output logic [31:0]                  rvfi_rs3_rdata,
    output logic [ 4:0]                  rvfi_rd_addr,
    output logic [31:0]                  rvfi_rd_wdata,
    output logic [31:0]                  rvfi_pc_rdata,
    output logic [31:0]                  rvfi_pc_wdata,
    output logic [31:0]                  rvfi_mem_addr,
    output logic [ 3:0]                  rvfi_mem_rmask,
    output logic [ 3:0]                  rvfi_mem_wmask,
    output logic [31:0]                  rvfi_mem_rdata,
    output logic [31:0]                  rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic                         fetch_enable_i,
    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    output logic                         core_sleep_o,

    // DFT bypass controls
    input logic                          scan_rst_ni
);

  localparam bit          Lockstep          = SecureIbex;
  localparam bit          ResetAll          = Lockstep;
  localparam bit          DummyInstructions = SecureIbex;
  localparam bit          RegFileECC        = SecureIbex;
  localparam int unsigned RegFileDataWidth  = RegFileECC ? 32 + 7 : 32;
  // Icache parameters
  localparam int unsigned BusSizeECC        = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC       = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC        = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;

  // Clock signals
  logic                        clk;
  logic                        core_busy_d, core_busy_q;
  logic                        clock_en;
  logic                        irq_pending;
  // Core <-> Register file signals
  logic                        dummy_instr_id;
  logic [4:0]                  rf_raddr_a;
  logic [4:0]                  rf_raddr_b;
  logic [4:0]                  rf_waddr_wb;
  logic                        rf_we_wb;
  logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_a_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_b_ecc;
  // Core <-> RAMs signals
  logic [IC_NUM_WAYS-1:0]      ic_tag_req;
  logic                        ic_tag_write;
  logic [IC_INDEX_W-1:0]       ic_tag_addr;
  logic [TagSizeECC-1:0]       ic_tag_wdata;
  logic [TagSizeECC-1:0]       ic_tag_rdata [IC_NUM_WAYS];
  logic [IC_NUM_WAYS-1:0]      ic_data_req;
  logic                        ic_data_write;
  logic [IC_INDEX_W-1:0]       ic_data_addr;
  logic [LineSizeECC-1:0]      ic_data_wdata;
  logic [LineSizeECC-1:0]      ic_data_rdata [IC_NUM_WAYS];
  // Alert signals
  logic                        core_alert_major, core_alert_minor;
  logic                        lockstep_alert_major, lockstep_alert_minor;

  /////////////////////
  // Main clock gate //
  /////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_d;
    end
  end

  assign clock_en     = core_busy_q | debug_req_i | irq_pending | irq_nm_i;
  assign core_sleep_o = ~clock_en;

  prim_clock_gating core_clock_gate_i (
      .clk_i     ( clk_i           ),
      .en_i      ( clock_en        ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk             )
  );

  ////////////////////////
  // Core instantiation //
  ////////////////////////

  ibex_core #(
    .PMPEnable         ( PMPEnable         ),
    .PMPGranularity    ( PMPGranularity    ),
    .PMPNumRegions     ( PMPNumRegions     ),
    .MHPMCounterNum    ( MHPMCounterNum    ),
    .MHPMCounterWidth  ( MHPMCounterWidth  ),
    .RV32E             ( RV32E             ),
    .RV32M             ( RV32M             ),
    .RV32B             ( RV32B             ),
    .BranchTargetALU   ( BranchTargetALU   ),
    .ICache            ( ICache            ),
    .ICacheECC         ( ICacheECC         ),
    .BusSizeECC        ( BusSizeECC        ),
    .TagSizeECC        ( TagSizeECC        ),
    .LineSizeECC       ( LineSizeECC       ),
    .BranchPredictor   ( BranchPredictor   ),
    .DbgTriggerEn      ( DbgTriggerEn      ),
    .DbgHwBreakNum     ( DbgHwBreakNum     ),
    .WritebackStage    ( WritebackStage    ),
    .ResetAll          ( ResetAll          ),
    .RndCnstLfsrSeed   ( RndCnstLfsrSeed   ),
    .RndCnstLfsrPerm   ( RndCnstLfsrPerm   ),
    .SecureIbex        ( SecureIbex        ),
    .DummyInstructions ( DummyInstructions ),
    .RegFileECC        ( RegFileECC        ),
    .RegFileDataWidth  ( RegFileDataWidth  ),
    .DmHaltAddr        ( DmHaltAddr        ),
    .DmExceptionAddr   ( DmExceptionAddr   )
  ) u_ibex_core (
    .clk_i (clk),
    .rst_ni,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_err_i,

    .data_req_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_rdata_i,
    .data_err_i,

    .dummy_instr_id_o  (dummy_instr_id),
    .rf_raddr_a_o      (rf_raddr_a),
    .rf_raddr_b_o      (rf_raddr_b),
    .rf_waddr_wb_o     (rf_waddr_wb),
    .rf_we_wb_o        (rf_we_wb),
    .rf_wdata_wb_ecc_o (rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i  (rf_rdata_a_ecc),
    .rf_rdata_b_ecc_i  (rf_rdata_b_ecc),

    .ic_tag_req_o      (ic_tag_req),
    .ic_tag_write_o    (ic_tag_write),
    .ic_tag_addr_o     (ic_tag_addr),
    .ic_tag_wdata_o    (ic_tag_wdata),
    .ic_tag_rdata_i    (ic_tag_rdata),
    .ic_data_req_o     (ic_data_req),
    .ic_data_write_o   (ic_data_write),
    .ic_data_addr_o    (ic_data_addr),
    .ic_data_wdata_o   (ic_data_wdata),
    .ic_data_rdata_i   (ic_data_rdata),

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,
    .irq_pending_o (irq_pending),

    .debug_req_i,
    .crash_dump_o,

`ifdef RVFI
    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
`endif

    .fetch_enable_i,
    .alert_minor_o (core_alert_minor),
    .alert_major_o (core_alert_major),
    .core_busy_o (core_busy_d)
  );

  /////////////////////////////////
  // Register file Instantiation //
  /////////////////////////////////

  if (RegFile == RegFileFF) begin : gen_regfile_ff
    ibex_register_file_ff #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end else if (RegFile == RegFileFPGA) begin : gen_regfile_fpga
    ibex_register_file_fpga #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end else if (RegFile == RegFileLatch) begin : gen_regfile_latch
    ibex_register_file_latch #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end

  ////////////////////////
  // Rams Instantiation //
  ////////////////////////

  if (ICache) begin : gen_rams

    for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams_inner
      // Tag RAM instantiation
      prim_ram_1p #(
        .Width           (TagSizeECC),
        .Depth           (IC_NUM_LINES),
        .DataBitsPerMask (TagSizeECC)
      ) tag_bank (
        .clk_i    (clk_i),
        .req_i    (ic_tag_req[way]),
        .cfg_i    (ram_cfg_i),
        .write_i  (ic_tag_write),
        .wmask_i  ({TagSizeECC{1'b1}}),
        .addr_i   (ic_tag_addr),
        .wdata_i  (ic_tag_wdata),
        .rdata_o  (ic_tag_rdata[way])
      );
      // Data RAM instantiation
      prim_ram_1p #(
        .Width           (LineSizeECC),
        .Depth           (IC_NUM_LINES),
        .DataBitsPerMask (LineSizeECC)
      ) data_bank (
        .clk_i    (clk_i),
        .req_i    (ic_data_req[way]),
        .cfg_i    (ram_cfg_i),
        .write_i  (ic_data_write),
        .wmask_i  ({LineSizeECC{1'b1}}),
        .addr_i   (ic_data_addr),
        .wdata_i  (ic_data_wdata),
        .rdata_o  (ic_data_rdata[way])
      );
    end

  end else begin : gen_norams

    prim_ram_1p_pkg::ram_1p_cfg_t unused_ram_cfg;
    logic unused_ram_inputs;

    assign unused_ram_cfg    = ram_cfg_i;
    assign unused_ram_inputs = (|ic_tag_req) & ic_tag_write & (|ic_tag_addr) & (|ic_tag_wdata) &
                               (|ic_data_req) & ic_data_write & (|ic_data_addr) & (|ic_data_wdata);
    assign ic_tag_rdata      = '{default:'b0};
    assign ic_data_rdata     = '{default:'b0};

  end

  // Redundant lockstep core implementation
  if (Lockstep) begin : gen_lockstep
    // Note: certain synthesis tools like DC are very smart at optimizing away redundant logic.
    // Hence, we have to insert an optimization barrier at the IOs of the lockstep Ibex.
    // This is achieved by manually buffering each bit using prim_buf.
    // Our Xilinx and DC synthesis flows make sure that these buffers cannot be optimized away
    // using keep attributes (Vivado) and size_only constraints (DC).

    localparam int NumBufferBits = $bits({
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_rdata_intg_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_rdata_i,
      data_rdata_intg_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      fetch_enable_i,
      core_busy_d
    });

    logic [NumBufferBits-1:0] buf_in, buf_out;

    logic [31:0]                  hart_id_local;
    logic [31:0]                  boot_addr_local;

    logic                         instr_req_local;
    logic                         instr_gnt_local;
    logic                         instr_rvalid_local;
    logic [31:0]                  instr_addr_local;
    logic [31:0]                  instr_rdata_local;
    logic [6:0]                   instr_rdata_intg_local;
    logic                         instr_err_local;

    logic                         data_req_local;
    logic                         data_gnt_local;
    logic                         data_rvalid_local;
    logic                         data_we_local;
    logic [3:0]                   data_be_local;
    logic [31:0]                  data_addr_local;
    logic [31:0]                  data_wdata_local;
    logic [6:0]                   data_wdata_intg_local;
    logic [31:0]                  data_rdata_local;
    logic [6:0]                   data_rdata_intg_local;
    logic                         data_err_local;

    logic                         dummy_instr_id_local;
    logic [4:0]                   rf_raddr_a_local;
    logic [4:0]                   rf_raddr_b_local;
    logic [4:0]                   rf_waddr_wb_local;
    logic                         rf_we_wb_local;
    logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_local;

    logic [IC_NUM_WAYS-1:0]       ic_tag_req_local;
    logic                         ic_tag_write_local;
    logic [IC_INDEX_W-1:0]        ic_tag_addr_local;
    logic [TagSizeECC-1:0]        ic_tag_wdata_local;
    logic [IC_NUM_WAYS-1:0]       ic_data_req_local;
    logic                         ic_data_write_local;
    logic [IC_INDEX_W-1:0]        ic_data_addr_local;
    logic [LineSizeECC-1:0]       ic_data_wdata_local;

    logic                         irq_software_local;
    logic                         irq_timer_local;
    logic                         irq_external_local;
    logic [14:0]                  irq_fast_local;
    logic                         irq_nm_local;
    logic                         irq_pending_local;

    logic                         debug_req_local;
    crash_dump_t                  crash_dump_local;
    logic                         fetch_enable_local;

    logic                         core_busy_local;

    assign buf_in = {
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_rdata_intg_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_rdata_i,
      data_rdata_intg_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      fetch_enable_i,
      core_busy_d
    };

    assign {
      hart_id_local,
      boot_addr_local,
      instr_req_local,
      instr_gnt_local,
      instr_rvalid_local,
      instr_addr_local,
      instr_rdata_local,
      instr_rdata_intg_local,
      instr_err_local,
      data_req_local,
      data_gnt_local,
      data_rvalid_local,
      data_we_local,
      data_be_local,
      data_addr_local,
      data_wdata_local,
      data_rdata_local,
      data_rdata_intg_local,
      data_err_local,
      dummy_instr_id_local,
      rf_raddr_a_local,
      rf_raddr_b_local,
      rf_waddr_wb_local,
      rf_we_wb_local,
      rf_wdata_wb_ecc_local,
      rf_rdata_a_ecc_local,
      rf_rdata_b_ecc_local,
      ic_tag_req_local,
      ic_tag_write_local,
      ic_tag_addr_local,
      ic_tag_wdata_local,
      ic_data_req_local,
      ic_data_write_local,
      ic_data_addr_local,
      ic_data_wdata_local,
      irq_software_local,
      irq_timer_local,
      irq_external_local,
      irq_fast_local,
      irq_nm_local,
      irq_pending_local,
      debug_req_local,
      crash_dump_local,
      fetch_enable_local,
      core_busy_local
    } = buf_out;

    // Manually buffer all input signals.
    prim_buf #(.Width(NumBufferBits)) u_signals_prim_buf (
      .in_i(buf_in),
      .out_o(buf_out)
    );

    logic [TagSizeECC-1:0]  ic_tag_rdata_local [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] ic_data_rdata_local [IC_NUM_WAYS];
    for (genvar k = 0; k < IC_NUM_WAYS; k++) begin : gen_ways
      prim_buf #(.Width(TagSizeECC)) u_tag_prim_buf (
        .in_i(ic_tag_rdata[k]),
        .out_o(ic_tag_rdata_local[k])
      );
      prim_buf #(.Width(LineSizeECC)) u_data_prim_buf (
        .in_i(ic_data_rdata[k]),
        .out_o(ic_data_rdata_local[k])
      );
    end

    logic lockstep_alert_minor_local, lockstep_alert_major_local;
    ibex_lockstep #(
      .PMPEnable         ( PMPEnable         ),
      .PMPGranularity    ( PMPGranularity    ),
      .PMPNumRegions     ( PMPNumRegions     ),
      .MHPMCounterNum    ( MHPMCounterNum    ),
      .MHPMCounterWidth  ( MHPMCounterWidth  ),
      .RV32E             ( RV32E             ),
      .RV32M             ( RV32M             ),
      .RV32B             ( RV32B             ),
      .BranchTargetALU   ( BranchTargetALU   ),
      .ICache            ( ICache            ),
      .ICacheECC         ( ICacheECC         ),
      .BusSizeECC        ( BusSizeECC        ),
      .TagSizeECC        ( TagSizeECC        ),
      .LineSizeECC       ( LineSizeECC       ),
      .BranchPredictor   ( BranchPredictor   ),
      .DbgTriggerEn      ( DbgTriggerEn      ),
      .DbgHwBreakNum     ( DbgHwBreakNum     ),
      .WritebackStage    ( WritebackStage    ),
      .ResetAll          ( ResetAll          ),
      .RndCnstLfsrSeed   ( RndCnstLfsrSeed   ),
      .RndCnstLfsrPerm   ( RndCnstLfsrPerm   ),
      .SecureIbex        ( SecureIbex        ),
      .DummyInstructions ( DummyInstructions ),
      .RegFileECC        ( RegFileECC        ),
      .RegFileDataWidth  ( RegFileDataWidth  ),
      .DmHaltAddr        ( DmHaltAddr        ),
      .DmExceptionAddr   ( DmExceptionAddr   )
    ) u_ibex_lockstep (
      .clk_i              (clk),
      .rst_ni             (rst_ni),

      .hart_id_i          (hart_id_local),
      .boot_addr_i        (boot_addr_local),

      .instr_req_i        (instr_req_local),
      .instr_gnt_i        (instr_gnt_local),
      .instr_rvalid_i     (instr_rvalid_local),
      .instr_addr_i       (instr_addr_local),
      .instr_rdata_i      (instr_rdata_local),
      .instr_rdata_intg_i (instr_rdata_intg_local),
      .instr_err_i        (instr_err_local),

      .data_req_i         (data_req_local),
      .data_gnt_i         (data_gnt_local),
      .data_rvalid_i      (data_rvalid_local),
      .data_we_i          (data_we_local),
      .data_be_i          (data_be_local),
      .data_addr_i        (data_addr_local),
      .data_wdata_i       (data_wdata_local),
      .data_wdata_intg_o  (data_wdata_intg_local),
      .data_rdata_i       (data_rdata_local),
      .data_rdata_intg_i  (data_rdata_intg_local),
      .data_err_i         (data_err_local),

      .dummy_instr_id_i   (dummy_instr_id_local),
      .rf_raddr_a_i       (rf_raddr_a_local),
      .rf_raddr_b_i       (rf_raddr_b_local),
      .rf_waddr_wb_i      (rf_waddr_wb_local),
      .rf_we_wb_i         (rf_we_wb_local),
      .rf_wdata_wb_ecc_i  (rf_wdata_wb_ecc_local),
      .rf_rdata_a_ecc_i   (rf_rdata_a_ecc_local),
      .rf_rdata_b_ecc_i   (rf_rdata_b_ecc_local),

      .ic_tag_req_i       (ic_tag_req_local),
      .ic_tag_write_i     (ic_tag_write_local),
      .ic_tag_addr_i      (ic_tag_addr_local),
      .ic_tag_wdata_i     (ic_tag_wdata_local),
      .ic_tag_rdata_i     (ic_tag_rdata_local),
      .ic_data_req_i      (ic_data_req_local),
      .ic_data_write_i    (ic_data_write_local),
      .ic_data_addr_i     (ic_data_addr_local),
      .ic_data_wdata_i    (ic_data_wdata_local),
      .ic_data_rdata_i    (ic_data_rdata_local),

      .irq_software_i     (irq_software_local),
      .irq_timer_i        (irq_timer_local),
      .irq_external_i     (irq_external_local),
      .irq_fast_i         (irq_fast_local),
      .irq_nm_i           (irq_nm_local),
      .irq_pending_i      (irq_pending_local),

      .debug_req_i        (debug_req_local),
      .crash_dump_i       (crash_dump_local),

      .fetch_enable_i     (fetch_enable_local),
      .alert_minor_o      (lockstep_alert_minor_local),
      .alert_major_o      (lockstep_alert_major_local),
      .core_busy_i        (core_busy_local),
      .test_en_i          (test_en_i),
      .scan_rst_ni        (scan_rst_ni)
    );

    // Manually buffer the output signals.
    prim_buf #(.Width (7)) u_prim_buf_wdata_intg (
      .in_i(data_wdata_intg_local),
      .out_o(data_wdata_intg_o)
    );

    prim_buf u_prim_buf_alert_minor (
      .in_i(lockstep_alert_minor_local),
      .out_o(lockstep_alert_minor)
    );

    prim_buf u_prim_buf_alert_major (
      .in_i(lockstep_alert_major_local),
      .out_o(lockstep_alert_major)
    );

  end else begin : gen_no_lockstep
    assign lockstep_alert_major = 1'b0;
    assign lockstep_alert_minor = 1'b0;
    assign data_wdata_intg_o    = 'b0;
    logic unused_scan, unused_intg;
    assign unused_scan = scan_rst_ni;
    assign unused_intg = |{instr_rdata_intg_i, data_rdata_intg_i};
  end

  assign alert_major_o = core_alert_major | lockstep_alert_major;
  assign alert_minor_o = core_alert_minor | lockstep_alert_minor;

  `ASSERT_KNOWN(IbexAlertMinorX, alert_minor_o)
  `ASSERT_KNOWN(IbexAlertMajorX, alert_major_o)

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Writeback Stage
 *
 * Writeback is an optional third pipeline stage. It writes data back to the register file that was
 * produced in the ID/EX stage or awaits a response to a load/store (LSU writes direct to register
 * file for load data). If the writeback stage is not present (WritebackStage == 0) this acts as
 * a simple passthrough to write data direct to the register file.
 */

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Disable it for synthesis and where explicitly requested (by defining
// DV_FCOV_DISABLE).
`ifdef SYNTHESIS
  `define DV_FCOV_DISABLE
`elsif YOSYS
  `define DV_FCOV_DISABLE
`endif

// Disable instantiations of FCOV coverpoints or covergroups.
`ifdef VERILATOR
  `define DV_FCOV_DISABLE_CP
`elsif DV_FCOV_DISABLE
  `define DV_FCOV_DISABLE_CP
`endif

// Instantiates a covergroup in an interface or module.
//
// This macro assumes that a covergroup of the same name as the NAME_ arg is defined in the
// interface or module. It just adds some extra signals and logic to control the creation of the
// covergroup instance with ~bit en_<cg_name>~. This defaults to 0. It is ORed with the external
// COND_ signal. The testbench can modify it at t = 0 based on the test being run.
// NOTE: This is not meant to be invoked inside a class.
//
// NAME_ : Name of the covergroup.
// COND_ : External condition / expr that controls the creation of the covergroup.
// ARGS_ : Arguments to covergroup instance, if any. Args MUST BE wrapped in (..).
`ifndef DV_FCOV_INSTANTIATE_CG
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ())
`else
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ()) \
    bit en_``NAME_ = 1'b0; \
    NAME_ NAME_``_inst; \
    initial begin \
      /* The #1 delay below allows any part of the tb to control the conditions first at t = 0. */ \
      #1; \
      if ((en_``NAME_) || (COND_)) begin \
        $display("%0t: (%0s:%0d) [%m] %0s", $time, `__FILE__, `__LINE__, \
                 {"Creating covergroup ", `"NAME_`"}); \
        NAME_``_inst = new``ARGS_; \
      end \
    end
`endif
`endif

// Creates a coverpoint for an expression where only the expression true case is of interest for
// coverage (e.g. where the expression indicates an event has occured).
`ifndef DV_FCOV_EXPR_SEEN
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_)
`else
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_) cp_``NAME_: coverpoint EXPR_ { bins seen = {1}; }
`endif
`endif

// Creates a SVA cover that can be used in a covergroup.
//
// This macro creates an unnamed SVA cover from the property (or an expression) `PROP_` and an event
// with the name `EV_NAME_`. When the SVA cover is hit, the event is triggered. A coverpoint can
// cover the `triggered` property of the event.
`ifndef DV_FCOV_SVA
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni)
`else
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni) \
    event EV_NAME_; \
    cover property (@(posedge CLK_) disable iff (RST_ == 0) (PROP_)) begin \
      -> EV_NAME_; \
    end
`endif
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef DV_FCOV_MARK_UNUSED
  `define DV_FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef DV_FCOV_SIGNAL
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef DV_FCOV_SIGNAL_GEN_IF
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

module ibex_wb_stage #(
  parameter bit ResetAll       = 1'b0,
  parameter bit WritebackStage = 1'b0
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     en_wb_i,
  input  ibex_pkg::wb_instr_type_e instr_type_wb_i,
  input  logic [31:0]              pc_id_i,
  input  logic                     instr_is_compressed_id_i,
  input  logic                     instr_perf_count_id_i,

  output logic                     ready_wb_o,
  output logic                     rf_write_wb_o,
  output logic                     outstanding_load_wb_o,
  output logic                     outstanding_store_wb_o,
  output logic [31:0]              pc_wb_o,
  output logic                     perf_instr_ret_wb_o,
  output logic                     perf_instr_ret_compressed_wb_o,

  input  logic [4:0]               rf_waddr_id_i,
  input  logic [31:0]              rf_wdata_id_i,
  input  logic                     rf_we_id_i,

  input  logic [31:0]              rf_wdata_lsu_i,
  input  logic                     rf_we_lsu_i,

  output logic [31:0]              rf_wdata_fwd_wb_o,

  output logic [4:0]               rf_waddr_wb_o,
  output logic [31:0]              rf_wdata_wb_o,
  output logic                     rf_we_wb_o,

  input logic                      lsu_resp_valid_i,
  input logic                      lsu_resp_err_i,

  output logic                     instr_done_wb_o
);

  import ibex_pkg::*;

  // 0 == RF write from ID
  // 1 == RF write from LSU
  logic [31:0] rf_wdata_wb_mux    [2];
  logic [1:0]  rf_wdata_wb_mux_we;

  if(WritebackStage) begin : g_writeback_stage
    logic [31:0]    rf_wdata_wb_q;
    logic           rf_we_wb_q;
    logic [4:0]     rf_waddr_wb_q;

    logic           wb_done;

    logic           wb_valid_q;
    logic [31:0]    wb_pc_q;
    logic           wb_compressed_q;
    logic           wb_count_q;
    wb_instr_type_e wb_instr_type_q;

    logic           wb_valid_d;

    // Stage becomes valid if an instruction enters for ID/EX and valid is cleared when instruction
    // is done
    assign wb_valid_d = (en_wb_i & ready_wb_o) | (wb_valid_q & ~wb_done);

    // Writeback for non load/store instructions always completes in a cycle (so instantly done)
    // Writeback for load/store must wait for response to be received by the LSU
    // Signal only relevant if wb_valid_q set
    assign wb_done = (wb_instr_type_q == WB_INSTR_OTHER) | lsu_resp_valid_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if(~rst_ni) begin
        wb_valid_q <= 1'b0;
      end else begin
        wb_valid_q <= wb_valid_d;
      end
    end

    if (ResetAll) begin : g_wb_regs_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_we_wb_q      <= '0;
          rf_waddr_wb_q   <= '0;
          rf_wdata_wb_q   <= '0;
          wb_instr_type_q <= wb_instr_type_e'(0);
          wb_pc_q         <= '0;
          wb_compressed_q <= '0;
          wb_count_q      <= '0;
        end else if (en_wb_i) begin
          rf_we_wb_q      <= rf_we_id_i;
          rf_waddr_wb_q   <= rf_waddr_id_i;
          rf_wdata_wb_q   <= rf_wdata_id_i;
          wb_instr_type_q <= instr_type_wb_i;
          wb_pc_q         <= pc_id_i;
          wb_compressed_q <= instr_is_compressed_id_i;
          wb_count_q      <= instr_perf_count_id_i;
        end
      end
    end else begin : g_wb_regs_nr
      always_ff @(posedge clk_i) begin
        if (en_wb_i) begin
          rf_we_wb_q      <= rf_we_id_i;
          rf_waddr_wb_q   <= rf_waddr_id_i;
          rf_wdata_wb_q   <= rf_wdata_id_i;
          wb_instr_type_q <= instr_type_wb_i;
          wb_pc_q         <= pc_id_i;
          wb_compressed_q <= instr_is_compressed_id_i;
          wb_count_q      <= instr_perf_count_id_i;
        end
      end
    end

    assign rf_waddr_wb_o         = rf_waddr_wb_q;
    assign rf_wdata_wb_mux[0]    = rf_wdata_wb_q;
    assign rf_wdata_wb_mux_we[0] = rf_we_wb_q & wb_valid_q;

    assign ready_wb_o = ~wb_valid_q | wb_done;

    // Instruction in writeback will be writing to register file if either rf_we is set or writeback
    // is awaiting load data. This is used for determining RF read hazards in ID/EX
    assign rf_write_wb_o = wb_valid_q & (rf_we_wb_q | (wb_instr_type_q == WB_INSTR_LOAD));

    assign outstanding_load_wb_o  = wb_valid_q & (wb_instr_type_q == WB_INSTR_LOAD);
    assign outstanding_store_wb_o = wb_valid_q & (wb_instr_type_q == WB_INSTR_STORE);

    assign pc_wb_o = wb_pc_q;

    assign instr_done_wb_o = wb_valid_q & wb_done;

    // Increment instruction retire counters for valid instructions which are not lsu errors
    assign perf_instr_ret_wb_o            = instr_done_wb_o & wb_count_q &
                                            ~(lsu_resp_valid_i & lsu_resp_err_i);
    assign perf_instr_ret_compressed_wb_o = perf_instr_ret_wb_o & wb_compressed_q;

    // Forward data that will be written to the RF back to ID to resolve data hazards. The flopped
    // rf_wdata_wb_q is used rather than rf_wdata_wb_o as the latter includes read data from memory
    // that returns too late to be used on the forwarding path.
    assign rf_wdata_fwd_wb_o = rf_wdata_wb_q;
  end else begin : g_bypass_wb
    // without writeback stage just pass through register write signals
    assign rf_waddr_wb_o         = rf_waddr_id_i;
    assign rf_wdata_wb_mux[0]    = rf_wdata_id_i;
    assign rf_wdata_wb_mux_we[0] = rf_we_id_i;

    // Increment instruction retire counters for valid instructions which are not lsu errors
    assign perf_instr_ret_wb_o            = instr_perf_count_id_i & en_wb_i &
                                            ~(lsu_resp_valid_i & lsu_resp_err_i);
    assign perf_instr_ret_compressed_wb_o = perf_instr_ret_wb_o & instr_is_compressed_id_i;

    // ready needs to be constant 1 without writeback stage (otherwise ID/EX stage will stall)
    assign ready_wb_o    = 1'b1;

    // Unused Writeback stage only IO & wiring
    // Assign inputs and internal wiring to unused signals to satisfy lint checks
    // Tie-off outputs to constant values
    logic           unused_clk;
    logic           unused_rst;
    wb_instr_type_e unused_instr_type_wb;
    logic [31:0]    unused_pc_id;

    assign unused_clk            = clk_i;
    assign unused_rst            = rst_ni;
    assign unused_instr_type_wb  = instr_type_wb_i;
    assign unused_pc_id          = pc_id_i;

    assign outstanding_load_wb_o  = 1'b0;
    assign outstanding_store_wb_o = 1'b0;
    assign pc_wb_o                = '0;
    assign rf_write_wb_o          = 1'b0;
    assign rf_wdata_fwd_wb_o      = 32'b0;
    assign instr_done_wb_o        = 1'b0;
  end

  assign rf_wdata_wb_mux[1]    = rf_wdata_lsu_i;
  assign rf_wdata_wb_mux_we[1] = rf_we_lsu_i;

  // RF write data can come from ID results (all RF writes that aren't because of loads will come
  // from here) or the LSU (RF writes for load data)
  assign rf_wdata_wb_o = ({32{rf_wdata_wb_mux_we[0]}} & rf_wdata_wb_mux[0]) |
                         ({32{rf_wdata_wb_mux_we[1]}} & rf_wdata_wb_mux[1]);
  assign rf_we_wb_o    = |rf_wdata_wb_mux_we;

  `DV_FCOV_SIGNAL_GEN_IF(logic, wb_valid, g_writeback_stage.wb_valid_q, WritebackStage)

  `ASSERT(RFWriteFromOneSourceOnly, $onehot0(rf_wdata_wb_mux_we))
endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abstract primitives wrapper.
//
// This file is a stop-gap until the DV file list is generated by FuseSoC.
// Its contents are taken from the file which would be generated by FuseSoC.
// https://github.com/lowRISC/ibex/issues/893

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_clock_gating (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

  if (Impl == prim_pkg::ImplGeneric) begin : gen_generic
    prim_generic_clock_gating u_impl_generic (
      .*
    );
  end else if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_clock_gating u_impl_xilinx (
      .*
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Common Library: Clock Gating cell
//
// The logic assumes that en_i is synchronized (so the instantiation site might need to put a
// synchronizer before en_i).

module prim_generic_clock_gating #(
  parameter bit NoFpgaGate = 1'b0 // this parameter has no function in generic
) (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);

  logic en_latch /* verilator clock_enable */;
  always_latch begin
    if (!clk_i) begin
      en_latch = en_i | test_en_i;
    end
  end
  assign clk_o = en_latch & clk_i;

endmodule
module IbexCoreBlackbox
	#(
		//parameters, currently just int (not bit)
		parameter PMP_GRANULARITY = 0,
		parameter PMP_NUM_REGIONS = 0,
		parameter MHPM_COUNTER_NUM = 0,
		parameter MHPM_COUNTER_WIDTH = 0,
		parameter RV32M = ibex_pkg::RV32MFast, //default 2
    	parameter RV32B = ibex_pkg::RV32BNone, //default 0
    	parameter REGFILE = ibex_pkg::RegFileFF, //default 0
		parameter DBG_HW_BREAK_NUM = 0,
		parameter [31:0] DM_HALT_ADDR = 0,
		parameter [31:0] DM_EXCEPTION_ADDR = 0
	) //TODO !!!!!!!!!!!
( 
	//inputs/outputs
	// Clock and Reset
    input clk_i,
    input rst_ni,

    input test_en_i,     // enable all clock gates for testing
    //input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

    //split up struct TODO: connect these somewhere?
    input ram_cfg_i_ram_cfg_en,
    input [3:0] ram_cfg_i_ram_cfg,
    input ram_cfg_i_rf_cfg_en,
    input [3:0] ram_cfg_i_rf_cfg,

    input [31:0] hart_id_i,
    input [31:0] boot_addr_i,

    // Instruction memory interface
    output instr_req_o,
    input  instr_gnt_i,
    input  instr_rvalid_i,
    output [31:0] instr_addr_o,
    input  [31:0] instr_rdata_i,
    input  instr_err_i,

    // Data memory interface
    output data_req_o,
    input  data_gnt_i,
    input  data_rvalid_i,
    output data_we_o,
    output [3:0] data_be_o,
    output [31:0] data_addr_o,
    output [31:0] data_wdata_o,
    input  [31:0] data_rdata_i,
    input  data_err_i,

    // Interrupt inputs
    input irq_software_i, //msip, software interrupt
    input irq_timer_i, //mtip
    input irq_external_i, //meip? external interrupt
    input [14:0] irq_fast_i, //fast local interrupts??
    input irq_nm_i,       //nmi non-maskeable interrupt

    // Debug Interface
    input debug_req_i, //debug
    //output ibex_pkg::crash_dump_t        crash_dump_o,

    //debugging output for ibex_lockstep.sv
    output [31:0] crash_dump_o_current_pc,
    output [31:0] crash_dump_o_next_pc,
    output [31:0] crash_dump_o_last_data_addr,
    output [31:0] crash_dump_o_exception_addr,

    // CPU Control Signals
    input fetch_enable_i,
    output alert_minor_o,
    output alert_major_o,
    output core_sleep_o,

    // DFT bypass controls
    input scan_rst_ni
);

	prim_ram_1p_pkg::ram_1p_cfg_t ibex_ram_config;
	ibex_pkg::crash_dump_t ibex_crash_dump;

	ibex_top #(
		.PMPEnable(1'b0),
	    .PMPGranularity(PMP_GRANULARITY),
	    .PMPNumRegions(PMP_NUM_REGIONS),
	    .MHPMCounterNum(MHPM_COUNTER_NUM),
	    .MHPMCounterWidth(MHPM_COUNTER_WIDTH),
	    .RV32E(1'b0),
	    .RV32M(RV32M),
	    .RV32B(RV32B),
	    .RegFile(REGFILE),
	    .BranchTargetALU(1'b0),
	    .WritebackStage(1'b0),
	    .ICache(1'b0),
	    .ICacheECC(1'b0),
	    .BranchPredictor(1'b0),
	    .DbgTriggerEn(1'b0),
	    .DbgHwBreakNum(DBG_HW_BREAK_NUM),
	    .SecureIbex(1'b0),
	    .DmHaltAddr(DM_HALT_ADDR),
	    .DmExceptionAddr(DM_EXCEPTION_ADDR)
	) i_ibex (
	    .clk_i,
	    .rst_ni,
	    .test_en_i,
	    .ram_cfg_i ( ibex_ram_config ), //CHECK
	    .hart_id_i,
	    .boot_addr_i,
		.instr_req_o,
	    .instr_gnt_i,
	    .instr_rvalid_i,
	    .instr_addr_o,
	    .instr_rdata_i,
	    .instr_err_i,
		.data_req_o,
	    .data_gnt_i,
	    .data_rvalid_i,
	    .data_we_o,
	    .data_be_o,
	    .data_addr_o,
	    .data_wdata_o,
	    .data_rdata_i,
	    .data_err_i,
		.irq_software_i,
	    .irq_timer_i,
	    .irq_external_i,
	    .irq_fast_i,
	    .irq_nm_i,
	    .debug_req_i,
	    .crash_dump_o ( ibex_crash_dump ),
	    .fetch_enable_i,
	    .alert_minor_o,
	    .alert_major_o,
	    .core_sleep_o,
	    .scan_rst_ni
	);

endmodule`undef WT_DCACHE
`undef DISABLE_TRACER
`undef SRAM_NO_INIT
`undef VERILATOR
