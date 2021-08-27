package ibex

import chisel3._
import chisel3.util._
import chisel3.experimental.{IntParam, StringParam, RawParam}

import scala.collection.mutable.{ListBuffer}

import freechips.rocketchip.config._
import freechips.rocketchip.subsystem._
import freechips.rocketchip.devices.tilelink._
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.diplomaticobjectmodel.logicaltree.{LogicalTreeNode}
import freechips.rocketchip.rocket._
import freechips.rocketchip.subsystem.{RocketCrossingParams}
import freechips.rocketchip.tilelink._
import freechips.rocketchip.interrupts._
import freechips.rocketchip.util._
import freechips.rocketchip.tile._
import freechips.rocketchip.amba.axi4._
import freechips.rocketchip.prci.ClockSinkParameters  

case class IbexCoreParams(
  val bootFreqHz: BigInt = BigInt(1700000000),              // Frequency
  val pmpGranularity: Int = 0,
  val pmpNumRegions: Int = 4,
  val rv32m: String = "ibex_pkg::RV32MFast",
  val rv32b: String = "ibex_pkg::RV32BNone",
  val regFile: String = "ibex_pkg::RegFileFF"
) extends CoreParams {
  val useVM: Boolean = false                  // Support virtual memory
  val useUser: Boolean = true                // Support user mode
  val useSupervisor: Boolean = false         // Support supervisor mode
  val useDebug: Boolean = true               // Support RISC-V debug specs
  val useAtomics: Boolean = false            // Support A extension
  val useAtomicsOnlyForIO: Boolean = false    // Support A extension for memory-mapped IO (may be true even if useAtomics is false)
  val useCompressed: Boolean = true         // Support C extension
  override val useVector: Boolean = false      // Support V extension
  val useSCIE: Boolean = false               // Support custom instructions (in custom-0 and custom-1)
  val useRVE: Boolean = true                // Use E base ISA
  val mulDiv: Option[MulDivParams] = Some(MulDivParams()) // copied from Rocket
  val fpu: Option[FPUParams] = None //NO FLOATING POINT          // F and D extensions and related setting (see below)
  val fetchWidth: Int = 1                // Max # of insts fetched every cycle
  val decodeWidth: Int = 1               // Max # of insts decoded every cycle
  val retireWidth: Int = 2               // Max # of insts retired every cycle
  val instBits: Int = if (useCompressed) 16 else 32                   // Instruction bits (if 32 bit and 64 bit are both supported, use 64)
  val nLocalInterrupts: Int = 15          // # of local interrupts (see SiFive interrupt cookbook)
  val nPMPs: Int = 0                     // # of Physical Memory Protection units
  val nBreakpoints: Int = 0              // # of hardware breakpoints supported (in RISC-V debug specs)
  val useBPWatch: Boolean = false            // Support hardware breakpoints
  val nPerfCounters: Int = 29             // # of supported performance counters
  val haveBasicCounters: Boolean = true     // Support basic counters defined in the RISC-V counter extension
  val haveFSDirty: Boolean = false           // If true, the core will set FS field in mstatus CSR to dirty when appropriate
  val misaWritable: Boolean = false          // Support writable misa CSR (like variable instruction bits)
  val haveCFlush: Boolean = false            // Rocket specific: enables Rocket's custom instruction extension to flush the cache
  val nL2TLBEntries: Int = 512 //??             // # of L2 TLB entries
  val mtvecInit: Option[BigInt] = Some(BigInt(0))       // mtvec CSR (of V extension) initial value
  val mtvecWritable: Boolean = true          // If mtvec CSR is writable
  val nL2TLBWays: Int = 1
  val lrscCycles: Int = 80 // copied from Rocket
  val mcontextWidth: Int = 0 // TODO: Check
  val scontextWidth: Int = 0 // TODO: Check
  val useNMI: Boolean = true
}

case class IbexTileAttachParams(
  tileParams: IbexTileParams,
  crossingParams: RocketCrossingParams
) extends CanAttachTile {
  type TileType = IbexTile
  val lookup = PriorityMuxHartIdFromSeq(Seq(tileParams))
}

case class IbexTileParams(
  name: Option[String] = Some("ibex_tile"),
  hartId: Int = 0,
  val core: IbexCoreParams = IbexCoreParams()
) extends InstantiableTileParams[IbexTile]
{
  val beuAddr: Option[BigInt] = None
  val blockerCtrlAddr: Option[BigInt] = None
  val btb: Option[BTBParams] = None
  val boundaryBuffers: Boolean = false
  val dcache: Option[DCacheParams] = None //no dcache
  val icache: Option[ICacheParams] = None //optional icache, currently in draft so turning option off
  val clockSinkParams: ClockSinkParameters = ClockSinkParameters()
  def instantiate(crossing: TileCrossingParamsLike, lookup: LookupByHartIdImpl)(implicit p: Parameters): IbexTile = {
    new IbexTile(this, crossing, lookup)
  }
}

class IbexTile private(
  val ibexParams: IbexTileParams,
  crossing: ClockCrossingType,
  lookup: LookupByHartIdImpl,
  q: Parameters)
  extends BaseTile(ibexParams, crossing, lookup, q)
  with SinksExternalInterrupts
  with SourcesExternalNotifications
{

  def this(params: IbexTileParams, crossing: TileCrossingParamsLike, lookup: LookupByHartIdImpl)(implicit p: Parameters) =
    this(params, crossing.crossingType, lookup, p)

  //TileLink nodes
  val intOutwardNode = IntIdentityNode()
  val masterNode = visibilityNode
  val slaveNode = TLIdentityNode()

  tlOtherMastersNode := tlMasterXbar.node
  masterNode :=* tlOtherMastersNode
  DisableMonitors { implicit p => tlSlaveXbar.node :*= slaveNode }

  override lazy val module = new IbexTileModuleImp(this)

  val portName = "ibex-mem-port"
  val node = TLIdentityNode()

  //check how many inflight requests supported at once
  //TEMP: borrowed from sodor
  val dmemNode = TLClientNode(
    Seq(TLMasterPortParameters.v1(
      clients = Seq(TLMasterParameters.v1(
        name = portName,
        sourceId = IdRange(0, 1))))))

  val imemNode = TLClientNode(
    Seq(TLMasterPortParameters.v1(
      clients = Seq(TLMasterParameters.v1(
        name = portName,
        sourceId = IdRange(0, 1))))))

  tlMasterXbar.node := node := TLBuffer() := dmemNode
  tlMasterXbar.node := node := TLBuffer() := imemNode

  // Required entry of CPU device in the device tree for interrupt purpose
  val cpuDevice: SimpleDevice = new SimpleDevice("cpu", Seq("lowRISC,ibex", "riscv")) {
    override def parent = Some(ResourceAnchors.cpus)
    override def describe(resources: ResourceBindings): Description = {
      val Description(name, mapping) = super.describe(resources)
      Description(name, mapping ++
                        cpuProperties ++
                        nextLevelCacheProperty ++
                        tileProperties)
    }
  }

  ResourceBinding {
    Resource(cpuDevice, "reg").bind(ResourceAddress(hartId))
  } //check resource address

  def connectIbexInterrupts(debug: Bool, msip: Bool, mtip: Bool, meip: Bool, lip: UInt) {
    val (interrupts, _) = intSinkNode.in(0)
    debug := interrupts(0)
    mtip := interrupts(2) //mtip
    msip := interrupts(1) //msip
    meip := interrupts(3) //meip
    //lip := interrupts(5) //lip
  }

}



class IbexTileModuleImp(outer: IbexTile) extends BaseTileModuleImp(outer){
  // annotate the parameters
  Annotated.params(this, outer.ibexParams)

  val debugHwBreakNum = 1
  val dmHaltAddress = 0x1A110800
  val dmExceptionAddress = 0x1A110808
  val mhpmCounterNumber = 0
  val mhmpCounterWid = 40

  val core = Module(new IbexCoreBlackbox(
    pmpGranularity = outer.ibexParams.core.pmpGranularity,
    pmpNumRegions = outer.ibexParams.core.pmpNumRegions,
    mhpmCounterNum = mhpmCounterNumber,
    mhpmCounterWidth = mhmpCounterWid,
    rv32m = outer.ibexParams.core.rv32m,
    rv32b = outer.ibexParams.core.rv32b,
    regfile = outer.ibexParams.core.regFile,
    dbgHwBreakNum = debugHwBreakNum,
    dmHaltAddr = dmHaltAddress,
    dmExceptionAddr = dmExceptionAddress
  ))

  //connect signals
  core.io.clk_i := clock
  core.io.rst_ni := ~reset.asBool
  core.io.boot_addr_i := outer.resetVectorSinkNode.bundle
  core.io.hart_id_i := outer.hartIdSinkNode.bundle

  /*val int_bundle = new TileInterrupts()
  outer.decodeCoreInterrupts(int_bundle)
  val lip = Wire(UInt())
  lip := int_bundle.lip.asUInt
  core.io.debug_req_i := Wire(int_bundle.debug)
  core.io.irq_timer_i := Wire(int_bundle.mtip)
  core.io.irq_software_i := Wire(int_bundle.msip)
  core.io.irq_external_i := Wire(int_bundle.meip)
  core.io.irq_fast_i := lip*/ //type mismatch, uint vs bool
  //core.io.irq_nm_i := int_bundle.nmi.rnmi //recoverable nmi

  outer.connectIbexInterrupts(core.io.debug_req_i, core.io.irq_software_i, core.io.irq_timer_i, core.io.irq_external_i, core.io.irq_fast_i)
  //core.io.irq_nm_i := int_bundle.nmi.rnmi //recoverable nmi



  // MEMORY
  // dmem
  val (dmem, dmem_edge) = outer.dmemNode.out(0)

  val s_ready :: s_active :: s_inflight :: Nil = Enum(3)
  val dmem_state = RegInit(s_ready)

  val dmem_addr = Reg(UInt(32.W)) //32 bit addr
  val dmem_data = Reg(UInt(64.W))
  val dmem_mask = Reg(UInt(8.W))
  //val dmem_w_mask = Reg(UInt(8.W))
  val byte_en = Reg(UInt(4.W))
  val num_bytes = Reg(UInt(3.W))
  val r_size = Reg(UInt(2.W))
  val w_size = Reg(UInt(2.W))
  val not_dw_aligned = Reg(Bool())
  r_size := 2.U //2^2 = 4 bytes

  /*ISA expects LSByte of write data to be written. TL mask is which byte of write data to write.
    dmem_mask should always be f, 3, or 1 (with appropriate word alignment). Use data_be_o to adjust address.
  */

  when (dmem_state === s_ready && core.io.data_req_o) {
    dmem_state := s_active
    dmem_addr := core.io.data_addr_o + (PriorityEncoder(core.io.data_be_o) * core.io.data_we_o)
    dmem_data := core.io.data_wdata_o << (32.U * ((core.io.data_addr_o & 4.U) === 4.U))
    byte_en := core.io.data_be_o

    /*when (PopCount(core.io.data_be_o) === 1.U) {
      dmem_mask := 1.U << (4.U * ((core.io.data_addr_o & 4.U) === 4.U))
    } .elsewhen (PopCount(core.io.data_be_o) === 2.U) {
      dmem_mask := 3.U << (4.U * ((core.io.data_addr_o & 4.U) === 4.U))
    } .otherwise {
      dmem_mask := core.io.data_be_o << (4.U * ((core.io.data_addr_o & 4.U) === 4.U))
    }*/

    dmem_mask := core.io.data_be_o << (4.U * ((core.io.data_addr_o & 4.U) === 4.U))

    //num_bytes := PopCount(byte_en)
    w_size := PriorityEncoder(PopCount(core.io.data_be_o)) //log2Ceil
    not_dw_aligned := ((core.io.data_addr_o & 4.U) === 4.U)
  }
  when (dmem_state === s_active && dmem.a.fire()) {
    dmem_state := s_inflight
  }
  when (dmem_state === s_inflight && dmem.d.fire()) {
    dmem_state := s_ready
  }
  dmem.a.valid := dmem_state === s_active
  core.io.data_gnt_i := dmem_state === s_ready && core.io.data_req_o // check, data_gnt is expected to be high for only 1 cycle at a time
  dmem.d.ready := true.B
  core.io.data_rvalid_i := dmem.d.valid //check, data_rvalid can only be high for 1 cycle (appears to align w tilelink spec)

  //val mask = FillInterleaved(8, dmem_mask) //expand mask to 32 bits
  //printf("write mask = %b\n", byte_en)
  //printf("dmem_mask = %b\n", dmem_mask)
  //printf(p"num_bytes = ${num_bytes}\n")
  //printf(p"w_size = ${w_size}\n")

  //seperate write addr/mask and read addr/mask???

  val dmem_get = dmem_edge.Get(0.U, dmem_addr, r_size)._2
  val dmem_put = dmem_edge.Put(0.U, dmem_addr, w_size, dmem_data, dmem_mask)._2

  dmem.a.bits := Mux(core.io.data_we_o, dmem_put, dmem_get)             //write or read depending on write enable
  core.io.data_rdata_i := dmem.d.bits.data >> (32.U * not_dw_aligned)   //read data
  core.io.data_err_i := dmem.d.bits.corrupt | dmem.d.bits.denied        //set error

  //unused
  dmem.b.valid := false.B
  dmem.c.ready := true.B
  dmem.e.ready := true.B


  //imem
  val (imem, imem_edge) = outer.imemNode.out(0)
  val imem_state = RegInit(s_ready)

  val imem_addr = Reg(UInt(32.W)) //32 bit addr
  val r_lower = Reg(UInt(32.W))
  //val r_upper = Reg(UInt(32.W))
  val r_word_sel = Reg(Bool()) // 1 for upper half of doubleword, 0 for lower half

  when (imem_state === s_ready && core.io.instr_req_o) {
    imem_state := s_active
    imem_addr := core.io.instr_addr_o
    r_word_sel := ((core.io.instr_addr_o & 4.U) === 4.U)
  }
  when (imem_state === s_active && imem.a.fire()) {
    imem_state := s_inflight
  }
  when (imem_state === s_inflight && imem.d.fire()) {
    imem_state := s_ready
  }

  imem.a.valid := imem_state === s_active
  core.io.instr_gnt_i := imem_state === s_ready // check
  imem.d.ready := true.B
  core.io.instr_rvalid_i := imem.d.valid //check

  val imem_get = imem_edge.Get(0.U, imem_addr, r_size)._2

  imem.a.bits := imem_get
  //r_upper := imem.d.bits.data >> 32
  //r_lower := imem.d.bits.data
  core.io.instr_rdata_i := imem.d.bits.data >> (32.U * r_word_sel)
  //Mux(r_word_sel, r_upper, r_lower) // 1 cycle delay
  //core.io.instr_rdata_i := imem.d.bits.data //d channel returns 64 bits of data
  // tl reads from doubleword aligned addr, must pick which half to read depending on instr_addr
  // ibex addr is word aligned
  core.io.instr_err_i := imem.d.bits.corrupt | imem.d.bits.denied

  //unused
  imem.b.valid := false.B
  imem.c.ready := true.B
  imem.e.ready := true.B

  //used for icache, tie off
  core.io.ram_cfg_i_ram_cfg_en := 0.U
  core.io.ram_cfg_i_ram_cfg := 0.U
  core.io.ram_cfg_i_rf_cfg_en := 0.U
  core.io.ram_cfg_i_rf_cfg := 0.U

  //continuously fetch instructions
  core.io.fetch_enable_i := 1.U

  //DFT not used
  core.io.scan_rst_ni := 1.U
}




