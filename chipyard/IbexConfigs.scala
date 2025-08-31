package chipyard

import chisel3._

import org.chipsalliance.cde.config.Config

// Ibex Configs moved under the ibex generator for modularity

class IbexConfig extends Config(
  new ibex.WithNIbexCores(1) ++
  new chipyard.config.WithInclusiveCacheWriteBytes(4) ++
  new chipyard.config.AbstractConfig)

