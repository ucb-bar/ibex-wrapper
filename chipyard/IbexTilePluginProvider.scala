package chipyard.config

import ibex.IbexTileAttachParams
import freechips.rocketchip.subsystem.HierarchicalElementPortParamsLike

class IbexTilePluginProvider extends TilePluginProvider {
  // Ibex tile params do not define generic trace toggles in Chipyard; no-op for trace injectors.

  override def tilePrefetchInjectors(make: (Int, HierarchicalElementPortParamsLike) => HierarchicalElementPortParamsLike) = Seq({
    case tp: IbexTileAttachParams => tp.copy(crossingParams = tp.crossingParams.copy(
      master = make(tp.tileParams.tileId, tp.crossingParams.master)))
  })
}

