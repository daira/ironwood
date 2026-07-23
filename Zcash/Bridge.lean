-- The circuit–verifier bridge: modules importing both `Zcash.Circuits` and `Zcash.Snark`,
-- connecting the proved Action circuit semantics to the verifier soundness stack. The two
-- subtrees stay import-clean of each other; the cross-tree layer lives here.
--
-- * `ProjectionBridge` — the VK-match projection's semantics across the fixture/verifier
--   gate-`Expr` mirror: erasure and selector compression preserve evaluation.

import Zcash.Bridge.ProjectionBridge
