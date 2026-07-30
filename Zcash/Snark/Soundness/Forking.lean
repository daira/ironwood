import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Assembly
import Zcash.Snark.Soundness.Forking.Ordering
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Forking.Adversary

/-!
# Fiat–Shamir random-oracle soundness

Reusable random-oracle lemmas, deployed transcript ordering, closed-form IPA assembly, and the
querying-adversary/forking reduction.
-/
