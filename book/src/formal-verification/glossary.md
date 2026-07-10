# Glossary

Coined terms and shorthand used across the [proof map](proof-map.md) and the Lean
soundness proofs. Anchors point to a module + name under `Zcash/Snark/`.

<style>
.iw-glossary { margin: 1.3rem 0; display: grid; gap: 26px; }
.iw-glossary section { display: grid; gap: 9px; }
.iw-glossary .grp {
  font-size: .8rem; font-weight: 700; text-transform: uppercase;
  letter-spacing: .11em; opacity: .55; margin: 0;
}
.iw-glossary .g {
  border: 1px solid var(--table-border-color, rgba(128,140,170,.28));
  border-left: 3px solid var(--links, #0e8fa3);
  border-radius: 8px; padding: 9px 13px;
  background: var(--quote-bg, rgba(128,140,170,.05));
}
.iw-glossary .g-head {
  display: flex; justify-content: space-between; align-items: baseline;
  gap: 6px 16px; flex-wrap: wrap;
}
.iw-glossary .term { font-weight: 650; }
.iw-glossary .term code { font-weight: 650; }
.iw-glossary .anchor {
  font-family: "SFMono-Regular", Consolas, "Liberation Mono", Menlo, monospace;
  font-size: .78em; opacity: .6; white-space: nowrap;
}
.iw-glossary .def { margin-top: 3px; line-height: 1.5; opacity: .9; }
</style>

<div class="iw-glossary">

<section>
<div class="grp">The fingerprint</div>
<div class="g"><div class="g-head"><span class="term">fingerprint</span><span class="anchor">Verifier.Assemble.assemble · Fingerprint.Match.MsmMatch</span></div><div class="def">The whole verifier collapsed into one multi-scalar multiplication; the proof accepts exactly when that MSM is the group identity. Checked equal to the Rust verifier's captured MSM — the map's <em>faithful to Rust</em> node.</div></div>
<div class="g"><div class="g-head"><span class="term">conditional vs deployed</span><span class="anchor">Main.DeployedAccepts</span></div><div class="def"><em>Conditional</em> capstones take an opaque <code>accepts : Prop</code> — a scaffold, not finished soundness; <em>deployed</em> capstones take the concrete accept (assembled MSM = identity).</div></div>
<div class="g"><div class="g-head"><span class="term">verifier equation</span><span class="anchor">Main.deployedAccepts_verifierEq</span></div><div class="def">halo2's explicit IPA verifier equation, recovered from the compact <code>MSM = 0</code> accept — the readable form the IPA argument consumes.</div></div>
</section>

<section>
<div class="grp">Fiat–Shamir &amp; rewinding</div>
<div class="g"><div class="g-head"><span class="term">forking lemma</span><span class="anchor">Forking.Probability.extractable_of_prob</span></div><div class="def">Rewinding the random oracle to get three accepting continuations per round at distinct challenges; assembled into the transcript tree the extractor consumes. Proven (an averaging argument) once the accept probability beats the knowledge error <code>kerr/Nᵏ</code>.</div></div>
<div class="g"><div class="g-head"><span class="term">rewind</span><span class="anchor">Forking.Rewind.roChallenges_reprogramRounds</span></div><div class="def">Re-running the schedule with the oracle reprogrammed at a round prefix: redrawing the IPA round vector is exactly reprogramming the deployed oracle (<code>roChallenges_reprogramRounds</code>) — the bridge from the forking measure to the deployed rewound runs, and the load-bearing consumer of <em>transcript ordering</em>. The <code>_rewind</code> capstones state the accept probability over these runs.</div></div>
<div class="g"><div class="g-head"><span class="term">transcript ordering</span><span class="anchor">Forking.Ordering</span></div><div class="def">Round-by-round soundness: each IPA round point sits in the transcript prefix before its challenge is drawn, so later messages cannot bend earlier challenges.</div></div>
</section>

<section>
<div class="grp">Peel &amp; IPA extraction</div>
<div class="g"><div class="g-head"><span class="term">U / W</span><span class="anchor">Deployed.Binding</span></div><div class="def">The auxiliary generators the deployed verifier folds into the MSM alongside the main <code>g</code> basis — the fold and blinding terms.</div></div>
<div class="g"><div class="g-head"><span class="term">peel</span><span class="anchor">Deployed.IpaPeel.deployed_to_acceptV</span></div><div class="def">Stripping the <code>U</code>/<code>W</code> terms off the deployed transcript tree to recover a clean, <code>g</code>-only IPA tree — or, failing that, a discrete-log relation.</div></div>
<div class="g"><div class="g-head"><span class="term">three-special-soundness</span><span class="anchor">Ipa.Soundness.ipa_soundV</span></div><div class="def">Extraction of the witness from three accepting transcripts at pairwise-distinct challenges per round.</div></div>
</section>

<section>
<div class="grp">Binding &amp; the AGM</div>
<div class="g"><div class="g-head"><span class="term">HasNontrivialRelation</span><span class="anchor">Deployed.Binding.HasNontrivialRelation</span></div><div class="def">A nontrivial discrete-log relation on <code>(g, U, W)</code>. One always exists at prime order, so the <code>∨</code>-branch is vacuous <em>as a statement</em>; the force is the computational assumption that no efficient adversary can <em>find</em> one.</div></div>
<div class="g"><div class="g-head"><span class="term">fixed-slot</span><span class="anchor">AGM.Adapter.FixedSlotEmbedding</span></div><div class="def">The AGM trick: hide a discrete-log challenge in one basis slot fixed before the adversary runs; a found relation hitting that slot yields the discrete log.</div></div>
<div class="g"><div class="g-head"><span class="term">DL reduction bound</span><span class="anchor">AGM.Probability.relation_prob_le_of_textbookDL</span></div><div class="def">The random-slot accounting: the planted slot is hit with probability at least <code>1/|basis|</code> of the finder's, so relation-finding probability is bounded by a multiple of the discrete-log advantage — where DL-hardness enters as an explicit, priced hypothesis.</div></div>
</section>

<section>
<div class="grp">Constraints &amp; multiopen</div>
<div class="g"><div class="g-head"><span class="term">circuit satisfaction</span><span class="anchor">KnowledgeSoundness.circuitSatViaGates</span></div><div class="def">The decoded columns satisfy the circuit gates — the constraint half of the SNARK relation, paired with the IPA opening.</div></div>
<div class="g"><div class="g-head"><span class="term">decoded columns</span><span class="anchor">Multiopen.Decode.decodedCols</span></div><div class="def">The individual column polynomials recovered from the batched multiopen witness by Vandermonde inversion of rewound openings.</div></div>
<div class="g"><div class="g-head"><span class="term">challenge batch (x₄) · challenge unbatch (x₁)</span><span class="anchor">Multiopen.Deployed.deployedCommitment_x4_batch · deployed_witness_member_binding</span></div><div class="def">The multiopen batching layers: <code>x₄</code> folds all opening claims into one by powers of the challenge; <code>x₁</code> bundles the commitments queried at each point set into an aggregate, which the unbatch opens back to the individual member commitments — pinning the extracted witness as the two-level power combination of their column witnesses.</div></div>
<div class="g"><div class="g-head"><span class="term">bad set</span><span class="anchor">Constraints.Vanishing.szBadSet · GoodChallenge</span></div><div class="def">The challenge values that fool the gate check — the roots of the constraint-difference polynomial; a uniform random-oracle challenge lands in it with probability ≤ <code>d/p</code> (Schwartz–Zippel). A challenge outside it is the map's <em>sound challenge</em>.</div></div>
</section>

<section>
<div class="grp">Capstones &amp; hypotheses</div>
<div class="g"><div class="g-head"><span class="term">capstones</span><span class="anchor">Soundness/Vesta.lean · GoodChallenge</span></div><div class="def">The top-level <code>orchard_verifier_vesta_*</code> theorems, forming a ladder of increasingly strong variants (conditional → reductions → forking → deployed / adaptive / rewind), each in an <code>opening</code> and a <code>constraint</code> form. The map's <em>verifier soundness</em> node is the base capstone. Two orthogonal wrappers sit on top: <code>_agm_dl</code> — the map's <em>AGM bridge</em> — routes the relation branch through the fixed-slot adapter to a discrete-log solution; <code>_xgood</code> derives <code>hgood</code> (the <em>sound challenge</em>) instead of assuming it.</div></div>
<div class="g"><div class="g-head"><span class="term">quotient check</span><span class="anchor">hquot · Soundness/Vesta.lean</span></div><div class="def">The verifier's gate/quotient point-check, plus carrying the gate challenge <code>x</code> over to the multiopen point <code>x₃</code>. Carried as the capstone hypothesis <code>hquot</code>; still open.</div></div>
<div class="g"><div class="g-head"><span class="term">sound challenge</span><span class="anchor">hgood · Soundness/Vesta.lean</span></div><div class="def">The challenge avoids the Schwartz–Zippel bad set, so the point-check at <code>x</code> implies the full gate identity. Carried as the capstone hypothesis <code>hgood</code>; discharged by the SZ territory's <code>_xgood</code> wrapper.</div></div>
<div class="g"><div class="g-head"><span class="term">accept probability</span><span class="anchor">hprob · Soundness/Vesta.lean</span></div><div class="def">The accepting-proof probability beats the knowledge error <code>kerr/Nᵏ</code> — enough for the forking lemma to extract. Carried as the capstone hypothesis <code>hprob</code>; the measure-side random-oracle floor.</div></div>
</section>

</div>
