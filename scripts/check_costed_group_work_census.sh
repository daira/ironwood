#!/usr/bin/env bash
# Pin the repository-owned host-language surface of the staged Vesta work model.
#
# `CostedVestaComp.pure` and `CostedVestaComp.map` deliberately charge zero group work.  They are
# sound only when their payload construction / callback performs no Vesta group law: already
# charged points may be packaged, projected, compared, or transported, but new additions, scalar
# multiplications, negations, and MSM evaluations must use the reified constructors.
#
# This check makes that manual audit reviewable in two ways:
#
# 1. only the two censused production modules may mention the costed computation types; and
# 2. every definition in `AdaptiveStatementCost.lean` that uses a host-language payload or callback
#    through `pure`, `map`, `bind`, or `query` is pinned below, together with its direct
#    scalar-multiplication, addition/negation, `.sum`, and `.eval` source footprint.
#
# Any new producer, host callback, or direct raw group expression fails CI until this census
# is deliberately reviewed and updated.  This is an accidental-drift guard, not a semantic proof:
# an indirect helper or caller-supplied adversary can still hide group work.  That irreducible
# shallow-language boundary remains the explicit `StagedGroupWorkFaithful` premise.
set -euo pipefail
cd "$(dirname "$0")/.."

expected_modules=$(printf '%s\n' \
  Zcash/Snark/Soundness/AGM/CostedOracle.lean \
  Zcash/Snark/Soundness/Action/AdaptiveStatementCost.lean)

actual_modules=$(find Zcash/Snark/Soundness -name '*.lean' -print0 \
  | xargs -0 grep -lE 'Costed(Vesta|LabeledOracle)Comp' \
  | sort)

status=0
if [[ "$actual_modules" != "$expected_modules" ]]; then
  echo "VIOLATION: the production costed-computation module census changed" >&2
  diff -u <(printf '%s\n' "$expected_modules") <(printf '%s\n' "$actual_modules") >&2 || true
  status=1
fi

# Scan top-level definitions only. A declaration body ends when the next non-indented command or
# documentation block begins. The counters pin direct source notation inside the whole declaration
# (including dependent result specifications); pinning the current nonzero specification-only
# footprint still makes any newly written direct expression review-visible.
actual_callbacks=$(awk '
function flush() {
  if (in_def && uses_host) {
    print current "|smul=" smul "|add=" add "|neg=" neg "|sum=" sum "|eval=" eval
  }
}
function start_def(line, name) {
  sub(/^private[[:space:]]+/, "", line)
  sub(/^noncomputable[[:space:]]+/, "", line)
  sub(/^def[[:space:]]+/, "", line)
  name = line
  sub(/[[:space:]({:].*$/, "", name)
  current = name
  in_def = 1
  uses_host = 0
  smul = 0
  add = 0
  neg = 0
  sum = 0
  eval = 0
}
/^(private[[:space:]]+)?(noncomputable[[:space:]]+)?def[[:space:]]+/ {
  flush()
  start_def($0)
  next
}
in_def && /^[^[:space:]]/ {
  flush()
  in_def = 0
  current = ""
}
in_def {
  line = $0
  if (line ~ /Costed(Vesta|LabeledOracle)Comp\.(pure|map|bind|query)/) uses_host = 1
  while (sub(/•/, "", line)) smul++
  line = $0
  while (sub(/ \+ /, "", line)) add++
  line = $0
  while (sub(/-/, "", line)) neg++
  line = $0
  while (sub(/\.sum/, "", line)) sum++
  line = $0
  while (sub(/\.eval/, "", line)) eval++
}
END { flush() }
' Zcash/Snark/Soundness/Action/AdaptiveStatementCost.lean | sort)

expected_callbacks=$(printf '%s\n' \
  'adaptiveStatementExtractorReductionProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'adaptiveStatementFinderAfterProvenanceProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'adaptiveStatementFinderReductionProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedKnowledgeExtractorReductionProgramAtReifiedBasisFromCache|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedKnowledgeExtractorReductionProgramAtReifiedBasis|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedKnowledgeExtractorReductionProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedRelationFinderReductionProgramAtReifiedBasisFromCache|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedRelationFinderReductionProgramAtReifiedBasis|smul=0|add=0|neg=0|sum=0|eval=0' \
  'cachedRelationFinderReductionProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'certifiedCachedRunProgram|smul=0|add=0|neg=0|sum=0|eval=0' \
  'certifiedKnowledgeExtractorExecutionContinuation|smul=0|add=0|neg=0|sum=0|eval=0' \
  'certifiedKnowledgeExtractorExecutionProgramWithBasis|smul=0|add=0|neg=0|sum=0|eval=0' \
  'certifiedRelationFinderExecutionContinuation|smul=0|add=0|neg=0|sum=0|eval=0' \
  'certifiedRelationFinderExecutionProgramWithBasis|smul=0|add=0|neg=0|sum=0|eval=0' \
  'costedAcceptsVCertified|smul=0|add=0|neg=0|sum=0|eval=1' \
  'costedAcceptsV|smul=0|add=0|neg=0|sum=0|eval=0' \
  'costedAdaptiveStatementBasisCache|smul=1|add=0|neg=0|sum=1|eval=1' \
  'costedAdaptiveStatementCanonicalInstanceCache|smul=0|add=0|neg=0|sum=0|eval=1' \
  'programmedCachedKnowledgeExtractorReductionProgram|smul=4|add=2|neg=0|sum=0|eval=0' \
  'programmedCachedRelationFinderReductionProgram|smul=4|add=2|neg=0|sum=0|eval=0')

if [[ "$actual_callbacks" != "$expected_callbacks" ]]; then
  echo "VIOLATION: the audited staged host-callback census changed" >&2
  diff -u <(printf '%s\n' "$expected_callbacks") <(printf '%s\n' "$actual_callbacks") >&2 || true
  status=1
fi

if [[ $status -eq 0 ]]; then
  echo "costed group-work census: 2 production modules, 20 host-callback definitions pinned."
fi
exit $status
