// Package supervised is the baseline against which the scoped design is
// measured. It answers the same question as the reducer, which steps a
// configuration permits, with the architecture a conventional system would
// use: a flat worker that proposes every step whose shape matches a rule, an
// independent supervisor that decides each proposal against a policy, and a
// hash-chained audit log that records every decision, refusals included.
//
// The worker reduces under reduce.Apply with a flat configuration, one that
// permits everything, so the only thing that can stop a step is the
// supervisor. The policy is a second implementation of the admissibility
// rules, written from the specification and sharing no code with the reducer.
// What is shared is reduce.Apply, which defines what a step does to a term;
// both designs rely on it, and the line counts in cmd/supexp make that
// explicit.
package supervised
