#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

static void pc (const vector<int> c) {
  for (unsigned i = 0; i < c.size(); i++)
    printf ("%d ", c[i]);
  printf ("\n");
}

static void pc (const BCheckerClause * c) {
  if (!c) {
    printf("0\n");
    return;
  }
  for (unsigned i = 0; i < c->size; i++)
    printf ("%d ", c->literals[i]);
  printf ("\n");
}

static void pc (const Clause * c) {
  if (!c) {
    printf("0\n");
    return;
  }
  for (int i = 0; i < c->size; i++)
    printf ("%d ", c->literals[i]);
  printf ("\n");
}

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i, bool core_units)
:
  internal (i), inconsistent (false),
  num_clauses (0), size_clauses (0), clauses (0),
  core_units (core_units), validating (0)
{
  LOG ("BCHECKER new");

  // Initialize random number table for hash function.
  //
  Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1)) nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));
}

BChecker::~BChecker () {
  LOG ("BCHECKER delete");
  for (size_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i], * next; c; c = next)
      next = c->next, delete_clause (c);
  delete [] clauses;
}

/*------------------------------------------------------------------------*/

uint64_t BChecker::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t)1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

uint64_t BChecker::compute_hash (const vector<int> & simplified) {
  ///TODO: Hash isn't order insinsetive. Since internal Clause objects
  //  are prone to reordering we must have an order insensitive hash computation.
  //  In the meantime, sort before computing the hash value.
  auto sorted (simplified); sort(sorted.begin (), sorted.end ());
  unsigned i = 0, j = 0;
  uint64_t hash = 0;
  for (i = 0; i < sorted.size (); i++) {
    int lit = sorted[i];
    hash += nonces[j++] * (uint64_t) lit;
    if (j == num_nonces) j = 0;
  }
  return hash;
}

void BChecker::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2*size_clauses : 1;
  LOG ("BCHECKER enlarging clauses of checker from %" PRIu64 " to %" PRIu64,
    (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  BCheckerClause ** new_clauses;
  new_clauses = new BCheckerClause * [ new_size_clauses ];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (BCheckerClause * c = clauses[i], * next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete [] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

BCheckerClause * BChecker::find (Clause * c) {
  stats.searches++;
  const auto size = c->size;
  vector<int> lits;
  unordered_set<int> marks;
  for (int i = 0; i < size; i++) {
    lits.push_back (c->literals[i]);
    marks.insert (lits[i]);
  }
  assert (marks.size () == size);
  const uint64_t hash = compute_hash (lits);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * res = 0;
  for (int i : cp_ordering[c]) {
    assert (i >= 0);
    assert (i < proof.size());
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    assert (!deleted);
    assert (hash == bc->hash);
    assert (!res || bc == res);
    assert (bc);
    res = bc;
  }
  return res;
}

BCheckerClause ** BChecker::find (const vector<int> & simplified) {
  stats.searches++;
  BCheckerClause ** res, * bc;
  const uint64_t hash = compute_hash (simplified);
  const unsigned size = simplified.size ();
  const uint64_t h = reduce_hash (hash, size_clauses);
  unordered_set<int> marks;
  for (unsigned i = 0; i < size; ++i)
    marks.insert (simplified[i]);
  // The only preprocessing we should do is to remove duplicates.
  assert (marks.size () == size);
  for (res = clauses + h; (bc = *res); res = &bc->next) {
    if (bc->hash == hash && bc->size == size) {
      bool found = true;
      const int * literals = bc->literals;
      for (unsigned i = 0; found && i != size; i++)
        found = marks.count(literals[i]);
      if (found) break;
    }
    stats.collisions++;
  }
  return res;
}

BCheckerClause * BChecker::new_clause (const vector<int> & simplified, const uint64_t hash) {
  const size_t size = simplified.size ();
  assert (0 < size && size <= UINT_MAX);
  const size_t surplus_bytes = size - 1;
  const size_t bytes = sizeof (BCheckerClause) + (surplus_bytes-1) * sizeof (int);
  BCheckerClause * res = (BCheckerClause *) new char [bytes];
  res->next = 0;
  res->hash = hash;
  res->size = size;
  res->original = false;
  int * literals = res->literals;
  int * p = literals;
  for (const auto & lit : simplified)
    *p++ = lit;

  num_clauses++;

  return res;
}

void BChecker::delete_clause (BCheckerClause * c) {
  assert (c->size > 0);
  assert (num_clauses);
  num_clauses--;
  delete [] (char*) c;
}

BCheckerClause * BChecker::insert (Clause * c) {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  vector<int> lits;
  for (int i = 0; i < c->size; i++)
    lits.push_back (c->literals[i]);
  uint64_t hash = compute_hash (lits);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * bc = new_clause (lits, hash);
  bc->next = clauses[h];
  bc->original = !c->redundant;
  clauses[h] = bc;
  return bc;
}

BCheckerClause * BChecker::insert (const vector<int> & simplified) {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  uint64_t hash = compute_hash (simplified);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * c = new_clause (simplified, hash);
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

bool BChecker::exists (const vector<int> & c) {
  return num_clauses && *find(c);
}

bool BChecker::exists (Clause * c) {
  return num_clauses && find(c);
}

static bool satisfied (Internal * internal, Clause * c) {
  for (int i = 0; i < c->size; i++)
    if (internal->val(c->literals[i]) > 0)
      return true;
  return false;
}

///TODO: Avoid unnecessary allocations and reuse valid garbage Clause references when possible.
void BChecker::revive_internal_clause (BCheckerClause * bc) {
  if (bc->size == 1) {
    int lit = bc->literals[0];
    Clause * c = internal->new_unit_clause (lit, !bc->original);
    assert (internal->val (lit) > 0);
    assert (internal->fixed (lit) > 0);
  } else {
    vector<int> & clause = internal->clause;
    assert (clause.empty());
    for (unsigned i = 0; i < bc->size; i++)
      clause.push_back (bc->literals[i]);
    Clause * c = internal->new_clause (!bc->original);
    clause.clear();
    if (satisfied (internal, c)) {
      for (int i = 0; i < c->size && internal->val(c->literals[1]); i++) {
        if (internal->val(c->literals[i]) >= 0) {
          int lit = c->literals[i];
          c->literals[i] = c->literals[1];
          c->literals[1] = lit;
        }
      }
    } else {
      ///TODO: Revisit this code block. The issue is that bc isn't maintaing the
      // correct order of counterpart literals.
      // for (int i = 0; i < c->size && internal->val(c->literals[0]); i++) {
      //   if (!internal->val(c->literals[i])) {
      //     int lit = c->literals[i];
      //     c->literals[i] = c->literals[0];
      //     c->literals[0] = lit;
      //   }
      // }
      for (int i = 1; i < c->size && internal->val(c->literals[1]) < 0; i++) {
        if (!internal->val(c->literals[i])) {
          int lit = c->literals[i];
          c->literals[i] = c->literals[1];
          c->literals[1] = lit;
        }
      }
      assert (internal->val (c->literals[0]) <= 0);
      assert (internal->val (c->literals[1]) <= 0);
    }
    internal->watch_clause (c);
  }
}

void BChecker::stagnate_internal_clause (const int i) {
  assert (proof.size() == counterparts.size());
  BCheckerClause * bc = proof[i].first;
  Clause * c = counterparts[i];
  if (c->size > 1)
    internal->unwatch_clause (c);
  internal->mark_garbage (c);
  ///TODO: Decide either to invalidate counterpart reference or
  // to cancel the garbage collection during validation. Might be
  // better to reuse the same reference if stil valid instead of
  // allocating a new one.
  assert (c->garbage);
  invalidate_counterpart (c);
}

void BChecker::shrink_internal_trail (const int trail_sz) {
  assert (trail_sz <= internal->trail.size());
  internal->trail.resize(trail_sz);
  internal->propagated = trail_sz;

  {
    // just to understand what is happening
    //
    assert (!internal->level);
    assert(internal->control.size () == 1);
  }
}

// The internal solver does not support reactivation of
// fixed literals. However, this is needed to be able to
// propagate these literals again.
void BChecker::reactivate_fixed (int l) {
  Flags & f = internal->flags (l);
  assert (f.status == Flags::FIXED);
  assert (internal->stats.now.fixed > 0);
  internal->stats.now.fixed--;
  f.status = Flags::ACTIVE;
  assert (internal->active (l));
  internal->stats.reactivated++;
  assert (internal->stats.inactive > 0);
  internal->stats.inactive--;
  internal->stats.active++;
}

void BChecker::undo_trail_literal (int lit) {
  assert (internal->val (lit) > 0);
  if (!internal->active (lit))
    reactivate_fixed (lit);
  internal->unassign (lit);
  assert (!internal->val (lit));
  assert (internal->active (lit));
  assert (internal->var(lit).reason);
  internal->var(lit).reason->reason = false;
  internal->var(lit).reason = 0;
}

void BChecker::undo_trail_core (Clause * c, unsigned & trail_sz) {
  LOG ("BCHECKER undoing trail core");
  assert (c && trail_sz > 0 && c->size > 0);
  assert (trail_sz <= internal->trail.size());
  assert (is_on_trail (c));
  int clit = c->literals[0];
  assert (internal->var (clit).reason == c);
  assert (internal->val (clit) > 0);

  while (internal->trail[trail_sz - 1] != clit)
  {
    assert(trail_sz > 1);

    int l = internal->trail[--trail_sz];

    Clause * r = internal->var(l).reason;
    assert (r);

    undo_trail_literal (l); // sets r->reason to false

    if (core_units) mark_core (r);

    if (r->core)
      for (int j = 1; j < r->size; j++)
      {
        Clause * reason = internal->var(r->literals[j]).reason;
        assert (reason);
        mark_core (reason);
      }
  }
  assert(clit == internal->trail[--trail_sz]);
  undo_trail_literal (clit);
}

bool BChecker::is_on_trail (Clause * c) {
  assert (internal->protected_reasons && !c->garbage);
  return c->reason;
}

void BChecker::mark_core (Clause * c) {
  assert (c);
  c->core = true;
}

void BChecker::conflict_analysis_core () {

  Clause * conflict = internal->conflict;
  assert(conflict);
  mark_core (conflict);

  ///TODO: Check this is correct even when chronological backtraking is on (internal->opts.chrono).
  // Need to check with https://cca.informatik.uni-freiburg.de/papers/MoehleBiere-SAT19.pdf


  ///NOTE: Checking the 'lit' is assigned might be redundant. But let us keep this
  // for now because unassigning a literal does not necessarily reset the trail value.
  auto got_value_by_propagation = [this](int lit) {
    bool assigned = internal->val (lit) != 0;
    int trail = internal->var (lit).trail;
    return assigned && trail > internal->control.back().trail && trail < internal->propagated;
  };

  for (int i = 0; i < conflict->size; i++)
  {
    int lit = conflict->literals[i];
    Var & v = internal->var(lit);
    assert (v.level > 0 || v.reason);
    if (got_value_by_propagation (lit) && !internal->marked (abs (lit)))
      internal->mark(abs(lit));
    else if (!v.level)
      mark_core (v.reason);
  }

  for (int i = internal->propagated-1; i > internal->control.back().trail; i--)
  {
    int lit = internal->trail[i];
    Var & v = internal->var(lit);
    if (!internal->marked(abs(lit)))
      continue;

    internal->unmark(abs(lit));

    Clause * c = v.reason;
    assert (c);

    mark_core (c);

    assert (internal->var(c->literals[0]).reason == c);
    assert (internal->val(c->literals[0]) > 0);

    for (int j = 1; j < c->size; j++)
    {
      int lit = c->literals[j];
      Var & y = internal->var(lit);
      assert(internal->val(lit) < 0);
      if (got_value_by_propagation (lit) && !internal->marked (abs(lit)))
        internal->mark (abs(lit));
      else if (!y.level)
        mark_core (y.reason);
    }
  }
}

static void dump_trail (Internal * internal, int verb = 0, int d = 0) {
  printf ("trail is partitioned into %d partitions: ", internal->control.size());
  for (int i = 0; i < internal->control.size(); i++)
    if (i == internal->control.size()-1)
      printf ("[%d-%d]\n", internal->control[i].trail, internal->trail.size()-1);
    else
      printf ("[%d-%d], ", internal->control[i].trail, internal->control[i+1].trail-1);
  if (verb > 0) {
    printf("last propagation has reasoned the following literals: ");
    for (int i = internal->control.back().trail + d; i < internal->propagated; i++) {
      printf ("%d ", internal->trail[i]);
      if (verb > 1) {
        Clause * r = internal->var (internal->trail[i]).reason;
        assert (r);
        printf ("from (");
        for (int m = 0; m < r->size; m++)
          printf (" %d", r->literals[m]);
        printf (") ");
      }
    }
    printf ("\n");
    printf("last propagation has reasoned the following conflict: "); pc (internal->conflict);
  }
}

bool BChecker::validate_lemma (Clause * lemma) {
  assert (validating);
  assert (!internal->level);
  assert (lemma && lemma->core);
  assert (internal->propagated == internal->trail.size ());

  vector <int> decisions;
  for (int i = 0; i < lemma->size; i++) {
    int lit = lemma->literals[i];
    if (!internal->val (lit))
      decisions.push_back (-lit);
  }

  assert (decisions.size());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level  == decisions.size());

  assert(!internal->conflict);
  if (internal->propagate ())
  {
    ///TODO: This might happen according to the Minisat patch.
    // -- If propagate fails, it may be due to incrementality and missing
    // -- units. Update qhead and re-propagate the entire trail
    // internal->propagated = 0;
    // if (internal->propagate ()) {
    //   internal->backtrack ();
       return false;
    // }
  }

  for (int i = 0; i < lemma->size; i++)
    if (!internal->var(lemma->literals[i]).level && internal->val(lemma->literals[i]))
      mark_core (internal->var(lemma->literals[i]).reason);

  conflict_analysis_core ();

  clear ();
  return true;
}

void BChecker::mark_core_trail_antecedents () {
  for (int lit : internal->trail) {
    Clause * reason = internal->var (lit).reason;
    assert (reason);
    if (reason->core) {
      assert (reason->literals[0] == lit);
      for (int j = 1; j < reason->size; j++)
        mark_core (internal->var (reason->literals[j]).reason);
      ///TODO: qhead = i;
    }
  }
}

void BChecker::put_units_back () {
  ///TODO: Needs to be implemented
}

void BChecker::check_data () {
  assert (proof.size() == counterparts.size());
  assert (proof.size() == stats.derived + stats.deleted);
  int deleted_lemmas = 0, valid_counterparts = 0;
  for (int i = 0; i < proof.size(); i++) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];
    assert (bc && (!deleted || !c));
    if (!deleted) {
      assert (c->size == 2 || !c->garbage);
      if (c->garbage) {
        invalidate_counterpart (c);
        deleted_lemmas++;
        continue;
      }
      auto & indexes = cp_ordering[c];
      assert (indexes.size() == 1);
      bool found = false;
      for (int j = 0; j < indexes.size() && !found; j++)
        found = indexes[j] == i;
      assert (found);
      valid_counterparts++;
    } else deleted_lemmas++;
  }
  assert (valid_counterparts + deleted_lemmas == proof.size());
}

void BChecker::clear () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

bool BChecker::validate () {
  assert (inconsistent);
  assert (proof.size ());
  assert (internal->unsat);

  START (bchecking);
  LOG ("BCHECKER starting validation");

  ///NOTE: The delay in notifying the proof with binary deleted clause
  // can lead to a situation where garbage binary clauses are lost
  // because they have not been deallocated yet at this point. However,
  // this is crucial for backward validation.

  validating = true;

  ///NOTE: Assert that conflicting assumptions and failing constraint
  // are being cached as learnt clauses if any (revisit src/assume.cpp).

  // 'protect_reasons' should protect fixed literal reasons as well.
  //
  ///TODO: Check which has more overhead:
  // 1- either protect all reasons once and check ->reason flag
  // 2- or use the Minisat way (Solver::locked ()).
  if (!internal->protected_reasons)
    internal->protect_reasons();
  internal->flush_all_occs_and_watches ();

  check_data ();

  Clause * last_conflict = internal->conflict;
  assert (last_conflict); // for workaround.
  mark_core (last_conflict);

  ///TODO: final conflict under assumptions
  // contains only one literal, mark all reasons.
  // Mark all conflict reasons as core
  for (int i = 0; i < last_conflict->size; i++) {
    assert (internal->val(last_conflict->literals[i]) < 0);
    Var & v = internal->var(last_conflict->literals[i]);
    Clause * reason = v.reason;
    if (reason) mark_core (reason);
  }

  clear ();

  unsigned trail_sz = internal->trail.size();

  for (int i = proof.size() - 1; i >= 0; i--) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];

    assert (bc && bc->size);
    assert (!deleted || !c);

    if (deleted) {
      revive_internal_clause (bc);
      continue;
    }

    assert (c && !c->garbage);

    if (is_on_trail (c)) {
      if (core_units) mark_core (c);
      undo_trail_core (c, trail_sz);
    }

    stagnate_internal_clause (i);

    if (c->core) {
      ///NOTE: If c->redundant is false, this does not mean the clause isn't a learnt (derived)
      //       clause. Irredundant does not necessarily mean learnt. For instance, a derived
      //       original clause is considered an irredundant leanrt clause.
      shrink_internal_trail (trail_sz);
      if (!validate_lemma (c)) goto exit;
    }
  }

  shrink_internal_trail (trail_sz);

  mark_core_trail_antecedents ();

  put_units_back ();

  internal->flush_all_occs_and_watches ();

  ///TODO: Clean up internal clauses that were created for validation purposes.

  printf ("Core lemmas are: \n");
  for (unsigned i = 0; i < internal->clauses.size (); i++) {
    if (internal->clauses[i]->garbage) continue;
    if (internal->clauses[i]->core)
      pc (internal->clauses[i]);
  }

  validating = false;

exit:
  STOP (bchecking);
  ///TODO: Find a less ugly way of doing this :)
  if (validating) return validating = false;
  else return true;
}

/*------------------------------------------------------------------------*/

void BChecker::invalidate_counterpart (Clause * c) {
  assert (c);
  assert (proof.size() == counterparts.size());
  vector<int> & indexes = cp_ordering[c];
  // I don't expect the internal solver to delete the same reference twice.
  assert (!validating || indexes.size() == 1);
  for (int i : indexes) {
    assert (i >= 0);
    assert (i < proof.size());
    assert (counterparts[i] == c);
    assert (proof[i].second == false);
    proof[i].second = true;
    counterparts[i] = 0;
  }
  indexes.clear ();
}

BCheckerClause * BChecker::get_bchecker_clause (const vector<int> & c) {
  BCheckerClause * bc = num_clauses > 0 ? *find(c) : 0;
  if (!bc) bc = insert (c);
  return bc;
}

BCheckerClause * BChecker::get_bchecker_clause (Clause * c) {
  BCheckerClause * bc = num_clauses > 0 ? find(c) : 0;
  if (!bc) bc = insert (c);
  return bc;
}

BCheckerClause * BChecker::get_bchecker_clause (int lit) {
  BCheckerClause * bc = num_clauses > 0 ? *find({lit}) : 0;
  if (!bc) bc = insert ({lit});
  return bc;
}

void BChecker::append_lemma (BCheckerClause * bc, Clause * c) {
  assert (bc);
  bool deleted = c == 0;
  if (deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    cp_ordering[c].push_back (proof.size());
    assert (cp_ordering[c].size() == 1);
  }
  proof.push_back ({bc, deleted});
  counterparts.push_back (c);
  assert (proof.size() == counterparts.size());
}

/*------------------------------------------------------------------------*/

void BChecker::add_derived_clause (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  BCheckerClause * bc = get_bchecker_clause (c);
  assert (bc);
  append_lemma (bc, c);
  STOP (bchecking);
}

void BChecker::add_derived_unit_clause (const int lit, bool original) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  assert (lit);
  assert (!original || !exists ({lit}));
  BCheckerClause * bc = get_bchecker_clause (lit);
  bc->original = original;
  Clause * r = internal->var(lit).reason;
  Clause * unit = 0;
  if (!r || r->size > 1)
    unit = internal->new_unit_clause (lit, true);
  else
    unit = r;
  if (!original) append_lemma (bc, unit);
  if (!r) internal->var(lit).reason = unit;
  assert (unit->size == 1 && unit->literals[0] == lit);
  assert (internal->var(lit).reason->literals[0] == lit);
  STOP (bchecking);
}

void BChecker::add_derived_empty_clause () {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  inconsistent = true;
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::strengthen_clause (Clause * c, int lit) {
  if (inconsistent) return;
  START (bchecking);
  assert (c && lit);
  LOG (c, "BCHECKER strengthen by removing %d in", lit);
  BCheckerClause * bc = get_bchecker_clause (c);
  vector<int> strengthened;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit != lit)
      strengthened.push_back (internal_lit);
  }
  BCheckerClause * strengthened_bc = get_bchecker_clause (strengthened);
  invalidate_counterpart (c);
  append_lemma (strengthened_bc, c);
  append_lemma (bc, 0);
  STOP (bchecking);
}

void BChecker::flush_clause (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER flushing falsified literals in");
  assert (c);
  BCheckerClause * bc = get_bchecker_clause (c);
  vector<int> flushed;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) >= 0)
      flushed.push_back (internal_lit);
  }
  assert (flushed.size() > 1);
  BCheckerClause * flushed_bc = get_bchecker_clause (flushed);
  invalidate_counterpart (c);
  append_lemma (flushed_bc, c);
  append_lemma (bc, 0);
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::delete_clause (const vector<int> & c, bool original) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  assert (!exists (c));
  BCheckerClause * bc = insert (c);
  bc->original = original;
  append_lemma (bc, 0);
  STOP (bchecking);
}

void BChecker::delete_clause (Clause * c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  BCheckerClause * bc = get_bchecker_clause (c);
  bc->original = !c->redundant;
  invalidate_counterpart (c);
  append_lemma (bc, 0);
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::update_moved_counterparts () {
  if (inconsistent) return;
  START (bchecking);
  assert (proof.size() == counterparts.size());
  ///TODO: consider maintaining a counterparts list to lessen the overhead here.
  for (int i = 0; i < proof.size(); i++) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];

    assert (!deleted || !c);

    if (deleted) continue;

    assert (c->size == 2 || !c->garbage || c->moved);

    if (c->moved) {
      assert (c->copy);
      /// TODO: proof isn't notified with deleted clauses
      //  of size 2 until they are actually deallocated.
      // Consider cancelling the delaying when bchecking.
      assert (c->size == 2 || !c->copy->garbage);
      assert (c != c->copy);
      auto & old_indexes = cp_ordering[c];
      auto & new_indexes = cp_ordering[c->copy];
      assert (old_indexes.size());
      assert (new_indexes.empty());
      for (int j : old_indexes)
        new_indexes.push_back (j);
      old_indexes.clear ();
      counterparts[i] = c->copy;
    }
    c = counterparts[i];
    assert (c->size == 2 || !c->garbage);
    if (c->garbage) {
      assert (c->size == 2);
      invalidate_counterpart (c);
      append_lemma (bc, 0);
      assert (!counterparts[i] && proof[i].second);
    } else {
      if (!(unsigned(counterparts[i]->size) == proof[i].first->size)) {
        pc (counterparts[i]);
        pc (proof[i].first);
      }
      assert (unsigned(counterparts[i]->size) == proof[i].first->size);
    }
  }
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::dump () {
  int max_var = 0;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i]; c; c = c->next)
      for (unsigned i = 0; i < c->size; i++)
        if (abs (c->literals[i]) > max_var)
          max_var = abs (c->literals[i]);
  printf ("p cnf %d %" PRIu64 "\n", max_var, num_clauses);
  for (uint64_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i]; c; c = c->next) {
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

}
