#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i, bool core_units)
:
  internal (i), num_clauses (0), size_clauses (0), clauses (0),
  core_units (core_units), dying (0), validating (0)
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
  dying = true; // hack to cancel delete notifications;
  for (size_t i = 0; i < size_clauses; i++)
    for (BCheckerClause * c = clauses[i], * next; c; c = next)
      next = c->next, delete_clause (c);
  delete [] clauses;
  ///TODO: deallocate all unit clauses.
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

uint64_t BChecker::compute_hash (const vector<int> & lits) {
  ///NOTE: Hash isn't order insinsetive. Since internal Clause objects
  // are prone to reordering we must have an order insensitive hash computation.
  // In the meantime, sort before computing the hash value.
  auto sorted (lits); sort(sorted.begin (), sorted.end ());
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
  LOG ("BCHECKER enlarging clauses of bchecker from %" PRIu64 " to %" PRIu64,
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

BCheckerClause * BChecker::new_clause (const vector<int> & lits, const uint64_t hash) {
  const size_t size = lits.size ();
  assert (0 < size && size <= UINT_MAX);
  const size_t surplus_bytes = size - 1;
  const size_t bytes = sizeof (BCheckerClause) + (surplus_bytes-1) * sizeof (int);
  BCheckerClause * res = (BCheckerClause *) new char [bytes];
  res->next = 0;
  res->hash = hash;
  res->size = size;
  res->marked_garbage = false;
  int * literals = res->literals;
  int * p = literals;
  for (const auto & lit : lits)
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
  vector<int> lits;
  for (int i = 0; i < c->size; i++)
    lits.push_back (c->literals[i]);
  return insert (lits);
}

BCheckerClause * BChecker::insert (const vector<int> & lits) {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  uint64_t hash = compute_hash (lits);
  const uint64_t h = reduce_hash (hash, size_clauses);
  BCheckerClause * bc = new_clause (lits, hash);
  bc->next = clauses[h];
  clauses[h] = bc;
  return bc;
}

void BChecker::revive_internal_clause (int i) {
  assert (!counterparts[i] && proof[i].second);
  BCheckerClause * bc = proof[i].first;
  assert (bc->size > 1);
  ///NOTE: Unit clauses should not be deleted.
  // The motivation behind allocating unit clauses is to simplify the code.
  ///TODO: bchecker is responsible for deleting (deallocating) these clauses.
  vector<int> & clause = internal->clause;
  assert (clause.empty());
  for (unsigned j = 0; j < bc->size; j++)
    clause.push_back (bc->literals[j]);
  Clause * c = internal->new_clause (true /* if it was deleted before, this means it's redundant */);
  clause.clear();
  internal->watch_clause (c);
  assert (c && (revive_ordering[i].empty () || revive_ordering[i].size() == 1));
  for (int j : revive_ordering[i]) {
    assert (revive_ordering[j].empty ()); // Are chains even possible?
    assert (!proof[j].second && !counterparts[j]);
    counterparts[j] = c;
  }
  counterparts[i] = c;
}

void BChecker::stagnate_internal_clause (const int i) {
  assert (proof.size() == counterparts.size());
  Clause * c = counterparts[i];
  // counterparts[i] = 0; // for incremental
  if (c->size == 1) return;
  internal->unwatch_clause (c);
  if (!c->garbage) {
    ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->moved);
    c->garbage = true;
    proof[i].first->marked_garbage = true;
  }
    // internal->mark_garbage (c);
  // assert (proof.size() == counterparts.size());
  // Clause * c = counterparts[i];
  // counterparts[i] = 0; // for incremental
  // if (c->size == 1) return;
  // internal->unwatch_clause (c);
  // if (!c->garbage) {
  //   ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
  //   // clauses as deleted (produce 'd ...' lines) as soon they are marked
  //   // garbage.
  //   assert (!c->moved);
  //   internal->mark_garbage (c);
  // }
}

void BChecker::shrink_internal_trail (const unsigned trail_sz) {
  assert (trail_sz <= internal->trail.size());
  internal->trail.resize(trail_sz);
  internal->propagated = trail_sz;
  ///TODO: set internal->propagated2 properly.
  assert (!internal->level);
  assert(internal->control.size () == 1);
}

///NOTE: The internal solver does not support reactivation
// of fixed literals. However, this is needed to be able
// to propagate these literals again.
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
  Var & v = internal->var (lit);
  assert (v.reason);
}

void BChecker::undo_trail_core (Clause * c, unsigned & trail_sz) {

#ifndef NDEBUG
  assert (trail_sz > 0 && trail_sz <= internal->trail.size());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (internal->var (clit).reason == c);
  assert (internal->val (clit) > 0);
#endif

  while (internal->trail[trail_sz - 1] != clit)
  {
    assert(trail_sz > 1);
    int l = internal->trail[--trail_sz];

    Clause * r = internal->var(l).reason;
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (core_units) mark_core (r);

    if (r->core)
      for (int j = 1; j < r->size; j++)
        mark_core (internal->var(r->literals[j]).reason);
  }

  assert(clit == internal->trail[--trail_sz]);
  undo_trail_literal (clit);
}

bool BChecker::is_on_trail (Clause * c) {
  assert (c);
  int lit = c->literals[0];
  return internal->val (lit) > 0 && internal->var (lit).reason == c;
}

void BChecker::mark_core (Clause * c) {
  assert (c);
  c->core = true;
}

void BChecker::mark_last_conflict (bool overconstrained) {
  if (internal->unsat) {
    Clause * last_conflict = internal->conflict;
    assert (!overconstrained && "handle the case where the problem is oevrconstrained");
    mark_core (last_conflict);
    for (int i = 0; i < last_conflict->size; i++) {
      assert (internal->val(last_conflict->literals[i]) < 0);
      Var & v = internal->var(last_conflict->literals[i]);
      Clause * reason = v.reason;
      if (reason) mark_core (reason);
    }
  } else assert (failing_assumptions.size () && internal->marked_failed);
}

void BChecker::conflict_analysis_core () {

  Clause * conflict = internal->conflict;
  assert(conflict);
  mark_core (conflict);

  ///TODO: Check this is correct even when chronological backtraking is on (internal->opts.chrono).
  // Need to check with https://cca.informatik.uni-freiburg.de/papers/MoehleBiere-SAT19.pdf

  auto got_value_by_propagation = [this](int lit) {
    assert (internal->val (lit) != 0);
#ifndef NDEBUG
    int trail = internal->var (lit).trail;
    assert (trail >= 0 && trail < int (internal->trail.size()));
    assert (internal->trail[trail] == -lit);
#endif
    return internal->var (lit).trail > internal->control.back().trail;
  };

  ///TODO: Use internal->mark|ed () instead.
  unordered_set<int> seen;

  for (int i = 0; i < conflict->size; i++)
  {
    int lit = conflict->literals[i];
    Var & v = internal->var(lit);
    assert (v.level > 0 || v.reason);
    if (got_value_by_propagation (lit))
      seen.insert (abs(lit));
    else if (!v.level)
      mark_core (v.reason);
  }

  for (int i = internal->trail.size()-1; i > internal->control.back().trail; i--)
  {
    int lit = internal->trail[i];
    Var & v = internal->var(lit);
    if (!seen.count (abs(lit)))
      continue;

    seen.erase (abs(lit));

    Clause * c = v.reason;

    mark_core (c);

    assert (internal->var(c->literals[0]).reason == c);
    assert (internal->val(c->literals[0]) > 0);
    assert (c->literals[0] == lit);

    for (int j = 1; j < c->size; j++)
    {
      int lit = c->literals[j];
      Var & v = internal->var(lit);
      assert(internal->val(lit) < 0);
      if (got_value_by_propagation (lit))
        seen.insert (abs(lit));
      else if (!v.level) {
        mark_core (v.reason);
      }
    }
  }
  assert (seen.empty ());
}

bool BChecker::validate_lemma (Clause * lemma) {
  assert (validating);
  assert (!internal->level);
  assert (lemma && lemma->core);
  assert (internal->propagated == internal->trail.size ());

  // printf ("validating: "); for (int i = 0; i < lemma->size; i++) printf ("%d ", lemma->literals[i]); printf ("\n");

  vector <int> decisions;
  for (int i = 0; i < lemma->size; i++) {
    int lit = lemma->literals[i];
    if (!internal->val (lit))
    ///NOTE: assert (!internal->val (lit)); ?
    decisions.push_back (-lit);
  }

  assert (decisions.size());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level  == int (decisions.size()));

  for (int i = 0; i < lemma->size; i++)
    if (!internal->var(lemma->literals[i]).level && internal->val(lemma->literals[i]))
      mark_core (internal->var(lemma->literals[i]).reason);

  assert(!internal->conflict);
  if (internal->propagate ())
  {
    ///TODO:  This might happen according to the Minisat patch. It was mentioned:
    //        -- If propagate fails, it may be due to incrementality and missing
    //        -- units. Update qhead and re-propagate the entire trail
    //        Understand what exactly happens and why is this needed.
    //        A good point to start: test/trace/reg0048.trace.
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
      assert (0);
      return false;
    }
  }

  conflict_analysis_core ();

  clear ();
  return true;
}

void BChecker::mark_core_trail_antecedents () {
  for (int i = internal->trail.size() - 1; i >= 0; i--) {
    int lit = internal->trail[i];
    Clause * reason = internal->var (lit).reason;
    assert (reason);
    if (reason->core) {
      assert (reason->literals[0] == lit);
      for (int j = 1; j < reason->size; j++)
        mark_core (internal->var (reason->literals[j]).reason);
      internal->propagated = i;
      ///TODO: set internal->propagated2
    }
  }
}

void BChecker::reallocate () {
  assert (!dying && !validating);
  dying = true;
  assert (proof.size() == counterparts.size ());
  for (int i = 0; i < proof.size (); i++) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];
    if (deleted) {
      assert (c && !c->garbage);
      internal->mark_garbage (c);
      counterparts[i] = 0;
    } else {
      assert (c);
      if (bc->marked_garbage) {
        c->garbage = false;
        bc->marked_garbage = false;
        internal->watch_clause (c);
      }
    }
  }
  dying = false;
}

void BChecker::put_units_back () {
  ///TODO: Is this enough to restore the trail?! ..
  for (int lit : original_units) {
    if (!internal->val (lit)) {
      internal->assign_original_unit (lit);
      assert (internal->var (lit).reason);
    }
  }
}

void BChecker::check_environment () {
  assert (proof.size() == counterparts.size());
  assert (proof.size() == unsigned(stats.derived + stats.deleted));
  for (unsigned i = 0; i < proof.size(); i++) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];
    assert (bc && (!deleted || !c));
    if (!deleted && c && c->garbage)
      ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
      // clauses as deleted (produce 'd ...' lines) as soon they are marked
      // garbage.
      assert (c->size == 2);
  }
}

void BChecker::clear () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

bool BChecker::validate (bool overconstrained) {

  assert (internal->unsat || !internal->marked_failed);

  if (!internal->marked_failed) {
    internal->failing ();
    internal->marked_failed = true;
  }

  START (bchecking);
  LOG ("BCHECKER starting validation");

  validating = true;

#ifndef NDEBUG
    check_environment ();
#endif

  mark_last_conflict (overconstrained);
  clear ();
  unsigned trail_sz = internal->trail.size();

  for (int i = proof.size() - 1; i >= 0; i--) {

    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];

    assert (bc && bc->size);
    assert (!deleted || !c);

    if (deleted) {
      revive_internal_clause (i);
      continue;
    }

    assert (c && (c->size == 2 || !c->garbage));

    if (is_on_trail (c)) {
      if (core_units) mark_core (c);
      undo_trail_core (c, trail_sz);
    }

    stagnate_internal_clause (i);

    if (c->core) {
      shrink_internal_trail (trail_sz);
      if (!validate_lemma (c))
        goto abort;
    }
  }

  shrink_internal_trail (trail_sz);

  mark_core_trail_antecedents ();

  validating = false;

  reallocate  ();

  dump_core ();

abort:
  STOP (bchecking);

  failing_assumptions.clear ();
  put_units_back ();
  internal->garbage_collection();

  ///TODO: reallocate? don't ruin the internal facilities if the validation fails.

  if (validating) return validating = false;
  else return true;
}

/*------------------------------------------------------------------------*/

void BChecker::dump_core () {
  printf ("Core lemmas are: \n");
  for (Clause * c : internal->clauses) {
    if (c->core) {
      for (int i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("\n");
    }
  }
  if (failing_assumptions.size ()) {
    for (int l : failing_assumptions)
      printf ("%d ", l);
    printf ("\n");
    if (failing_assumptions.size () > 1)
      for (int l : internal->assumptions)
        if (internal->failed (l))
          printf ("%d \n", l);
  }
}

/*------------------------------------------------------------------------*/

void BChecker::invalidate_counterpart (Clause * c, int i) {
  assert (c && proof.size() == counterparts.size());
  vector<unsigned> & indexes = cp_ordering[c];
  assert (indexes.size() < 2);
  if (indexes.size ()) stats.counterparts--;
  for (int j : indexes) {
    assert (counterparts[j] == c);
    counterparts[j] = 0;
  }
  assert (revive_ordering[i].empty ());
  revive_ordering[i] = indexes;
  indexes.clear (); // This address might be user for another clause allocation in the future...
  assert (cp_ordering[c].empty ());
  cp_ordering.erase (c);
}

void BChecker::append_lemma (BCheckerClause * bc, Clause * c, bool deleted = false) {
  assert (deleted || c);
  stats.added++;
  if (deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    assert (!validating || !c->core);
    auto & indexes = cp_ordering[c];
    if (deleted) {
      if (c) {
        // assert (indexes.size () == 1); // does not hold with reduce as it might reduce original clauses that have not been added here.
        assert (indexes.size () < 2);
        for (int i : indexes) {
          assert (counterparts[i] == c);
          counterparts[i] = 0;
        }
        assert (revive_ordering[proof.size()].empty ());
        revive_ordering[proof.size()] = indexes;
        indexes.clear (); // This address might be user for another clause allocation in the future...
        assert (cp_ordering[c].empty ());
        cp_ordering.erase (c);
      }
    } else {
      indexes.push_back (proof.size());
      assert (indexes.size() == 1);
      stats.counterparts++;
    }
  }
  proof.push_back ({bc, deleted});
  counterparts.push_back (deleted ? 0 : c);
  assert (proof.size() == counterparts.size());
}

/*------------------------------------------------------------------------*/

void BChecker::add_derived_clause (Clause * c) {
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  append_lemma (insert (c), c);
  STOP (bchecking);
}

void BChecker::add_derived_unit_clause (const int lit, bool original) {
  assert (!validating);
  START (bchecking);
  LOG (lit, "BCHECKER derived clause notification");
  assert (lit);
  if (original) internal->var(lit).reason = 0;
  Clause * c = 0;
  if (!internal->var(lit).reason)
    internal->var(lit).reason = c = internal->new_unit_clause (lit, true);
  if (!original) {
    append_lemma (insert ({lit}), !c ? internal->new_unit_clause (lit, true) : c);
    assert (internal->var(lit).reason->literals[0] == lit);
  } else original_units.push_back (lit);
  STOP (bchecking);
}

void BChecker::add_derived_empty_clause () {
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER derived empty clause notification");
  STOP (bchecking);
}

void BChecker::add_failed_assumptions (const vector<int> & c) {
  ///TODO: Allocate this clause and mark it as core.
  assert (!validating);
  assert (failing_assumptions.empty ());
  failing_assumptions = c;
  for (int failed : failing_assumptions) {
    Clause * r = internal->var (failed).reason;
    if (r) mark_core (r);
  }
}

/*------------------------------------------------------------------------*/

void BChecker::strengthen_clause (Clause * c, int lit) {
  if (validating) return;
  START (bchecking);
  assert (c && lit);
  LOG (c, "BCHECKER strengthen by removing %d in", lit);
  invalidate_counterpart (c, proof.size() + 1);
  vector<int> strengthened;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == lit) continue;
    strengthened.push_back (internal_lit);
  }
  assert (strengthened.size() > 1);
  append_lemma (insert (strengthened), c);
  append_lemma (insert (c), 0, true);
  STOP (bchecking);
}

void BChecker::flush_clause (Clause * c) {
  if (validating) return;
  START (bchecking);
  LOG (c, "BCHECKER flushing falsified literals in");
  assert (c);
  invalidate_counterpart (c, proof.size() + 1);
  vector<int> flushed;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) >= 0)
      flushed.push_back (internal_lit);
  }
  assert (flushed.size() > 1);
  append_lemma (insert (flushed), c);
  append_lemma (insert (c), 0, true);
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::delete_clause (const vector<int> & c, bool original) {
  if (dying) return;
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  vector<int> modified (c);
  if (original) {
    ///NOTE: This is an original clause that has been reduced to an irredundant
    // dervied clause after removing all falsified literals. This clause wasn't
    // allocated in memory. However, it needs to be revived for correct core
    // extraction and complete validation.
    // Moving the falsified literals to the end of the clause is crucial for
    // watching this clause after it is revived in the future as we want to watch
    // the unassigned literals.
    int sz = modified.size ();
    for (int i = 0; i < sz; i++) {
      if (internal->val (c[i]) < 0) {
        int bl = modified[--sz];
        modified[sz] = modified[i];
        modified[i] = bl;
      }
    }
  }
  append_lemma (insert (modified), 0, true);
  STOP (bchecking);
}

void BChecker::delete_clause (Clause * c) {
  ///TODO: Need to handle incrementality. The bchecker should be aware of
  // clauses that were deleted during the trimming/validation process. especially
  // the garbage clauses of size == 2 ??.
  ///TODO: can be triggered from stagnate_internal->clause.... 
  // if (dying) return;
  // assert (!validating);
  if (dying || validating) return;
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  append_lemma (insert (c), c, true);
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::update_moved_counterparts () {
  if (validating) return;
  START (bchecking);
  assert (proof.size() == counterparts.size());
  ///ISSUE: Don't iterate & insert at the same time...
  // for (auto & pair : cp_ordering) {
  //   Clause * c = pair.first;
  //   auto & old_indexes = pair.second;

  //   if (!c || !c->moved) continue;

  //   ///NOTE: old_indexes can be empty. This can happen during the
  //   // flushing of an original clause that is not

  //   auto & new_indexes = cp_ordering[c->copy];

  //   assert (new_indexes.empty());
  //   assert (c->size == 2 || !c->copy->garbage);

  //   for (int j : old_indexes) {
  //       new_indexes.push_back (j);
  //       assert (counterparts[j] == c);
  //       counterparts[j] = c->copy;
  //   }
  //   old_indexes.clear ();
  // }
  for (unsigned i = 0; i < proof.size(); i++) {
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];

    if (deleted || !c || !c->moved)
       continue;

    auto & old_indexes = cp_ordering[c];
    auto & new_indexes = cp_ordering[c->copy];

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
    assert (old_indexes.size() == 1);
    assert (new_indexes.empty());
#endif

    for (int j : old_indexes)
      new_indexes.push_back (j);
    old_indexes.clear ();
    counterparts[i] = c->copy;
  }
  STOP (bchecking);
}

}
