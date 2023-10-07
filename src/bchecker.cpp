#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

BCheckerClause::BCheckerClause (vector<int> c)
:
  revive_at (-1), marked_garbage (false)
{
  assert (c.size ());
  for (auto i : c)
    literals.push_back (i);
};

BCheckerClause::BCheckerClause (Clause * c)
:
  revive_at (-1), marked_garbage (false)
{
  assert (c && c->size);
  for (auto i = c->begin (); i != c->end (); i++)
    literals.push_back (*i);
};

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i, bool core_units)
:
  internal (i), core_units (core_units),
  isolate (0), validating (0)
{
  LOG ("BCHECKER new");

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));
}

BChecker::~BChecker () {
  LOG ("BCHECKER delete");
  isolate = true;
  for (const auto & bc : bchecker_clauses)
    delete (BCheckerClause *) bc;
  for (const auto & c : unit_clauses)
    delete [] (char*) c;
}

/*------------------------------------------------------------------------*/

BCheckerClause * BChecker::insert (Clause * c) {
  stats.insertions++;
  vector<int> lits;
  for (int  i = 0; i < c->size; i++)
    lits.push_back (c->literals[i]);
  BCheckerClause * bc = new BCheckerClause (lits);
  bchecker_clauses.push_back (bc);
  return bc;
}

BCheckerClause * BChecker::insert (const vector<int> & lits) {
  stats.insertions++;
  BCheckerClause * bc = new BCheckerClause (lits);
  bchecker_clauses.push_back (bc);
  return bc;
}

void BChecker::revive_internal_clause (int i) {
  assert (!counterparts[i] && proof[i].second);
  BCheckerClause * bc = proof[i].first;
  assert (!bc->unit ());
  ///NOTE: Unit clauses should not be deleted.
  // The motivation behind allocating unit clauses is to simplify the code.
  ///TODO: set eliminated flag to false if there are eliminated vars.
  vector<int> & clause = internal->clause;
  assert (clause.empty());
  for (int j : bc->literals)
    clause.push_back (j);
  Clause * c = internal->new_clause (true /* if it was deleted before, this means it's redundant */);
  clause.clear();
  internal->watch_clause (c);
  if (bc->revive_at >= 0) {
    int j = bc->revive_at;
    assert (j < i);
    assert (proof[j].first->revive_at < 0);  // Are chains even possible?
    assert (!proof[j].second && !counterparts[j]);
    counterparts[j] = c;
  }
  counterparts[i] = c;
}

void BChecker::stagnate_internal_clause (const int i) {
  assert (proof.size() == counterparts.size());
  Clause * c = counterparts[i];
  if (c->size == 1) return;
  {
    ///BUG: Some clauses seem to be marked as garbage and unwatched.
    // Others are marked as garbage but still watched?
    ///TODO:figure out what is happens with binary clauses.
    internal->unwatch_clause (c);
  }
  ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
  // clauses as deleted (produce 'd ...' lines) as soon they are marked
  // garbage.
  assert (!c->garbage || c->size == 2);
  if (!c->garbage) {
    assert (!c->moved);
    c->garbage = true;
    proof[i].first->marked_garbage = true;
  }
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

void BChecker::mark_conflict_lit (int l) {
  assert (internal->val(l) < 0);
  Var & v = internal->var(l);
  Clause * reason = v.reason;
  if (reason) mark_core (reason);
}

void BChecker::mark_conflict (bool overconstrained) {
  assert (!overconstrained || internal->unsat);
  if (internal->unsat) {
    Clause * conflict = 0;
    if (overconstrained) {
      // Last deleted lemma is the falsified original.
      // Revive it and mark it as the conflict clause.
      int i = proof.size () - 1;
      assert (proof[i].second);
      BCheckerClause * bc = proof[i].first;
      if (bc->unit ()) counterparts[i] = new_unit_clause (proof[i].first->literals[0], true);
      else revive_internal_clause (i);
      conflict = counterparts[i];
    } else {
      conflict = internal->conflict;
    }
    assert (conflict);
    mark_core (conflict);
    for (int i = 0; i < conflict->size; i++)
      mark_conflict_lit (conflict->literals[i]);
  } else {
    assert (failing_assumptions.size () && internal->marked_failed);
  }
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

#ifndef NDEBUG
    assert (internal->var(c->literals[0]).reason == c);
    assert (internal->val(c->literals[0]) > 0);
    assert (c->literals[0] == lit);
#endif

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

  vector <int> decisions;
  for (int i = 0; i < lemma->size; i++) {
    int lit = lemma->literals[i];
    if (!internal->val (lit))
      decisions.push_back (-lit);
  }

  assert (decisions.size());
  internal->search_assume_multiple_decisions (decisions);
  assert (internal->level  == int (decisions.size()));


  ///TODO: is this really needed? drop this...
  for (int i = 0; i < lemma->size; i++)
    if (!internal->var(lemma->literals[i]).level && internal->val(lemma->literals[i]))
      mark_core (internal->var(lemma->literals[i]).reason);

  assert(!internal->conflict);
  if (internal->propagate ())
  {
    // If propagate fails, it may be due to incrementality and
    // missing units. re-propagate the entire trail.
    ///TODO: Understand what exactly happens and why is this needed.
    // A good point to start: test/trace/reg0048.trace.
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
      return false;
    }
  }

  conflict_analysis_core ();

  clear_conflict ();
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
  assert (!isolate);
  lock_scope isolated (isolate);
  assert (proof.size() == counterparts.size ());
  for (unsigned i = 0; i < proof.size (); i++) {
    BCheckerClause * bc = proof[i].first;
    bool deleted = proof[i].second;
    Clause * c = counterparts[i];
    if (deleted) {
      assert (c && !c->garbage);
      counterparts[i] = 0;
      if (bc->unit ()) continue;
      internal->unwatch_clause (c);
      internal->mark_garbage (c);
    } else {
      assert (c);
      if (bc->marked_garbage) {
        bc->marked_garbage = c->garbage = false;
        internal->watch_clause (c);
      }
    }
  }
  internal->garbage_collection ();
}

void BChecker::put_units_back () {
  lock_scope isolated (isolate);
  for (Clause * c : unit_clauses) {
    const int lit = c->literals[0];
    if (!internal->val (lit))
      internal->search_assign (lit, c);
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

void BChecker::clear_conflict () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

void BChecker::dump_proof () {
  for (int i = proof.size () - 1; i >= 0; i--) {
    printf ("%s: ", proof[i].second ? "deleted" : "       ");
    auto & lits = proof[i].first->literals;
    for (int l : lits)
      printf ("%d ", l);
    Clause * c = counterparts[i];
    printf ("c: ");
    if (!c) printf ("0 ");
    else for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
    printf ("\n");
  }
}

bool BChecker::validate (bool overconstrained) {

  assert (!validating);
  assert (internal->unsat || !internal->marked_failed);

#ifndef NDEBUG
    check_environment ();
#endif

  save_scope save_unsat (internal->unsat);
  if (!internal->marked_failed) {
    internal->failing ();
    internal->marked_failed = true;
  }

  START (bchecking);
  LOG ("BCHECKER starting validation");
  lock_scope validation_scope (validating);

  mark_conflict (overconstrained);
  clear_conflict ();
  unsigned trail_sz = internal->trail.size();

  for (int i = proof.size() - 1 - int (overconstrained); i >= 0; i--) {

    bool deleted = proof[i].second;
    Clause * c = counterparts[i];

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
      bool lemma_validated = validate_lemma (c);
      assert (lemma_validated);
    }
  }

  shrink_internal_trail (trail_sz);
  mark_core_trail_antecedents ();

  // This is a good point to dump core as some of
  // the satisfied clauses will be removed after.
  dump_core ();

  reallocate  ();
  put_units_back ();
  failing_assumptions.clear ();

  STOP (bchecking);
  return true;
}

/*------------------------------------------------------------------------*/

void BChecker::dump_core () {
  printf ("DUMP CORE START\n");
  for (Clause * c : internal->clauses) {
    if (c->core) {
      for (int i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("\n");
    }
  }
  for (Clause * c : unit_clauses) {
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
  printf ("DUMP CORE END\n");
}

/*------------------------------------------------------------------------*/

Clause * BChecker::new_unit_clause (const int lit, bool original) {

  const int size = 1;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  stats.units++;

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = true;
  c->moved = false;
  c->reason = false;
  ///NOTE: for clauses of size 1, irredundant iff original.
  c->redundant = !original;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->core = false;
  c->used = c->glue = 0;
  c->size = size;
  c->pos = 2;
  c->literals[0] = lit;

  assert (c->bytes () == bytes);

  unit_clauses.push_back (c);
  LOG (c, "new pointer %p", (void*) c);

  return c;
}

/*------------------------------------------------------------------------*/

///TODO: Consider using lazy bchecker clause allocation: allocate once the internal
// clause is discarded from memory.
void BChecker::append_lemma (BCheckerClause * bc, Clause * c, bool deleted = false) {
  assert (deleted || c);
  assert (bc->revive_at < 0);
  stats.added++;
  if (deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    auto & indexes = cp_ordering[c];
    if (deleted) {
      if (c) {
        assert (indexes.size () < 2);
        for (int i : indexes) {
          assert (counterparts[i] == c);
          counterparts[i] = 0;
          bc->revive_at = i;
        }
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
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER derived clause notification");
  append_lemma (insert (c), c);
  STOP (bchecking);
}

void BChecker::add_derived_unit_clause (const int lit, bool original) {
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  LOG ({lit}, "BCHECKER derived clause notification");
  assert (lit);
  if (original) internal->var(lit).reason = 0;
  Clause * c = 0;
  if (!internal->var(lit).reason)
    internal->var(lit).reason = c = new_unit_clause (lit, original);
  if (!original) {
    append_lemma (insert ({lit}), !c ? new_unit_clause (lit, original) : c);
    assert (internal->var(lit).reason->literals[0] == lit);
  }
  STOP (bchecking);
}

void BChecker::add_derived_empty_clause () {
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  LOG ("BCHECKER derived empty clause notification");
  STOP (bchecking);
}

void BChecker::add_failed_assumptions (const vector<int> & c) {
  ///TODO: Allocate this clause and mark it as core.
  if (isolate) return;
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
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  assert (c && lit);
  LOG (c, "BCHECKER strengthen by removing %d in", lit);
  vector<int> strengthened;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == lit) continue;
    strengthened.push_back (internal_lit);
  }
  assert (strengthened.size() > 1);
  BCheckerClause * bc_strengthened = insert (strengthened);
  BCheckerClause * bc_c = insert (c);
  assert (cp_ordering[c].size () < 2);
  int revive_at = -1;
  if (cp_ordering[c].size ()) {
    revive_at = cp_ordering[c][0];
    counterparts[revive_at] = 0;
    stats.counterparts--;
    cp_ordering[c].clear ();
  }
  assert (cp_ordering[c].empty ());
  append_lemma (bc_strengthened, c);
  assert (cp_ordering[c].size () == 1);
  append_lemma (bc_c, 0, true);
  assert (cp_ordering[c].size () == 1);
  assert (bc_strengthened->revive_at < 0 && cp_ordering[c].size () == 1);
  bc_c->revive_at = revive_at;
  STOP (bchecking);
}

void BChecker::flush_clause (Clause * c) {
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER flushing falsified literals in");
  assert (c);
  vector<int> flushed;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) >= 0)
      flushed.push_back (internal_lit);
  }
  assert (flushed.size() > 1);
  BCheckerClause * bc_flushed = insert (flushed);
  BCheckerClause * bc_c = insert (c);
  assert (cp_ordering[c].size () < 2);
  int revive_at = -1;
  if (cp_ordering[c].size ()) {
    assert (cp_ordering[c].size () == 1);
    revive_at = cp_ordering[c][0];
    counterparts[revive_at] = 0;
    stats.counterparts--;
    cp_ordering[c].clear ();
  }
  append_lemma (bc_flushed, c);
  append_lemma (bc_c, 0, true);
  assert (bc_flushed->revive_at < 0 && cp_ordering[c].size () == 1);
  bc_c->revive_at = revive_at;
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::delete_clause (const vector<int> & c, bool original) {
  if (isolate) return;
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
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  LOG (c, "BCHECKER clause deletion notification");
  append_lemma (insert (c), c, true);
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::update_moved_counterparts () {
  if (isolate) return;
  assert (!validating);
  START (bchecking);
  assert (proof.size() == counterparts.size());
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
