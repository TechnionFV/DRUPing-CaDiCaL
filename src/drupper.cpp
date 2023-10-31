#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {


/*------------------------------------------------------------------------*/

// Enable proof drupping.

void Internal::drup () {
  assert (!drupper);
  drupper = new Drupper (this);
  drupper->setup_options ();
}

/*------------------------------------------------------------------------*/

DrupperClause::DrupperClause (vector<int> c)
:
  marked_garbage (false), revive_at (-1),
  failed (false), deleted (false), counterpart (0)
{
  assert (c.size ());
  for (auto i : c)
    literals.push_back (i);
};

DrupperClause::DrupperClause (Clause * c)
:
  marked_garbage (false), revive_at (-1),
  failed (false), deleted (false), counterpart (0)
{
  assert (c && c->size);
  for (auto i = c->begin (); i != c->end (); i++)
    literals.push_back (*i);
};

bool DrupperClause::unit () const {
  return literals.size () == 1;
}

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal * i, File * f, bool core_units)
:
  internal (i), failed_constraint (0),
  core_units (core_units), isolate (0),
  validating (0), file (f)
{
  LOG ("DRUPPER new");

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));

  if (internal->opts.drupdumpcore && !f)
    file = File::write (internal, stdout, "<stdout>");
}

Drupper::~Drupper () {
  LOG ("DRUPPER delete");
  isolate = true;
  for (const auto & dc : drupper_clauses)
    delete (DrupperClause *) dc;
  for (const auto & c : unit_clauses)
    delete [] (char*) c;
}
/*------------------------------------------------------------------------*/

bool Drupper::setup_options () {
  auto & opts = internal->opts;
  bool updated = false;
  updated |= opts.chrono;
  updated |= opts.vivify;
  updated |= opts.probe;
  // updated |= opts.condition;
  updated |= opts.compact;
  opts.chrono = 0;
  opts.vivify = 0;
  opts.probe = 0;
  // opts.condition = 0;
  opts.compact = 0;
  return updated;
}

/*------------------------------------------------------------------------*/

Clause * Drupper::new_unit_clause (const int lit, bool original) {

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

DrupperClause * Drupper::insert (Clause * c) {
  vector<int> lits;
  for (int  i = 0; i < c->size; i++)
    lits.push_back (c->literals[i]);
  DrupperClause * dc = new DrupperClause (lits);
  drupper_clauses.push_back (dc);
  return dc;
}

DrupperClause * Drupper::insert (const vector<int> & lits) {
  DrupperClause * dc = new DrupperClause (lits);
  drupper_clauses.push_back (dc);
  return dc;
}

/*------------------------------------------------------------------------*/

void Drupper::set_counterpart (DrupperClause * dc, Clause * c) {
  assert (!dc->counterpart);
  dc->counterpart = c;
  stats.counterparts++;
}

void Drupper::reset_counterpart (DrupperClause * dc) {
  assert (dc->counterpart);
  dc->counterpart = 0;
  stats.counterparts--;
}

/*------------------------------------------------------------------------*/

// Return true iff the clause contains a literal and its negation.
bool Drupper::trivially_satisfied (const vector <int> & c) {
  struct {
    bool operator () (const int & a, const int & b) {
      return (abs (a) < abs (b)) || (abs (a) == abs (b) && a < b);
    }
  } sorter;
  auto sorted (c);
  std::sort (sorted.begin (), sorted.end (), sorter);
  for (unsigned i = 1; i < sorted.size (); i++)
    if (sorted[i] == -sorted[i-1])
      return true;
  return false;
}

///TODO: Consider using lazy drupper clause allocation: allocate once the internal
// clause is discarded from memory.
void Drupper::append_lemma (DrupperClause * dc, Clause * c, bool deleted = false) {
  assert (dc->revive_at < 0);
  if (deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    auto & order = cp_ordering[c];
    if (deleted) {
      if (c) {
        if (order.cached ()) {
          int i = order.remove ();
          assert (proof[i]->counterpart == c);
          reset_counterpart (proof[i]);
          dc->revive_at = i;
        }
        assert (!order.cached ());
      }
    } else {
      order.cache (proof.size ());
    }
  }
  dc->deleted = deleted;
  set_counterpart (dc, deleted ? 0 : c);
  proof.push_back (dc);
}

void Drupper::append_failed (const vector<int> & c) {
  append_lemma (insert (c), 0);
  append_lemma (insert (c), 0, true);
  int i = proof.size () - 1;
  proof[i]->revive_at = i - 1;
  proof[i]->failed = true;
}

void Drupper::revive_internal_clause (int i) {
  assert (i >= 0 && i < proof.size ());
  DrupperClause * dc = proof[i];
  assert (!dc->unit () && !dc->counterpart && dc->deleted);
  vector<int> & clause = internal->clause;
  assert (clause.empty());
  for (int j : dc->literals) {
    if (internal->flags (j).eliminated ())
      internal->reactivate (j);
    clause.push_back (j);
  }
  Clause * c = internal->new_clause (true );
  clause.clear();
  internal->watch_clause (c);
  if (dc->revive_at >= 0) {
    int j = dc->revive_at;
#ifndef NDEBUG
    assert (j < i);
    assert (proof[j]->revive_at < 0);  // Are chains even possible?
    assert (!proof[j]->deleted && !proof[j]->counterpart);
#endif
    set_counterpart (proof[j], c);
  }
  set_counterpart (proof[i], c);
  if (dc->failed)
    mark_core (c);
}

void Drupper::stagnate_internal_clause (const int i) {
  Clause * c = proof[i]->counterpart;
  if (c->size == 1) return;
  internal->unwatch_clause (c);
  {
    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->garbage || c->size == 2);
    assert (!c->garbage && "remove this if you are actually delaying the trace of garbage binaries");
    if (!c->garbage) {
      assert (!c->moved);
      c->garbage = true;
      proof[i]->marked_garbage = true;
    }
  }
}

///NOTE: The internal solver does not support reactivation
// of fixed literals. However, this is needed to be able
// to propagate these literals again.
void Drupper::reactivate_fixed (int l) {
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

/*------------------------------------------------------------------------*/

void Drupper::shrink_internal_trail (const unsigned trail_sz) {
  assert (trail_sz <= internal->trail.size());
  internal->trail.resize(trail_sz);
  internal->propagated = trail_sz;
  ///TODO: set internal->propagated2 properly.
  assert (!internal->level);
  assert(internal->control.size () == 1);
}

void Drupper::clear_conflict () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

/*------------------------------------------------------------------------*/

void Drupper::undo_trail_literal (int lit) {
  assert (internal->val (lit) > 0);
  if (!internal->active (lit))
    reactivate_fixed (lit);
  internal->unassign (lit);
  assert (!internal->val (lit));
  assert (internal->active (lit));
#ifndef NDEBUG
  Var & v = internal->var (lit);
  assert (v.reason);
  // v.reason = 0;
#endif
}

void Drupper::undo_trail_core (Clause * c, unsigned & trail_sz) {

#ifndef NDEBUG
  assert (trail_sz > 0);
  assert (trail_sz <= internal->trail.size());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (internal->var (clit).reason == c);
  assert (internal->val (clit) > 0);
#endif

  while (internal->trail[--trail_sz] != clit)
  {
    assert(trail_sz > 0);
    int l = internal->trail[trail_sz];

    Clause * r = internal->var(l).reason;
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (core_units) mark_core (r);

    if (r->core)
      for (int j = 1; j < r->size; j++)
        mark_core (internal->var(r->literals[j]).reason);
  }

  assert(clit == internal->trail[trail_sz]);
  undo_trail_literal (clit);
}

bool Drupper::is_on_trail (Clause * c) {
  assert (c);
  int lit = c->literals[0];
  return internal->val (lit) > 0 && internal->var (lit).reason == c;
}

/*------------------------------------------------------------------------*/

void Drupper::mark_core (Clause * c) {
  assert (c);
  if (!c->core) stats.core++;
  c->core = true;
}

void Drupper::mark_conflict_lit (int l) {
  assert (internal->val(l) < 0);
  Var & v = internal->var(l);
  Clause * reason = v.reason;
  if (reason) mark_core (reason);
}

void Drupper::mark_conflict (bool overconstrained) {
  assert (!overconstrained || internal->unsat);
  if (internal->unsat) {
    Clause * conflict = 0;
    if (overconstrained) {
      // Last deleted lemma is the falsified original.
      // Revive it and mark it as the conflict clause.
      int i = proof.size () - 1;
      assert (i >= 0 && proof[i]->deleted);
      DrupperClause * dc = proof[i];
      if (dc->unit ())
        set_counterpart (proof[i], new_unit_clause (dc->literals[0], false));
      else
        revive_internal_clause (i);
      conflict = proof[i]->counterpart;
    } else {
      conflict = internal->conflict;
    }
    mark_core (conflict);
    for (int i = 0; i < conflict->size; i++)
      mark_conflict_lit (conflict->literals[i]);
  }
}

void Drupper::mark_failed_conflict () {
  assert (!failed_constraint);
  assert (internal->clause.empty ());
  if (internal->unsat_constraint && internal->constraint.size () > 1) {
    internal->clause = internal->constraint;
    failed_constraint = internal->new_clause (true);
    mark_core (failed_constraint);
    internal->watch_clause (failed_constraint);
    internal->clause.clear ();
  }
  assert (!internal->marked_failed);
  internal->failing ();
  internal->marked_failed = true;
}

/*------------------------------------------------------------------------*/

void Drupper::assume_negation (const Clause * lemma) {
  assert (validating && !internal->level);
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
}

bool Drupper::propagate_conflict () {
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
  return true;
}


void Drupper::conflict_analysis_core () {

  Clause * conflict = internal->conflict;
  assert(conflict);
  mark_core (conflict);

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

/*------------------------------------------------------------------------*/

void Drupper::mark_core_trail_antecedents () {
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

void Drupper::unmark_core_clauses () {
  save_core_phase_stats ();
  for (Clause * c : internal->clauses)
    if (c->core)
      c->core = false, stats.core--;
  for (Clause * c : unit_clauses)
    if (c->core)
      c->core = false, stats.core--;
  assert (stats.core == 0);
}

void Drupper::restore_trail () {
  assert (isolate);
  // Restoring the trail is done with respect to the order of literals.
  // Each unit is allocated in the same order it's pushed the trail.
  for (Clause * c : unit_clauses) {
    const int lit = c->literals[0];
    if (internal->val (lit)) continue;
    internal->search_assign (lit, c);
    internal->propagate ();
  }
}

void Drupper::clear_failing_assumptions (const unsigned proof_sz) {
  if (proof.size () == proof_sz) return;
  int pop = proof.size () - proof_sz;
  while (pop--) {
    if (proof.back ()->deleted)
      stats.deleted--;
    else
      stats.derived--;
    proof.pop_back ();
  };
}

void Drupper::reallocate () {
  assert (isolate);
  for (DrupperClause * dc : proof) {
    Clause * c = dc->counterpart;
    if (!dc->deleted) {
      assert (c);
      assert (dc->revive_at < 0);
      if (dc->marked_garbage) {
        dc->marked_garbage = c->garbage = false;
        internal->watch_clause (c);
      } else if (c->garbage) {
        assert (c->size == 2);
        assert (0 && "remove this if you are actually delaying the trace of garbage binaries");
      }
    }
  }
  for (int i = proof.size () - 1; i >= 0; i--) {
    DrupperClause * dc = proof[i];
    Clause * c = dc->counterpart;
    if (dc->deleted) {
      assert (c && !c->garbage);
      reset_counterpart (dc);
      if (dc->revive_at >= 0)
        reset_counterpart (proof[dc->revive_at]);
      if (dc->unit ()) continue;
      internal->mark_garbage (c);
    }
  }
}

void Drupper::reconsruct (const unsigned proof_sz) {
  lock_scope isolated (isolate);
  reallocate ();
  if (failed_constraint) {
    internal->unwatch_clause (failed_constraint);
    internal->mark_garbage (failed_constraint);
    failed_constraint = 0;
  }
  clear_failing_assumptions (proof_sz);
  restore_trail ();
}

/*------------------------------------------------------------------------*/

void Drupper::check_environment () const {
  assert (proof.size() == unsigned(stats.derived + stats.deleted));
  for (unsigned i = 0; i < proof.size(); i++) {
    DrupperClause * dc = proof[i];
    Clause * c = dc->counterpart;
    assert (dc && (!dc->deleted || !c));
    if (!dc->deleted && c && c->garbage) {
      ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
      // clauses as deleted (produce 'd ...' lines) as soon they are marked
      // garbage.
      assert (c->size == 2);
      assert (0 && "remove this if you are actually delaying the trace of garbage binaries");
    }
  }
}

void Drupper::dump_clauses (bool active) const {
  printf ("DUMP CLAUSES START\n");
  int j = unit_clauses.size() - 1;
  for (int i = internal->clauses.size () - 1; i >= 0; i--) {
    Clause * c = internal->clauses[i];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", i + j + 1, c->garbage ? "garbage" : "       ");
    printf ("(%lu): ", c);
    for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  for (; j >= 0; j--) {
    Clause * c = unit_clauses[j];
    if (active && c->garbage && c->size != 2)
      continue;
    printf ("(%d) %s: ", j, c->garbage ? "garbage" : "       ");
    printf ("c: ");
    for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
    printf ("\n");
  }
  printf ("DUMP CLAUSES END\n");
}

void Drupper::dump_clause (const Clause * c) const {
  if (!c) printf ("0 \n");
  else {
    const int * lits = c->literals;
    for (int i = 0; i < c->size; i++)
      printf ("%d ", lits[i]);
    printf ("\n");
  }
}

void Drupper::dump_clause (const DrupperClause * dc) const {
  assert (dc);
  for (int i : dc->literals)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_clause (const vector <int> & c) const {
  for (int i : c)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_proof () const {
  printf ("DUMP PROOF START\n");
  for (int i = proof.size () - 1; i >= 0; i--) {
    printf ("(%d) %s: ", i, proof[i]->deleted ? "deleted" : "       ");
    auto & lits = proof[i]->literals;
    for (int l : lits)
      printf ("%d ", l);
    Clause * c = proof[i]->counterpart;
    printf ("c: ");
    if (!c) printf ("0 ");
    else {
      for (int j = 0; j < c->size; j++) printf ("%d ", c->literals[j]);
      printf ("%s", c->garbage ? "(garbage)" : "");
    }
    printf ("\n");
  }
  printf ("DUMP PROOF END\n");
}

void Drupper::dump_trail () const {
  printf ("DUMP TRAIL START\n");
  auto & trail = internal->trail;
  for (int i = trail.size () - 1; i >= 0; i--)
    printf ("(%d) %d <-- ", i, trail[i]), dump_clause (internal->var (trail[i]).reason);
  printf ("DUMP TRAIL END\n");
}

bool Drupper::core_is_unsat () const {
  CaDiCaL::Solver s;
  s.set ("drup", 0);
  for (Clause * c : internal->clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        s.add (*i);
      s.add (0);
    }
  for (Clause * c : unit_clauses)
    if (c->core) {
      s.add (c->literals[0]);
      s.add (0);
    }
  for (int l : internal->assumptions)
    if (internal->failed (l)) {
      s.add (l);
      s.add (0);
    }
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    for (int i : internal->constraint)
      s.add (i);
    s.add (0);
  } // Otherwise should be part if internal->clauses
  return s.solve () == 20;
}

void Drupper::dump_core () const {
  if (!internal->opts.drupdumpcore || !file)
    return;
  file->put ("DUMP CORE START\n");
  for (Clause * c : internal->clauses)
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        file->put (*i), file->put (' ');
      file->put ("0\n");
    }
  for (Clause * c : unit_clauses)
    if (c->core) {
      file->put (c->literals[0]);
      file->put (" 0\n");
    }
  for (int l : internal->assumptions)
    if (internal->failed (l)) {
      file->put (l);
      file->put (" 0\n");
    }
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    for (int i : internal->constraint)
      file->put (i), file->put (' ');
    file->put ("0\n");
  } // Otherwise should be part if internal->clauses
  file->put ("DUMP END START\n");
}

/*------------------------------------------------------------------------*/

void Drupper::add_derived_clause (Clause * c) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG (c, "DRUPPER derived clause notification");
  append_lemma (insert (c), c);
  STOP (drupping);
}

void Drupper::add_derived_unit_clause (const int lit, bool original) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG ({lit}, "DRUPPER derived clause notification");
  assert (lit);
  assert (!original || !internal->var(lit).reason);
  Clause * c = 0;
  if (!internal->var(lit).reason)
    internal->var(lit).reason = c = new_unit_clause (lit, original);
  if (!original)
    append_lemma (insert ({lit}), !c ? new_unit_clause (lit, original) : c);
  assert (internal->var(lit).reason->literals[0] == lit);
  STOP (drupping);
}

void Drupper::add_derived_empty_clause () {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drupping);
}

void Drupper::add_failing_assumption (const vector<int> & c) {
  if (isolate) return;
  assert (!validating);
  if (c.size () > 1) {
    // See ../interesting_tests/assump_and_constraint
    if (!trivially_satisfied (c))
      append_failed (c);
  } else {
    Clause * r = internal->var (c[0]).reason;
    if (r) mark_core (r);
  }
}

/*------------------------------------------------------------------------*/

void Drupper::strengthen_clause (Clause * c, int lit) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  assert (c && lit);
  LOG (c, "DRUPPER strengthen by removing %d in", lit);
  vector<int> strengthened;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal_lit == lit) continue;
    strengthened.push_back (internal_lit);
  }
  assert (strengthened.size() > 1);
  int revive_at = -1;
  auto & order = cp_ordering[c];
  if (order.cached ()) {
    revive_at = order.remove ();
    reset_counterpart (proof[revive_at]);
  }
  append_lemma (insert (strengthened), c);
  append_lemma (insert (c), 0, true);
  proof[proof.size ()-1]->revive_at = revive_at;
  STOP (drupping);
}

void Drupper::flush_clause (Clause * c) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG (c, "DRUPPER flushing falsified literals in");
  assert (c);
  vector<int> flushed;
  for (int i = 0; i < c->size; i++) {
    int internal_lit = c->literals[i];
    if (internal->fixed (internal_lit) >= 0)
      flushed.push_back (internal_lit);
  }
  assert (flushed.size() > 1);
  int revive_at = -1;
  auto & order = cp_ordering[c];
  if (order.cached ()) {
    revive_at = order.remove ();
    assert (proof[revive_at]->counterpart == c);
    reset_counterpart (proof[revive_at]);
  }
  append_lemma (insert (flushed), c);
  append_lemma (insert (c), 0, true);
  proof[proof.size ()-1]->revive_at = revive_at;
  STOP (drupping);
}

/*------------------------------------------------------------------------*/

void Drupper::delete_clause (const vector<int> & c, bool original) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG (c, "DRUPPER clause deletion notification");
  vector<int> modified;
  ///TODO: remoeve duplicates. if there is only one unique literal, skip.
  for (int lit : c) {
    if (internal->marked (lit))
      continue;
    internal->mark (lit);
    modified.push_back (lit);
  }
  for (int lit : modified)
    internal->unmark (lit);
  if (modified.size () == c.size () || modified.size () > 1) {
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
  }
  STOP (drupping);
}

void Drupper::delete_clause (Clause * c) {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  LOG (c, "DRUPPER clause deletion notification");
  append_lemma (insert (c), c, true);
  STOP (drupping);
}

/*------------------------------------------------------------------------*/

void Drupper::update_moved_counterparts () {
  if (isolate) return;
  assert (!validating);
  START (drupping);
  for (unsigned i = 0; i < proof.size(); i++) {
    bool deleted = proof[i]->deleted;
    Clause * c = proof[i]->counterpart;

    if (deleted || !c || !c->moved)
       continue;

    auto & old_order = cp_ordering[c];
    auto & new_order = cp_ordering[c->copy];

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
    assert (old_order.cached ());
    assert (!new_order.cached ());
#endif

    new_order.cache (old_order.remove ());
    reset_counterpart (proof[i]);
    set_counterpart (proof[i], c->copy);
  }
  STOP (drupping);
}

/*------------------------------------------------------------------------*/

bool Drupper::trim (bool overconstrained) {

#ifndef NDEBUG
  assert (!setup_options ());
  check_environment ();
#endif

  assert (!validating && !isolate);
  save_scope<bool> save_unsat (internal->unsat);

  const unsigned proof_sz = proof.size ();
  if (internal->unsat) {
    mark_conflict (overconstrained);
    assert (proof_sz == proof.size ());
  } else {
    mark_failed_conflict ();
  }

  START (trimming);
  LOG ("DRUPPER starting validation");

  clear_conflict ();

  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = internal->trail.size();
  lock_scope validation_scope (validating);

  for (int i = proof.size() - 1 - int (overconstrained); i >= 0; i--) {

    bool deleted = proof[i]->deleted;
    Clause * c = proof[i]->counterpart;

    assert (!deleted || !c);

    if (deleted) {
      revive_internal_clause (i);
      continue;
    }

    if (is_on_trail (c)) {
      if (core_units) mark_core (c);
      undo_trail_core (c, trail_sz);
    }

    stagnate_internal_clause (i);

    if (c->core) {
      shrink_internal_trail (trail_sz);
      assume_negation (c);
      bool validated = propagate_conflict ();
      assert (validated);
      conflict_analysis_core ();
      clear_conflict ();
    }
  }

  shrink_internal_trail (trail_sz);
  mark_core_trail_antecedents ();

  {
    // This is a good point to dump core as some of
    // the satisfied clauses will be removed later.
    // ```
    dump_core ();
    // ```
    #ifndef NDEBUG
      assert (core_is_unsat ());
    #endif
  }

  unmark_core_clauses ();
  reconsruct (proof_sz);

  STOP (trimming);
  return true;
}

}
