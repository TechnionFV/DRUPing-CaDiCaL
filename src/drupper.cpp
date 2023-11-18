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

DrupperClause::DrupperClause (bool deletion, bool failing)
:
  marked_garbage (false), revive_at (0),
  failed (failing), deleted (deletion), counterpart (0)
{
};

DrupperClause::DrupperClause (vector<int> c, bool deletion, bool failing)
:
  marked_garbage (false), revive_at (0),
  failed (failing), deleted (deletion), counterpart (0)
{
  assert (c.size ());
  for (auto i : c)
    literals.push_back (i);
};

DrupperClause::DrupperClause (Clause * c, bool deletion, bool failing)
:
  marked_garbage (false), revive_at (0),
  failed (failing), deleted (deletion), counterpart (0)
{
  assert (c && c->size);
  for (const int l : *c)
    literals.push_back (l);
};

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal * i, File * f, bool core_units)
:
  internal (i), failed_constraint (0),
  core_units (core_units), isolated (0),
  validating (0), file (f), solves (0)
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
  isolated = true;
  for (const auto & dc : proof)
    delete (DrupperClause *) dc;
  for (const auto & c : unit_clauses)
    delete [] (char*) c;
  delete file;
}
/*------------------------------------------------------------------------*/

bool Drupper::setup_options () {
  auto & opts = internal->opts;
  bool updated = false;
  updated |= opts.chrono;
  updated |= opts.probe;
  updated |= opts.compact;
  opts.chrono = 0;
  opts.probe = 0;
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
  c->drup_idx = 0;
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

void Drupper::set_counterpart (DrupperClause * dc, Clause * c) {
  assert (!dc->counterpart);
  dc->counterpart = c;
  stats.counterparts++;
  if (c) dc->literals.clear ();
}

void Drupper::reset_counterpart (DrupperClause * dc) {
  assert (dc->counterpart && dc->literals.empty ());
  for (const int & lit : *dc->counterpart)
    dc->literals.push_back (lit);
  dc->counterpart->drup_idx = 0;
  stats.counterparts--;
  dc->counterpart = 0;
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
void Drupper::append_lemma (DrupperClause * dc, Clause * c) {
  assert (!dc->revive_at);
  if (dc->deleted) stats.deleted++;
  else stats.derived++;
  if (c) {
    if (dc->deleted) {
      if (c->drup_idx) {
        assert (proof[c->drup_idx - 1]->counterpart == c);
        dc->revive_at = c->drup_idx;
        reset_counterpart (proof[c->drup_idx - 1]);
      }
    } else {
      c->drup_idx = proof.size () + 1;
    }
  }
  set_counterpart (dc, dc->deleted ? 0 : c);
  proof.push_back (dc);
}

void Drupper::append_failed (const vector<int> & c) {
  append_lemma (new DrupperClause (c), 0);
  append_lemma (new DrupperClause (c, true), 0);
  int i = proof.size () - 1;
  proof[i]->revive_at = i;
  proof[i]->failed = true;
}

void Drupper::revive_clause (int i) {
  START (drup_revive);
  assert (i >= 0 && i < proof.size ());
  DrupperClause * dc = proof[i];
  assert (!dc->counterpart && dc->deleted);
  assert (dc->literals.size () > 1);
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
  if (dc->revive_at) {
    int j = dc->revive_at - 1;
#ifndef NDEBUG
    assert (j < i && j >= 0);
    assert (!proof[j]->revive_at);  // Are chains even possible?
    assert (!proof[j]->deleted && !proof[j]->counterpart);
#endif
    set_counterpart (proof[j], c);
  }
  set_counterpart (proof[i], c);
  if (dc->failed)
    mark_core (c);
  STOP (drup_revive);
}

void Drupper::stagnate_clause (const int i) {
  Clause * c = proof[i]->counterpart;
  if (c->size == 1) return;
  internal->unwatch_clause (c);
  {
    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->garbage && "remove this if you are actually delaying the trace of garbage binaries");
  }
  assert (!c->moved);
  c->garbage = true;
  proof[i]->marked_garbage = true;
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

void Drupper::clean_conflict () {
  internal->unsat = false;
  internal->backtrack();
  internal->conflict = 0;
}

/*------------------------------------------------------------------------*/

void Drupper::undo_trail_literal (const int lit) {
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
  START (drup_undo_trail);
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
  STOP (drup_undo_trail);
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

void Drupper::mark_conflict_lit (const int l) {
  assert (internal->val(l) < 0);
  Var & v = internal->var(l);
  Clause * reason = v.reason;
  if (reason) mark_core (reason);
}

void Drupper::mark_conflict (bool overconstrained) {
  if (internal->unsat) {
    Clause * conflict = 0;
    if (overconstrained) {
      // Last deleted lemma is the falsified original.
      // Revive it and mark it as the conflict clause.
      int i = proof.size () - 1;
      assert (i >= 0 && proof[i]->deleted);
      DrupperClause * dc = proof[i];
      if (dc->literals.size () == 1)
        set_counterpart (proof[i], new_unit_clause (dc->literals[0], false));
      else
        revive_clause (i);
      conflict = proof[i]->counterpart;
    } else {
      conflict = internal->conflict;
    }
    mark_core (conflict);
    for (int i = 0; i < conflict->size; i++)
      mark_conflict_lit (conflict->literals[i]);
  } else {
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
  START (drup_propagate);
  assert(!internal->conflict);
  if (internal->propagate ())
  {
    START (drup_repropagate);
    {
      // If propagate fails, it may be due to incrementality and
      // missing units. re-propagate the entire trail.
      ///TODO: Understand what exactly happens and why is this needed.
      // A good point to start: test/trace/reg0048.trace.
      assert (solves);
    }
    internal->propagated = 0;
    if (internal->propagate ()) {
      internal->backtrack ();
      return false;
    }
    STOP (drup_repropagate);
  }
  STOP (drup_propagate);
  return true;
}


void Drupper::conflict_analysis_core () {
  START (drup_analyze);
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
  STOP (drup_analyze);
}

/*------------------------------------------------------------------------*/

static void collect (Internal * internal) {
  if (!internal->protected_reasons)
    internal->protect_reasons ();
  internal->delete_garbage_clauses ();
  internal->unprotect_reasons ();
}

/*------------------------------------------------------------------------*/

void Drupper::mark_core_trail_antecedents () {
  START (drup_mark_antecedents);
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
  STOP (drup_mark_antecedents);
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
  assert (isolated);
  // Restoring the trail is done with respect to the order of literals.
  // Each unit is allocated in the same order it's pushed the trail.
  for (Clause * c : unit_clauses) {
    const int lit = c->literals[0];
    if (internal->val (lit)) continue;
    internal->search_assign (lit, c);
    internal->propagate ();
  }
}

void Drupper::clear_failing (const unsigned proof_sz) {
  if (failed_constraint) {
    internal->unwatch_clause (failed_constraint);
    internal->mark_garbage (failed_constraint);
    failed_constraint = 0;
  }
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
  assert (isolated);
  for (DrupperClause * dc : proof) {
    Clause * c = dc->counterpart;
    if (!dc->deleted) {
      assert (c);
      assert (!dc->revive_at);
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
      if (dc->revive_at)
        reset_counterpart (proof[dc->revive_at - 1]);
      if (dc->literals.size () == 1) continue;
      internal->mark_garbage (c);
    }
  }
}

void Drupper::reconsruct (const unsigned proof_sz) {
  START (drup_reconstruct);
  lock_scope isolate (isolated);
  unmark_core_clauses ();
  reallocate ();
  clear_failing (proof_sz);
  restore_trail ();
  collect (internal);
  STOP (drup_reconstruct);
}

/*------------------------------------------------------------------------*/

void Drupper::check_environment () const {
#ifndef NDEBUG
  assert (proof.size() == unsigned(stats.derived + stats.deleted));
  for (unsigned i = 0; i < proof.size(); i++) {
    DrupperClause * dc = proof[i];
    Clause * c = dc->counterpart;
    assert (dc);
    if (dc->deleted) {
      assert (dc->literals.size () && !c);
      if (dc->revive_at) {
        assert (dc->revive_at <= proof.size ());
        assert (dc->revive_at > 0);
        assert (!proof[dc->revive_at-1]->revive_at);
        assert (!proof[dc->revive_at-1]->deleted);
        assert (!proof[dc->revive_at-1]->counterpart);
        assert (proof[dc->revive_at-1]->literals.size ());
      }
    } else {
      assert (!c || dc->literals.empty ());
      assert (c || dc->literals.size ());
    }
    if (!dc->deleted && c && c->garbage) {
      ///NOTE: See the discussion in 'propagate' on avoiding to eagerly trace binary
      // clauses as deleted (produce 'd ...' lines) as soon they are marked
      // garbage.
      assert (c->size == 2);
      assert (0 && "remove this if you are actually delaying the trace of garbage binaries");
    }
  }
#endif
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
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER derived clause notification");
  append_lemma (new DrupperClause (), c);
  STOP (drup_inprocess);
}

void Drupper::add_derived_unit_clause (const int lit, bool original) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG ({lit}, "DRUPPER derived clause notification");
  assert (lit);
  assert (!original || !internal->var(lit).reason);
  Clause * c = 0;
  if (!internal->var(lit).reason)
    internal->var(lit).reason = c = new_unit_clause (lit, original);
  if (!original) {
    c = !c ? new_unit_clause (lit, original) : c;
    append_lemma (new DrupperClause (), c);
  }
  assert (internal->var(lit).reason->literals[0] == lit);
  STOP (drup_inprocess);
}

void Drupper::add_derived_empty_clause () {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG ("DRUPPER derived empty clause notification");
  STOP (drup_inprocess);
}

void Drupper::add_failing_assumption (const vector<int> & c) {
  if (isolated) return;
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

void Drupper::add_updated_clause (Clause * c) {
  if (isolated) return;
  assert (!validating && c);
  START (drup_inprocess);
  LOG (c, "DRUPPER updated");
  unsigned revive_at = 0;
  if (c->drup_idx) {
    revive_at = c->drup_idx;
    assert (proof[revive_at - 1]->counterpart == c);
    reset_counterpart (proof[revive_at - 1]);
  }
  append_lemma (new DrupperClause (), c);
  append_lemma (new DrupperClause (c, true), 0);
  proof[proof.size ()-1]->revive_at = revive_at;
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

// Must be called at a point in which no literals are marked!
static vector<int> remove_duplicates (Internal * internal, const vector <int> & c) {
  vector<int> unique;
  for (int lit : c) {
    if (internal->marked (lit))
      continue;
    internal->mark (lit);
    unique.push_back (lit);
  }
  for (int lit : unique)
    internal->unmark (lit);
  return unique;
}

static void swap_falsified_literals_right (Internal * internal, vector <int> & c) {
  int sz = c.size ();
  for (int i = 0; i < sz; i++) {
    if (internal->val (c[i]) < 0) {
      int bl = c[--sz];
      c[sz] = c[i];
      c[i] = bl;
    }
  }
}

/*------------------------------------------------------------------------*/

void Drupper::delete_clause (const vector<int> & c, bool original) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  // remove duplicates. if there is only one unique literal,
  // skip it unless it's a falsified original then we cache it.
  vector<int> modified = remove_duplicates (internal, c);
  bool falsified_original = modified.size () == 1 && internal->val (c[0]) < 0;
  if (modified.size () == c.size () || modified.size () > 1 || falsified_original) {
    if (original) {
      ///NOTE: This is an original clause that has been reduced to an irredundant
      // dervied clause after removing all its falsified literals. This clause was
      // not allocated in memory. However, it needs to be revived for correct core
      // extraction and complete validation.
      // Moving the falsified literals to the end of the clause is crucial as we
      // need to watch the first two unassigned literals of this clause once it is
      // revived.
      swap_falsified_literals_right (internal, modified);
    }
    append_lemma (new DrupperClause (modified, true), 0);
  }
  STOP (drup_inprocess);
}

void Drupper::delete_clause (Clause * c) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  append_lemma (new DrupperClause (c, true), c);
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::update_moved_counterparts () {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  for (unsigned i = 0; i < proof.size(); i++) {
    bool deleted = proof[i]->deleted;
    Clause * c = proof[i]->counterpart;

    if (deleted || !c || !c->moved)
       continue;

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
    assert (c->drup_idx);
    assert (c->copy->drup_idx);
#endif

    c->copy->drup_idx = c->drup_idx;
    reset_counterpart (proof[i]);
    set_counterpart (proof[i], c->copy);
  }
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

bool Drupper::trim (bool overconstrained) {
  START (drup_trim);
  LOG ("DRUPPER trim");

  solves++;

  save_scope<bool> recover_unsat (internal->unsat);
  assert (!validating && !isolated && !setup_options ());
  check_environment ();

  // Mark the conflict and its reasons as core.
  const unsigned proof_sz = proof.size ();
  mark_conflict (overconstrained);

  clean_conflict ();
  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = internal->trail.size();
  lock_scope trim_scope (validating);

  collect (internal);

  // Main trimming loop
  for (int i = proof.size() - 1 - int (overconstrained); i >= 0; i--) {

    bool deleted = proof[i]->deleted;
    Clause * c = proof[i]->counterpart;

    assert (!deleted || !c);

    if (deleted) {
      revive_clause (i);
      continue;
    }

    if (is_on_trail (c)) {
      if (core_units) mark_core (c);
      undo_trail_core (c, trail_sz);
      internal->report ('m');
    }

    stagnate_clause (i);

    if (c->core) {
      shrink_internal_trail (trail_sz);
      assume_negation (c);
      bool validated = propagate_conflict ();
      assert (validated);
      conflict_analysis_core ();
      clean_conflict ();
    }
  }

  internal->report ('M');

  shrink_internal_trail (trail_sz);
  mark_core_trail_antecedents ();

  {
    // This is a good point to dump core as garbage
    // core clauses will be removed later.
    // ```
    dump_core ();
    // ```
    #ifndef NDEBUG
      // Ensure the set of all core clauses is unsatisfiable
      assert (core_is_unsat ());
    #endif
  }

  reconsruct (proof_sz);
  STOP (drup_trim);
  return true;
}

}
