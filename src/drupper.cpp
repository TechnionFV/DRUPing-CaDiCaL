#include "internal.hpp"
#include "unordered_set"

namespace CaDiCaL {


/*------------------------------------------------------------------------*/

// Enable proof drupping.

void Internal::drup () {
  assert (!drupper);
  drupper = new Drupper (this);
}

/*------------------------------------------------------------------------*/

DrupperClause::DrupperClause (Clause * c, bool deletion)
: deleted (deletion)
{
  counterpart = c;
};

Clause * DrupperClause::clause () {
  return counterpart;
}

/*------------------------------------------------------------------------*/

Drupper::Drupper (Internal * i, File * f)
:
  internal (i), failed_constraint (0),
  isolated (0), validating (0), file (f)
{
  LOG ("DRUPPER new");

  setup_internal_options ();

  // Initialize statistics.
  //
  memset (&stats, 0, sizeof (stats));

  if (internal->opts.drupdumpcore && !f)
    file = File::write (internal, stdout, "<stdout>");
}

Drupper::~Drupper () {
  LOG ("DRUPPER delete");
  isolated = true;
  ///TODO: Ensure all allocated resources are freed. Unprotect clauses?
  internal->delete_garbage_clauses ();
  for (const auto & dc : proof) {
    if (dc->deleted)
      delete [] (char *) dc->clause ();
    delete (DrupperClause *) dc;
  }
  for (const auto & c : unit_clauses)
    delete [] (char*) c;
  delete file;
}
/*------------------------------------------------------------------------*/

void Drupper::set (const char * setting, bool val) {
  if (!strcmp (setting, "core_units"))
    settings.core_units = val;
  else if (!strcmp (setting, "unmark_core"))
    settings.unmark_core = val;
  else if (!strcmp (setting, "core_first"))
    settings.core_first = val;
  else if (!strcmp (setting, "check_core"))
    settings.check_core = val;
  else if (!strcmp (setting, "extract_core_literals"))
    settings.extract_core_literals = val;
  else assert (0 && "unknown drupper seting");
}

bool Drupper::setup_internal_options () {
  auto & opts = internal->opts;
  bool updated = false;
  updated |= opts.chrono;
  updated |= opts.probe;
  updated |= opts.compact;
  updated |= opts.arena;
  updated |= opts.vivify;
  opts.chrono = 0;
  opts.probe = 0;
  opts.compact = 0;
  opts.arena = 0;
  ///FIXME: ../interesting/vivify/red-*
  opts.vivify = 0;
  return updated;
}

/*------------------------------------------------------------------------*/

Clause * Drupper::new_clause (Clause * lits) {

  assert (lits->size <= (size_t) INT_MAX);
  const int size = (int) lits->size;
  assert (size >= 2);

  // Determine whether this clauses should be kept all the time.
  //
  bool keep = true;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = keep;
  c->moved = false;
  c->reason = false;
  c->redundant = true;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->core = false;
  c->drup_idx = 0;
  c->dummy = true;
  c->used = 0;

  c->glue = 0;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++) c->literals[i] = lits->literals[i];

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->bytes () == bytes);

  return c;
}

Clause * Drupper::new_clause (const vector<int> & lits) {

  assert (lits.size () <= (size_t) INT_MAX);
  const int size = (int) lits.size ();
  assert (size >= 2);

  // Determine whether this clauses should be kept all the time.
  //
  bool keep = true;

  size_t bytes = Clause::bytes (size);
  Clause * c = (Clause *) new char[bytes];

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->keep = keep;
  c->moved = false;
  c->reason = false;
  c->redundant = true;
  c->transred = false;
  c->subsume = false;
  c->vivified = false;
  c->vivify = false;
  c->core = false;
  c->drup_idx = 0;
  c->dummy = true;
  c->used = 0;

  c->glue = 0;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++) c->literals[i] = lits[i];

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->bytes () == bytes);

  return c;
}

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
  c->dummy = true;
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

void Drupper::append_lemma (DrupperClause * dc) {
  assert (dc);
  if (dc->deleted)
    stats.deleted++;
  else {
    stats.derived++;
    Clause * cp = dc->clause ();
    assert (!cp->drup_idx);
    cp->drup_idx = proof.size () + 1;
  }
  proof.push_back (dc);
}

void Drupper::append_failed (const vector<int> & lits) {
  Clause * c = new_clause (lits);
  c->garbage = true;
  internal->watch_clause (c);
  mark_core (c);
  ///TODO: Should reactivate literals here?
  append_lemma (new DrupperClause (c));
  append_lemma (new DrupperClause (c, true));
}

void Drupper::revive_clause (int i) {
  START (drup_revive);
  assert (i >= 0 && i < proof.size ());
  DrupperClause * dc = proof[i];
  assert (dc->deleted);
  Clause * c = dc->clause ();
  assert (c && c->garbage);
  c->garbage = false;
  for (int j : *c)
    if (internal->flags (j).eliminated ())
      internal->reactivate (j);
  internal->watch_clause (c);
  STOP (drup_revive);
}

void Drupper::stagnate_clause (const int i) {
  Clause * c = proof[i]->clause ();
  {
    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.
    assert (!c->garbage && "remove this if you are actually delaying the trace of garbage binaries");
  }
  assert (!c->moved);
  c->garbage = true;
  if (c->size > 1)
    internal->unwatch_clause (c);
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

    if (settings.core_units)
      mark_core (r);

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
      assert (0);
      // Last deleted lemma is the falsified original.
      // Revive it and mark it as the conflict clause.
      int i = proof.size () - 1;
      assert (i >= 0 && proof[i]->deleted);
      DrupperClause * dc = proof[i];
      assert (dc->counterpart);
      if (dc->counterpart->size > 1)
        revive_clause (i);
      else
        dc->counterpart->garbage = false;
      conflict = proof[i]->clause ();
    } else {
      conflict = internal->conflict;
    }
    mark_core (conflict);
    for (int i = 0; i < conflict->size; i++)
      mark_conflict_lit (conflict->literals[i]);
  } else {
    if (internal->unsat_constraint && internal->constraint.size () > 1) {
      failed_constraint = new_clause (internal->constraint);
      mark_core (failed_constraint);
      internal->watch_clause (failed_constraint);
    }
    assert (!internal->marked_failed);
    internal->failing ();
    internal->marked_failed = true;
  }
}

void Drupper::mark_failing (const int proof_sz) {
  // assert (proof_sz < proof.size () && !((proof.size () - proof_sz) % 2));
  // for (int i = proof_sz; i < proof.size(); i++)
    // if ((i - proof_sz) % 2)
      // mark_core (proof[i]->clause ());
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
  if (internal->propagate (settings.core_first))
  {
    START (drup_repropagate);
    {
      // If propagate fails, it may be due to incrementality and
      // missing units. re-propagate the entire trail.
      ///TODO: Understand what exactly happens and why is this needed.
      // A good point to start: test/trace/reg0048.trace.
      assert (stats.solves);
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
  for (int l : *conflict)
    assert (internal->val (l)  < 0);
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
    assert (internal->val (lit) < 0);
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
  for (DrupperClause * dc : proof) {
    Clause * c = dc->clause ();
    if (c->core)
      c->core = false, stats.core--;
  }
  for (Clause * c : internal->clauses)
    if (c->core)
      c->core = false, stats.core--;
  for (Clause * c : unit_clauses)
    if (c->core)
      c->core = false, stats.core--;
  if (failed_constraint && failed_constraint->core)
    failed_constraint->core = false, stats.core--;
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
    delete [] (char *) failed_constraint;
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
    Clause * c = dc->clause ();
    if (!dc->deleted) {
      assert (c && c->garbage);
      c->garbage = false;
      if (c->size > 1)
        internal->watch_clause (c);
    }
  }

  for (int i = proof.size () - 1; i >= 0; i--) {
    DrupperClause * dc = proof[i];
    if (dc->deleted) {
      Clause * c = dc->clause ();
      assert (c && !c->garbage);
      c->garbage = true;
      // assert (!is_on_trail (c) || c->size == 1);
    }
  }

  internal->flush_all_occs_and_watches ();
}

void Drupper::reconstruct (const unsigned proof_sz) {
  lock_scope isolate (isolated);
  START (drup_reconstruct);
  save_core_phase_stats ();
  if (settings.unmark_core)
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
    assert (dc);
    Clause * c = dc->clause ();
    if (!c) continue;
    assert (c);
    assert (!dc->deleted || c->garbage);
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

void Drupper::dump_clause (Clause * c) {
  if (!c) printf ("0 \n");
  else {
    const int * lits = c->literals;
    for (int i = 0; i < c->size; i++)
      printf ("%d ", lits[i]);
    printf ("\n");
  }
}

void Drupper::dump_clause (DrupperClause * dc) {
  assert (dc);
  dump_clause (dc->clause ());
}

void Drupper::dump_clause (vector <int> & c) {
  for (int i : c)
    printf ("%d ", i);
  printf ("\n");
}

void Drupper::dump_proof () {
  printf ("DUMP PROOF START\n");
  for (int i = proof.size () - 1; i >= 0; i--) {
    auto & dc = proof[i];
    printf ("(%d) %s: ", i, dc->deleted ? "deleted" : "       ");
    Clause * c = proof[i]->clause ();
    printf ("C (%lu): ", c);
    if (!c) printf ("0 ");
    else {
      for (int l : *c) printf ("%d ", l);
      printf ("%s", c->garbage ? "(garbage)" : "");
    }
    printf ("\n");
  }
  printf ("DUMP PROOF END\n");
}

void Drupper::dump_trail () {
  printf ("DUMP TRAIL START\n");
  auto & trail = internal->trail;
  for (int i = trail.size () - 1; i >= 0; i--)
    printf ("(%d) %d <-- ", i, trail[i]), dump_clause (internal->var (trail[i]).reason);
  printf ("DUMP TRAIL END\n");
}

bool Drupper::core_is_unsat () {
  CaDiCaL::Solver s;
  s.set ("drup", 0);
  for (auto & dc : proof) {
    Clause * c = dc->clause ();
    if (c->core) {
      for (int * i = c->begin (); i != c->end (); i++)
        s.add (*i);
      s.add (0);
    }
  }
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
  if (internal->unsat_constraint) {
    if (internal->constraint.size () == 1) {
      for (int l : internal->constraint)
        s.add (l);
      s.add (0);
    } else {
      assert (failed_constraint);
      for (int l : *failed_constraint)
        s.add (l);
      s.add (0);
    }
  }
  return s.solve () == 20;
}

void Drupper::dump_core () const {
  if (!internal->opts.drupdumpcore || !file)
    return;
  file->put ("DUMP CORE START\n");
  for (auto & dc : proof) {
    Clause * c = dc->clause ();
    if (c->core) {
      for (int l : *c)
        file->put (l), file->put (' ');
      file->put ("0\n");
    }
  }
  for (Clause * c : internal->clauses)
    if (c->core) {
      for (int l : *c)
        file->put (l), file->put (' ');
      file->put ("0\n");
    }
  for (Clause * c : unit_clauses)
    if (c->core) {
      file->put (c->literals[0]), file->put (' ');
      file->put ("0\n");
    }
  for (int l : internal->assumptions)
    if (internal->failed (l)) {
      file->put (l), file->put (' ');
      file->put ("0\n");
    }
  if (internal->unsat_constraint) {
    if (internal->constraint.size () == 1) {
      for (int l : internal->constraint)
        file->put (l), file->put (' ');
      file->put ("0\n");
    } else {
      assert (failed_constraint);
      for (int l : *failed_constraint)
        file->put (l), file->put (' ');
      file->put ("0\n");
    }
  }
  file->put ("DUMP CORE START\n");
}

vector<int> Drupper::extract_core_literals () const {
  vector<int> core_lits;
  for (Clause * c : internal->clauses)
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  for (DrupperClause * dc : proof) {
    Clause * c = dc->clause ();
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  }
  for (Clause * c : unit_clauses)
    if (c->core)
      for (int l : *c)
        if (!internal->flags (l).mark_core (true))
          core_lits.push_back (l);
  for (int l : internal->assumptions)
    if (!internal->flags (l).mark_core (true))
      core_lits.push_back (l);
  if (internal->unsat_constraint && internal->constraint.size () == 1) {
    int l = internal->constraint[0];
    if (!internal->flags (l).mark_core (true))
      core_lits.push_back (l);
  }
  // Otherwise should be part if internal->clauses
  return core_lits;
}

/*------------------------------------------------------------------------*/

void Drupper::add_derived_clause (Clause * c) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER derived clause notification");
  append_lemma (new DrupperClause (c));
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
    append_lemma (new DrupperClause (c));
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
  Clause * mc = new_clause (c);
  mc->garbage = true;
  if (c->drup_idx) {
    mc->drup_idx = c->drup_idx;
    assert (proof[c->drup_idx - 1]->clause () == c);
    proof[c->drup_idx - 1]->counterpart = mc;
    c->drup_idx = 0;
  }
  append_lemma (new DrupperClause (c));
  append_lemma (new DrupperClause (mc, true));
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
    Clause * mc = new_clause (modified);
    append_lemma (new DrupperClause (mc, true));
  }
  STOP (drup_inprocess);
}

void Drupper::delete_clause (Clause * c) {
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  LOG (c, "DRUPPER clause deletion notification");
  append_lemma (new DrupperClause (c, true));
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

void Drupper::update_moved_counterparts () {
  assert (0 && "shouldn't be triggered if arenaing is of");
  if (isolated) return;
  assert (!validating);
  START (drup_inprocess);
  for (unsigned i = 0; i < proof.size(); i++) {
    auto & dc = proof[i];

    Clause * c = dc->clause ();
    if (!c->moved)
      continue;

#ifndef NDEBUG
    assert (c->copy && c != c->copy);
    assert (c->copy->drup_idx == c->drup_idx);
#endif

    dc->counterpart = c->copy;
  }
  STOP (drup_inprocess);
}

/*------------------------------------------------------------------------*/

optional<vector<int>> Drupper::trim (bool overconstrained) {
  START (drup_trim);
  LOG ("DRUPPER trim");

  stats.solves++;

  save_scope<bool> recover_unsat (internal->unsat);
  assert (!validating && !isolated && !setup_internal_options ());
  check_environment ();

  // Mark the conflict and its reasons as core.
  const unsigned proof_sz = proof.size ();
  mark_conflict (overconstrained);

  clean_conflict ();
  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = internal->trail.size();
  lock_scope trim_scope (validating);

  // collect (internal);
  internal->flush_all_occs_and_watches ();

  // dump_proof ();

  // Main trimming loop
  for (int i = proof.size() - 1 - int (overconstrained); i >= 0; i--) {

    auto & dc = proof[i];

    if (dc->deleted) {
      revive_clause (i);
      continue;
    }

    if (proof_sz == i)
      mark_failing (proof_sz);

    Clause * c = proof[i]->clause ();

    if (is_on_trail (c)) {
      if (settings.core_units)
        mark_core (c);
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
      if (settings.check_core)
        assert (core_is_unsat ());
    #endif
  }

  optional<vector<int>> res = {};

  if (settings.extract_core_literals)
    res = extract_core_literals ();

  reconstruct (proof_sz);

  STOP (drup_trim);
  return res;
}

void Drupper::sort_watches (const int lit) {
  auto & ws = internal->watches (lit);
  int l = 0, h = ws.size () - 1;
  while (l < h) {
    auto w = ws[h];
    if (!w.clause->core) {
      h--;
      continue;
    }
    auto tw = ws[l];
    ws[l++] = ws[h];
    ws[h] = tw;
  }
}

}
